# scripts/make_geojson_americas.py
# Genera:
#  - data/geo/south_america_countries.geojson
#  - data/geo/central_america_countries.geojson
#  - data/adj/south_america_neighbors.json
#  - data/adj/central_america_neighbors.json
#
# Uso:
#   python scripts/make_geojson_americas.py --out data/geo --adj data/adj --simplify 0.05
#
# Requisiti:
#   pip install geopandas shapely requests

import os
import io
import json
import zipfile
import argparse
import tempfile
from typing import Dict, List, Set

import requests
import geopandas as gpd
from shapely.prepared import prep

# Mirror affidabili di Natural Earth 1:50m
NE_URLS = [
    "https://naciscdn.org/naturalearth/50m/cultural/ne_50m_admin_0_countries.zip",
    "https://naturalearth.s3.amazonaws.com/50m_cultural/ne_50m_admin_0_countries.zip",
]

# ISO-A3 usati nei dataset (inclusi territori rilevanti ai confini)
SOUTH_AMERICA = [
    "ARG", "BOL", "BRA", "CHL", "COL", "ECU", "GUY", "PRY", "PER",
    "SUR", "URY", "VEN", "GUF",  # French Guiana
    "FLK"  # Falkland Islands (per completezza, non influenza la K4)
]
CENTRAL_AMERICA = ["MEX", "BLZ", "GTM", "SLV", "HND", "NIC", "CRI", "PAN"]


# ──────────────────────────────────────────────────────────────────────────────
# Download & Load
# ──────────────────────────────────────────────────────────────────────────────

def download_ne_admin0() -> bytes:
    last_err = None
    for url in NE_URLS:
        try:
            r = requests.get(url, timeout=60)
            r.raise_for_status()
            return r.content
        except Exception as ex:
            last_err = ex
    raise RuntimeError(f"Impossibile scaricare Natural Earth. Ultimo errore: {last_err}")

def load_gdf_from_zip(zip_bytes: bytes) -> gpd.GeoDataFrame:
    with tempfile.TemporaryDirectory() as td:
        zf = zipfile.ZipFile(io.BytesIO(zip_bytes))
        zf.extractall(td)
        shp = [
            os.path.join(td, f)
            for f in os.listdir(td)
            if f.endswith(".shp") and "admin_0_countries" in f
        ][0]
        gdf = gpd.read_file(shp)
    return gdf


# ──────────────────────────────────────────────────────────────────────────────
# Normalizzazione campi e filtri
# ──────────────────────────────────────────────────────────────────────────────

def normalize_fields(gdf: gpd.GeoDataFrame) -> gpd.GeoDataFrame:
    # ISO_A3
    if "ADM0_A3" in gdf.columns:
        gdf["ISO_A3"] = gdf["ADM0_A3"]
    elif "ISO_A3_EH" in gdf.columns:
        gdf["ISO_A3"] = gdf["ISO_A3_EH"]
    elif "ISO_A3" in gdf.columns:
        gdf["ISO_A3"] = gdf["ISO_A3"]
    else:
        raise ValueError("Campo ISO a3 non trovato (ADM0_A3 / ISO_A3_EH / ISO_A3 assenti).")

    # NAME
    if "NAME_EN" in gdf.columns:
        gdf["NAME"] = gdf["NAME_EN"]
    elif "NAME" in gdf.columns:
        gdf["NAME"] = gdf["NAME"]
    else:
        gdf["NAME"] = gdf["ISO_A3"]

    gdf = gdf[["ISO_A3", "NAME", "geometry"]].copy()
    # CRS coerente
    if gdf.crs is None:
        gdf.set_crs(4326, inplace=True)
    else:
        gdf = gdf.to_crs(4326)
    # ripara eventuali geometrie
    gdf["geometry"] = gdf["geometry"].buffer(0)
    # separa multipoligoni in righe distinte
    gdf = gdf.explode(index_parts=False, ignore_index=True)
    return gdf

def filter_by_isos(gdf: gpd.GeoDataFrame, isos: List[str]) -> gpd.GeoDataFrame:
    g = gdf[gdf["ISO_A3"].isin(isos)].copy()
    g["geometry"] = g["geometry"].buffer(0)
    g = g.dissolve(by="ISO_A3", as_index=False)  # merge parti di uno stesso paese
    g = g.reset_index(drop=True)
    return g


# ──────────────────────────────────────────────────────────────────────────────
# Adiacenze su geometrie RAW + semplificazione per export
# ──────────────────────────────────────────────────────────────────────────────

def build_neighbors_raw(gdf_raw: gpd.GeoDataFrame) -> Dict[str, List[str]]:
    """
    Calcola il grafo di adiacenza su geometrie NON semplificate.
    Usa touches() (contatto linea o punto). Restituisce liste ordinate.
    """
    gdf = gdf_raw.reset_index(drop=True)
    keys = list(gdf["ISO_A3"])
    geoms = {row.ISO_A3: row.geometry for _, row in gdf.iterrows()}
    prepped = {k: prep(geoms[k]) for k in keys}

    neighbors: Dict[str, Set[str]] = {k: set() for k in keys}
    for i, a in enumerate(keys):
        pa = prepped[a]
        for b in keys[i+1:]:
            gb = geoms[b]
            if pa.touches(gb):
                neighbors[a].add(b)
                neighbors[b].add(a)

    return {k: sorted(list(v)) for k, v in neighbors.items()}

def simplify_for_export(gdf_raw: gpd.GeoDataFrame, simplify_tol: float) -> gpd.GeoDataFrame:
    """
    Semplifica SOLO per esportazione visuale. La topologia dell'adiacenza
    è già stata fissata sulle geometrie raw.
    """
    g = gdf_raw.copy()
    if simplify_tol > 0:
        g["geometry"] = g["geometry"].simplify(simplify_tol, preserve_topology=True)
        g["geometry"] = g["geometry"].buffer(0)
    return g


# ──────────────────────────────────────────────────────────────────────────────
# Utility I/O
# ──────────────────────────────────────────────────────────────────────────────

def ensure_dirs(out_geo: str, out_adj: str):
    os.makedirs(out_geo, exist_ok=True)
    os.makedirs(out_adj, exist_ok=True)

def write_geojson(gdf: gpd.GeoDataFrame, path: str):
    gdf.to_file(path, driver="GeoJSON")

def write_adj(adj: Dict[str, List[str]], path: str):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(adj, f, ensure_ascii=False, indent=2)


# ──────────────────────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="data/geo", help="cartella GeoJSON in uscita")
    ap.add_argument("--adj", default="data/adj", help="cartella adiacenze in uscita")
    ap.add_argument("--simplify", type=float, default=0.05, help="tolleranza semplificazione (gradi)")
    args = ap.parse_args()

    ensure_dirs(args.out, args.adj)

    print("Scarico Natural Earth…")
    z = download_ne_admin0()

    print("Carico shapefile…")
    world = load_gdf_from_zip(z)
    world = normalize_fields(world)

    # Filtri RAW (niente simplify per costruire il grafo di adiacenza)
    sa_raw = filter_by_isos(world, SOUTH_AMERICA)
    ca_raw = filter_by_isos(world, CENTRAL_AMERICA)

    # Adiacenze su RAW
    print("Calcolo adiacenze (RAW)…")
    sa_adj = build_neighbors_raw(sa_raw)
    ca_adj = build_neighbors_raw(ca_raw)

    # Sanity check: K4 in Sud America (ARG, BOL, BRA, PRY)
    must_edges = {("ARG", "BOL"), ("BOL", "BRA"), ("BRA", "PRY"), ("PRY", "ARG")}
    missing = [e for e in must_edges if (e[1] not in sa_adj.get(e[0], [])) or (e[0] not in sa_adj.get(e[1], []))]
    if missing:
        raise RuntimeError(
            "Adjacency too sparse: missing K4 edges "
            f"{missing}. Calcolo adiacenza deve avvenire su RAW. Verifica i dati."
        )

    # Semplificazione SOLO per export
    print("Semplifico geometrie per export…")
    sa_vis = simplify_for_export(sa_raw, args.simplify)
    ca_vis = simplify_for_export(ca_raw, args.simplify)

    # Percorsi output
    sa_gj = os.path.join(args.out, "south_america_countries.geojson")
    ca_gj = os.path.join(args.out, "central_america_countries.geojson")
    sa_adj_path = os.path.join(args.adj, "south_america_neighbors.json")
    ca_adj_path = os.path.join(args.adj, "central_america_neighbors.json")

    # Scritture
    print(f"Scrivo {sa_gj}")
    write_geojson(sa_vis, sa_gj)
    print(f"Scrivo {ca_gj}")
    write_geojson(ca_vis, ca_gj)

    print(f"Scrivo {sa_adj_path}")
    write_adj(sa_adj, sa_adj_path)
    print(f"Scrivo {ca_adj_path}")
    write_adj(ca_adj, ca_adj_path)

    print("Fatto.")
    print("File generati:")
    print(" -", sa_gj)
    print(" -", ca_gj)
    print(" -", sa_adj_path)
    print(" -", ca_adj_path)


if __name__ == "__main__":
    main()
