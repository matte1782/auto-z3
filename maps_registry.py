# maps_registry.py
import json
import os
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple

Geo = Dict  # alias per GeoJSON dict


@dataclass
class MapSpec:
    id: str
    label: str
    # Dove leggere la geometria: funzione o file
    geo_loader: Callable[[], Geo]
    # Chiave campo per l'ID regione nel GeoJSON
    feature_id_key: str
    # Adiacenza: se None, tentiamo il calcolo (se GeoPandas disponibile)
    adjacency: Optional[List[Tuple[str, str]]] = None
    # Alias/etichette amichevoli
    display_name: Optional[Dict[str, str]] = None
    # Colonna da usare per il match tra GeoJSON e DataFrame
    property_key: Optional[str] = None


DATA_DIR = "data/maps"


def _load_geojson(path_rel: str) -> Geo:
    path = os.path.join(DATA_DIR, path_rel)
    with open(path, encoding="utf-8") as f:
        return json.load(f)


# ---------- Italia Regioni (statico + adjacency pronta) ----------
def _geo_italy_regions() -> Geo:
    # Metti il file semplificato in data/maps/italy_regions.geojson
    return _load_geojson("italy_regions.geojson")


ITALY_REGIONS = [
    "VDA",
    "PIE",
    "LOM",
    "LIG",
    "TAA",
    "VEN",
    "FVG",
    "EMR",
    "TOS",
    "UMB",
    "MAR",
    "LAZ",
    "ABR",
    "MOL",
    "CAM",
    "PUG",
    "BAS",
    "CAL",
    "SIC",
    "SAR",
]
ITALY_LABELS = {
    "VDA": "Valle d’Aosta",
    "PIE": "Piemonte",
    "LOM": "Lombardia",
    "LIG": "Liguria",
    "TAA": "Trentino-Alto Adige",
    "VEN": "Veneto",
    "FVG": "Friuli-Venezia Giulia",
    "EMR": "Emilia-Romagna",
    "TOS": "Toscana",
    "UMB": "Umbria",
    "MAR": "Marche",
    "LAZ": "Lazio",
    "ABR": "Abruzzo",
    "MOL": "Molise",
    "CAM": "Campania",
    "PUG": "Puglia",
    "BAS": "Basilicata",
    "CAL": "Calabria",
    "SIC": "Sicilia",
    "SAR": "Sardegna",
}
# Adiacenze curate a mano (29E24)
ITA_EDGES = [
    ("VDA", "PIE"),
    ("VDA", "LOM"),
    ("PIE", "VDA"),
    ("PIE", "LOM"),
    ("PIE", "LIG"),
    ("PIE", "TAA"),
    ("LOM", "VDA"),
    ("LOM", "PIE"),
    ("LOM", "LIG"),
    ("LOM", "TAA"),
    ("LOM", "VEN"),
    ("LOM", "EMR"),
    ("LIG", "PIE"),
    ("LIG", "LOM"),
    ("LIG", "EMR"),
    ("TAA", "PIE"),
    ("TAA", "LOM"),
    ("TAA", "VEN"),
    ("VEN", "LOM"),
    ("VEN", "TAA"),
    ("VEN", "FVG"),
    ("VEN", "EMR"),
    ("FVG", "VEN"),
    ("FVG", "EMR"),  # FVG–EMR solo via mare? se vuoi rimuovi
    ("EMR", "LIG"),
    ("EMR", "LOM"),
    ("EMR", "VEN"),
    ("EMR", "TOS"),
    ("EMR", "MAR"),
    ("TOS", "EMR"),
    ("TOS", "LIG"),
    ("TOS", "UMB"),
    ("TOS", "MAR"),
    ("TOS", "LAZ"),
    ("UMB", "TOS"),
    ("UMB", "MAR"),
    ("UMB", "LAZ"),
    ("MAR", "EMR"),
    ("MAR", "TOS"),
    ("MAR", "UMB"),
    ("MAR", "LAZ"),
    ("MAR", "ABR"),
    ("LAZ", "TOS"),
    ("LAZ", "UMB"),
    ("LAZ", "MAR"),
    ("LAZ", "ABR"),
    ("LAZ", "MOL"),
    ("LAZ", "CAM"),
    ("ABR", "MAR"),
    ("ABR", "LAZ"),
    ("ABR", "MOL"),
    ("MOL", "ABR"),
    ("MOL", "LAZ"),
    ("MOL", "CAM"),
    ("MOL", "PUG"),
    ("CAM", "LAZ"),
    ("CAM", "MOL"),
    ("CAM", "PUG"),
    ("CAM", "BAS"),
    ("PUG", "MOL"),
    ("PUG", "CAM"),
    ("PUG", "BAS"),
    ("BAS", "PUG"),
    ("BAS", "CAM"),
    ("BAS", "CAL"),
    ("CAL", "BAS"),
    # isole separate
]


# ---------- Francia regioni (metti geojson; adjacency auto o hand) ----------
def _geo_france_regions() -> Geo:
    return _load_geojson("france_regions.geojson")


# ---------- Europa paesi (EU o intera Europa) ----------
def _geo_europe_countries() -> Geo:
    # Inserisci un geojson (NaturalEarth 1:50m / geoBoundaries) in data/maps/europe_countries.geojson
    return _load_geojson("europe_countries.geojson")


def compute_adjacency_from_geo(geo: Geo, id_prop: str) -> List[Tuple[str, str]]:
    """
    Calcolo robusto con GeoPandas/Shapely (se disponibili).
    """
    try:
        import geopandas as gpd  # type: ignore
        from shapely.geometry import shape
    except Exception:
        return []

    feats = geo["features"]
    recs = []
    for f in feats:
        recs.append({"id": f["properties"][id_prop], "geom": shape(f["geometry"])})
    gdf = gpd.GeoDataFrame(recs, geometry="geom", crs="EPSG:4326").reset_index(drop=True)
    gdf["geom"] = gdf["geom"].buffer(0)  # fix topologie
    edges: List[Tuple[str, str]] = []
    # spatial join touches/intersects
    sjoined = gpd.sjoin(gdf, gdf, predicate="touches", how="left", lsuffix="a", rsuffix="b")
    for _, row in sjoined.iterrows():
        a = row["id_a"]
        b = row.get("id_b")
        if a and b and a != b:
            pair = (str(a), str(b))
            rev = (str(b), str(a))
            if pair not in edges and rev not in edges:
                edges.append(pair)
    return edges


REGISTRY: Dict[str, MapSpec] = {
    "ITA_REG": MapSpec(
        id="ITA_REG",
        label="Italia — Regioni (20)",
        geo_loader=_geo_italy_regions,
        feature_id_key="REG_ID",  # nel tuo geojson usa REG_ID con codici VDA/PIE/...
        property_key="REG_ID",
        adjacency=ITA_EDGES,
        display_name=ITALY_LABELS,
    ),
    "FRA_REG": MapSpec(
        id="FRA_REG",
        label="Francia — Regioni (n)",
        geo_loader=_geo_france_regions,
        feature_id_key="REG_ID",
        property_key="REG_ID",
        adjacency=None,  # prova calcolo auto (se geopandas)
        display_name=None,
    ),
    "EUR_CTY": MapSpec(
        id="EUR_CTY",
        label="Europa — Paesi",
        geo_loader=_geo_europe_countries,
        feature_id_key="ISO_A3",  # tipico nei dataset NaturalEarth
        property_key="ISO_A3",
        adjacency=None,  # calcolo auto se GeoPandas
        display_name=None,
    ),
}
