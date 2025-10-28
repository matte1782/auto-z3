# scripts/export_geojson_americas.py
# Genera:
#   data/geo/south_america_countries.geojson
#   data/geo/central_america_countries.geojson
#
# Dipendenze: geopandas, shapely, requests, fiona, pyproj
#   pip install geopandas shapely fiona pyproj requests

import io
import json
import zipfile
import pathlib as pl
import requests
import geopandas as gpd

RAW_DIR = pl.Path("data/raw"); RAW_DIR.mkdir(parents=True, exist_ok=True)
OUT_DIR = pl.Path("data/geo"); OUT_DIR.mkdir(parents=True, exist_ok=True)

NE50_URL = "https://naturalearth.s3.amazonaws.com/50m_cultural/ne_50m_admin_0_countries.zip"
ZIP_PATH = RAW_DIR / "ne_50m_admin_0_countries.zip"
SHP_NAME = "ne_50m_admin_0_countries.shp"

def _download_once():
    if ZIP_PATH.exists():
        return
    print(f"⤵️ scarico Natural Earth 50m…\n{NE50_URL}")
    r = requests.get(NE50_URL, timeout=60)
    r.raise_for_status()
    ZIP_PATH.write_bytes(r.content)
    print(f"✓ salvato {ZIP_PATH}")

def _load_world_gdf() -> gpd.GeoDataFrame:
    """Legge lo shapefile NE50 localmente (se non c’è lo scarica)."""
    _download_once()
    shp_url = f"zip://{ZIP_PATH.as_posix()}!{SHP_NAME}"
    gdf = gpd.read_file(shp_url)[["NAME", "ADM0_A3", "CONTINENT", "geometry"]]
    gdf = gdf.rename(columns={"ADM0_A3": "ISO_A3"})
    # allinea CRS
    if gdf.crs is None:
        gdf.set_crs("EPSG:4326", inplace=True)
    else:
        gdf = gdf.to_crs(epsg=4326)
    # pulizie
    gdf["ISO_A3"] = gdf["ISO_A3"].replace({"-99": None})
    return gdf

def _dump_geojson(gdf: gpd.GeoDataFrame, out_path: pl.Path, simplify_tol=0.04):
    gdf = gdf.copy()
    gdf["geometry"] = gdf["geometry"].simplify(simplify_tol, preserve_topology=True)
    gdf["REG_ID"] = gdf["ISO_A3"]
    gdf = gdf[["ISO_A3", "NAME", "REG_ID", "geometry"]]
    gdf.to_file(out_path, driver="GeoJSON")
    print(f"✓ scritto {out_path} ({len(gdf)} features)")

def main():
    world = _load_world_gdf()

    # --- Sud America (include GUF = French Guiana)
    sa_iso3 = ["ARG","BOL","BRA","CHL","COL","ECU","GUY","PRY","PER","SUR","URY","VEN","GUF"]
    sa = world[world["ISO_A3"].isin(sa_iso3)]
    _dump_geojson(sa, OUT_DIR / "south_america_countries.geojson", simplify_tol=0.03)

    # --- America Centrale (solo paesi Belize..Panama)
    ca_iso3 = ["BLZ","GTM","SLV","HND","NIC","CRI","PAN"]
    ca = world[world["ISO_A3"].isin(ca_iso3)]
    _dump_geojson(ca, OUT_DIR / "central_america_countries.geojson", simplify_tol=0.03)

if __name__ == "__main__":
    main()
