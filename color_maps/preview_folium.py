# color_maps/preview_folium.py
import json
import folium
from streamlit_folium import st_folium

def render_folium_preview(geojson_path: str):
    with open(geojson_path, "r", encoding="utf-8") as f:
        gj = json.load(f)

    def style_fn(feature):
        return dict(
            fillColor="#EEF2F7",
            color="#1F2937",
            weight=1.0, fillOpacity=0.7
        )

    m = folium.Map(tiles="cartodbpositron", prefer_canvas=True, zoom_control=True)
    layer = folium.GeoJson(
        gj,
        style_function=style_fn,
        tooltip=folium.GeoJsonTooltip(fields=["NAME", "ISO_A3"])
    )
    layer.add_to(m)
    try:
        m.fit_bounds(layer.get_bounds())
    except Exception:
        pass
    st_folium(m, height=560, width=None)
