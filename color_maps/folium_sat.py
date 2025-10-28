# color_maps/folium_sat.py
# Renders a Folium map from a GeoJSON file + a color assignment (ISO_A3 -> color index).
# UI labels are intentionally minimal here; bilingual text is handled in the Streamlit UI.
from __future__ import annotations

from typing import Dict, Any
import folium
from streamlit_folium import st_folium

from .color_apply import inject_colors


def render_sat_map(geojson_path: str, assignment: Dict[str, int], height: int = 640) -> Dict[str, Any] | None:
    """
    Render a Folium map in Streamlit using a given color assignment.

    Parameters
    ----------
    geojson_path : str
        Path to the base GeoJSON (features must have properties.ISO_A3).
    assignment : Dict[str, int]
        Mapping ISO_A3 -> color index, as produced by the SAT model.
    height : int
        Height of the embedded map in pixels (default: 640).

    Returns
    -------
    Dict[str, Any] | None
        The object returned by st_folium (can contain map bounds, last click, etc.),
        or None if rendering failed.
    """
    # Build a colored GeoJSON (adds FILL / STROKE per feature)
    gj = inject_colors(geojson_path, assignment)

    def style_fn(feature: Dict[str, Any]) -> Dict[str, Any]:
        props = feature.get("properties", {})
        return dict(
            fillColor=props.get("FILL", "#E6E9EF"),
            color=props.get("STROKE", "#1F2937"),
            weight=1.0,
            fillOpacity=0.9,
        )

    # Folium map (carto basemap is light and performant)
    m = folium.Map(tiles="cartodbpositron", prefer_canvas=True, zoom_control=True)

    # Tooltip shows the NAME and ISO_A3 fields from the GeoJSON
    layer = folium.GeoJson(
        gj,
        style_function=style_fn,
        tooltip=folium.GeoJsonTooltip(fields=["NAME", "ISO_A3"]),
    )
    layer.add_to(m)

    # Best effort to fit bounds
    try:
        m.fit_bounds(layer.get_bounds())
    except Exception:
        # Some degenerate GeoJSONs may fail get_bounds; ignore safely.
        pass

    try:
        return st_folium(m, height=height, width=None)
    except Exception:
        # Streamlit/Folium can raise in headless environments; do not propagate.
        return None
