# color_maps/color_apply.py
# Utilities to inject colors into a GeoJSON based on a SAT assignment.
from __future__ import annotations

import json
from typing import Dict, List


APPLE_PALETTE: List[str] = [
    "#F94144", "#F8961E", "#F9C74F", "#90BE6D",
    "#43AA8B", "#577590", "#277DA1", "#9B5DE5",
]


def inject_colors(
    geojson_path: str,
    assignment: Dict[str, int],
    palette: List[str] = APPLE_PALETTE,
) -> Dict:
    """
    Return a GeoJSON (as a Python dict) with color info injected in properties.

    Parameters
    ----------
    geojson_path : str
        Path to the base GeoJSON file (must contain FeatureCollection with
        features having 'properties.ISO_A3' and 'properties.NAME').
    assignment : Dict[str, int]
        Mapping ISO_A3 -> color index (0..K-1) coming from SAT model.
    palette : List[str]
        List of hex colors; indices wrap via modulo to avoid IndexError.

    Returns
    -------
    Dict
        A GeoJSON dict with each feature.properties augmented with:
          - "FILL": hex color for the region
          - "STROKE": hex color for borders (constant dark gray)
    """
    with open(geojson_path, "r", encoding="utf-8") as f:
        gj = json.load(f)

    features = gj.get("features", [])
    for ft in features:
        props = ft.get("properties") or {}
        iso = props.get("ISO_A3")
        idx = assignment.get(iso)

        if idx is None:
            fill = "#E6E9EF"  # neutral grey when unassigned
        else:
            try:
                fill = palette[idx % len(palette)]
            except Exception:
                # Fallback in case palette is empty or idx invalid
                fill = "#E6E9EF"

        props["FILL"] = fill
        props["STROKE"] = "#1F2937"  # dark grey outline
        ft["properties"] = props  # ensure the dict is attached back

    return gj
