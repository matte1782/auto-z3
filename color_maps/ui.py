# color_maps/ui.py — bilingual-safe (EN/IT), no-regression
import json
import os
import re
from typing import Dict, List, Tuple

import streamlit as st

from i18n import t  # UI strings only; logic/data remain language-agnostic
from z3_runner import run_z3_safely

from .folium_sat import render_sat_map
from .preview_folium import render_folium_preview
from .solver import build_map_smt

BASE_GEO = os.path.join("data", "geo")
BASE_ADJ = os.path.join("data", "adj")

# Stable internal IDs → files; labels are translated at runtime
MAPS: Dict[str, Dict[str, str]] = {
    "south_america": {
        "label_key": "SOUTH_AMERICA_COUNTRIES",
        "geo": os.path.join(BASE_GEO, "south_america_countries.geojson"),
        "adj": os.path.join(BASE_ADJ, "south_america_neighbors.json"),
    },
    "central_america": {
        "label_key": "CENTRAL_AMERICA_COUNTRIES",
        "geo": os.path.join(BASE_GEO, "central_america_countries.geojson"),
        "adj": os.path.join(BASE_ADJ, "central_america_neighbors.json"),
    },
}

# Extract (ISO, color_index) from Z3 model def-funs
MODEL_VAR_RE = re.compile(r"\(define-fun\s+([A-Z]{3})_(\d+)\s+\(\)\s+Bool\s+(true|false)\)", re.I)


def _parse_assignment(model_text: str) -> Dict[str, int]:
    chosen: Dict[str, int] = {}
    for m in MODEL_VAR_RE.finditer(model_text or ""):
        iso, idx, val = m.group(1), int(m.group(2)), m.group(3).lower()
        if val == "true":
            chosen[iso] = idx
    return chosen


def _load_adjacency_pairs(adj_path: str) -> List[Tuple[str, str]]:
    with open(adj_path, encoding="utf-8") as f:
        adj = json.load(f)  # dict ISO -> [neighbors...]
    edges = set()
    for u, nbrs in adj.items():
        for v in nbrs:
            if not v or u == v:
                continue
            a, b = sorted((u, v))
            edges.add((a, b))
    return sorted(edges)


def _init_state():
    if "cmaps" not in st.session_state:
        st.session_state.cmaps = dict(
            map_id=None,
            n_colors=None,
            geo=None,
            adj=None,
            smt=None,
            status=None,
            model=None,
            assignment=None,
        )


def _patch_sa_k4(edges: List[Tuple[str, str]]) -> List[Tuple[str, str]]:
    """Ensure the classic K4 {ARG,BRA,PRY,BOL} is present (teaching exercise)."""
    must = {
        tuple(sorted(p))
        for p in [
            ("ARG", "BRA"),
            ("ARG", "PRY"),
            ("ARG", "BOL"),
            ("BRA", "PRY"),
            ("BRA", "BOL"),
            ("PRY", "BOL"),
        ]
    }
    es = set(edges)
    es |= must
    return sorted(es)


def _labels_for_select() -> Dict[str, str]:
    """Return map_id -> localized label using i18n keys."""
    return {mid: t(cfg["label_key"]) for mid, cfg in MAPS.items()}


def render_color_maps_page():
    _init_state()

    st.header(t("TAB_COLOR_MAPS_NEW"))
    colL, colR = st.columns([0.9, 1.1], gap="large")

    # Build localized options while keeping a stable internal key
    labels = _labels_for_select()
    ids_in_order = list(MAPS.keys())
    display_order = [labels[mid] for mid in ids_in_order]
    label_to_id = {labels[mid]: mid for mid in ids_in_order}

    with colL:
        map_label = st.selectbox(t("SELECT_MAP"), display_order)
        map_id = label_to_id[map_label]
        n_colors = st.slider(t("NUM_COLORS"), min_value=2, max_value=8, value=3)

        with st.form("solve_map_form", clear_on_submit=False):
            submitted = st.form_submit_button(t("BUTTON_SOLVE"), use_container_width=True)

        if submitted:
            geo = MAPS[map_id]["geo"]
            adj = MAPS[map_id]["adj"]

            # Load nodes (stable order)
            with open(geo, encoding="utf-8") as f:
                gj = json.load(f)
            nodes = [ft["properties"]["ISO_A3"] for ft in gj["features"]]

            # Load edges
            edges = _load_adjacency_pairs(adj)

            # South America teaching patch (K4 makes 3-color UNSAT)
            if map_id == "south_america":
                edges = _patch_sa_k4(edges)

            smt = build_map_smt(nodes, edges, n_colors)

            with st.spinner("Z3 solving…"):
                status, model, raw = run_z3_safely(smt, request_model=True)

            assignment = _parse_assignment(model) if status == "sat" else {}

            # Persist across reruns
            st.session_state.cmaps.update(
                map_id=map_id,
                n_colors=n_colors,
                geo=geo,
                adj=adj,
                smt=smt,
                status=status,
                model=model,
                assignment=assignment,
            )

    # ── Persistent output
    saved = st.session_state.cmaps
    st.markdown("### " + t("PREVIEW_RESULT"))

    if saved["status"] is None:
        st.info(t("INFO_CLICK_SOLVE"))
    else:
        badge = {
            "sat": t("SAT"),
            "unsat": t("UNSAT"),
            "unknown": t("UNKNOWN"),
            "error": "⚠️ " + t("ERROR"),
        }
        st.markdown(f"**{t('STATUS')}:** {badge.get(saved['status'], saved['status'])}")

        # SMT-LIB and download
        if saved["smt"]:
            st.markdown("**" + t("SMT2_GENERATED") + "**")
            st.code(saved["smt"], language="lisp")
            st.download_button(
                t("BTN_DOWNLOAD_SMT2"),
                data=saved["smt"],
                file_name=f"{(labels.get(saved['map_id'], 'map')).replace(' ', '_').lower()}_{saved['n_colors']}c.smt2",
                mime="text/plain",
                use_container_width=True,
            )

        # Model + assignment if SAT
        if saved["status"] == "sat":
            if saved["model"]:
                st.markdown("**" + t("MODEL_EXTRACT") + "**")
                st.code(saved["model"], language="lisp")
            if saved["assignment"]:
                txt = "\n".join(f"{k} → {v}" for k, v in sorted(saved["assignment"].items()))
                st.markdown("**ISO_A3 → " + t("NUM_COLORS").split()[0] + "**")
                st.code(txt, language="text")

            if saved["geo"] and saved["assignment"]:
                render_sat_map(saved["geo"], saved["assignment"])

    with colR:
        st.subheader(t("FOLIUM_PREVIEW"))
        try:
            render_folium_preview(MAPS[map_id]["geo"])
        except Exception as ex:
            st.error(f"{t('PREVIEW_ERROR')}: {ex}")
