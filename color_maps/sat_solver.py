from __future__ import annotations

import re
from typing import Dict, List, Tuple

from z3_runner import run_z3_safely


def exactly_one(*vars_for_region: List[str]) -> str:
    joined = " ".join(vars_for_region)
    return f"(and (or {joined}) ((_ at-most 1) {joined}))"


def build_smt(graph: Dict, n_colors: int) -> str:
    regions: List[str] = graph["regions"]
    edges: List[Tuple[str, str]] = graph["edges"]
    lines = []
    lines.append("; === Auto-Z3 Map Coloring ===")
    lines.append(f"; regions: {len(regions)} | colors: {n_colors}\n")

    for r in regions:
        color_vars = []
        for c in range(1, n_colors + 1):
            v = f"{r}{c}"
            lines.append(f"(declare-const {v} Bool)")
            color_vars.append(v)
        lines.append(f"(assert {exactly_one(*color_vars)})\n")

    lines.append("; edges")
    for u, v in edges:
        for c in range(1, n_colors + 1):
            lines.append(f"(assert (not (and {u}{c} {v}{c})))")
    lines.append("(check-sat)")
    return "\n".join(lines)


MODEL_BOOL_RE = re.compile(r"\(\s*define-fun\s+([^\s]+)\s+\(\)\s+Bool\s+(true|false)\s*\)", re.M)


def parse_model_to_assignment(model_text: str) -> Dict[str, int]:
    true_vars = []
    for name, val in MODEL_BOOL_RE.findall(model_text or ""):
        if val == "true":
            true_vars.append(name)
    assignment: Dict[str, int] = {}
    for var in true_vars:
        m = re.match(r"^(.+?)(\d+)$", var)
        if not m:
            continue
        region, color_idx = m.group(1), int(m.group(2))
        assignment[region] = color_idx
    return assignment


def solve_coloring(graph: Dict, n_colors: int) -> Tuple[str, Dict[str, int], str, str]:
    smt = build_smt(graph, n_colors)
    status, model, raw = run_z3_safely(smt, request_model=True)
    if status == "sat":
        return status, parse_model_to_assignment(model), model, smt
    return status, {}, model or raw, smt
