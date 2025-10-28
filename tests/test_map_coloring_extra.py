# tests/test_map_coloring_extra.py
import time
import pytest
from z3_runner import run_z3_safely

def _xorN_def(n: int) -> str:
    args = " ".join(f"(c{i} Bool)" for i in range(n))
    syms = " ".join(f"c{i}" for i in range(n))
    return (
        f"(define-fun xor{n} ({args}) Bool\n"
        f"  (and (or {syms}) ((_ at-most 1) {syms}))\n"
        f")"
    )

def _mk_smt_from_adj(adj: dict[str,set[str]], n_colors: int):
    countries = sorted(adj.keys())
    lines = [_xorN_def(n_colors), "", "; ───────────── nodes" ]
    for iso in countries:
        for k in range(n_colors):
            lines.append(f"(declare-const {iso}_{k} Bool)")
        args = " ".join(f"{iso}_{k}" for k in range(n_colors))
        lines.append(f"(assert (xor{n_colors} {args}))")
        lines.append("")
    lines.append("; ───────────── edges")
    seen = set()
    for u in countries:
        for v in adj[u]:
            if u == v or (v, u) in seen:
                continue
            seen.add((u, v))
            for k in range(n_colors):
                lines.append(f"(assert (not (and {u}_{k} {v}_{k})))")
    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)

def _run(smt, get_model=True):
    return run_z3_safely(smt, request_model=get_model)

def _count_true(model_text: str, iso: str, n: int) -> int:
    # Count occurrences of (define-fun ISO_k () Bool\n    true)
    return sum(1 for k in range(n) if f"(define-fun {iso}_{k} () Bool\n    true)" in model_text)

def test_south_america_sat_5colors(south_adj, paths):
    """South America must be SAT with ≥4 colours; here we check K=5 and the xor5 syntax."""
    k = 5
    smt = _mk_smt_from_adj(south_adj, k)
    t0 = time.perf_counter()
    status, model, raw = _run(smt, get_model=True)
    dt = time.perf_counter() - t0

    assert status == "sat", f"Expected SAT for South America with {k} colours, got {status}.\n{raw}"
    # Exactly-one per country in the returned model
    for iso in sorted(south_adj.keys()):
        assert _count_true(model, iso, k) == 1, f"{iso} violates exactly-one with {k} colours."

    # Keep a generous time budget to avoid flakes on CI
    assert dt < 8.0, f"Solving took too long ({dt:.2f}s)"
    # Save instance for manual inspection
    outp = paths["artifacts"] + f"/south_america_{k}colors.smt2"
    with open(outp, "w", encoding="utf-8") as f:
        f.write(smt)
