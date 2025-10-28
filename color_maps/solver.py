# color_maps/solver.py
from typing import List, Tuple

def _emit_define_xor_k(k: int) -> str:
    # (define-fun xorK ((x0 Bool) ... (x{k-1} Bool)) Bool (and (or ...) ((_ at-most 1) ...)))
    params = " ".join(f"(x{i} Bool)" for i in range(k))
    args = " ".join(f"x{i}" for i in range(k))
    return f"(define-fun xor{k} ({params}) Bool (and (or {args}) ((_ at-most 1) {args})))"

def _emit_node_block(iso: str, k: int) -> str:
    decls = "\n".join(f"(declare-const {iso}_{i} Bool)" for i in range(k))
    args = " ".join(f"{iso}_{i}" for i in range(k))
    return f"{decls}\n(assert (xor{k} {args}))\n"

def _emit_edges(edges: List[Tuple[str, str]], k: int) -> str:
    lines = ["; edges"]
    for (u, v) in edges:
        for i in range(k):
            lines.append(f"(assert (not (and {u}_{i} {v}_{i})))")
    return "\n".join(lines)

def build_map_smt(nodes: List[str], edges: List[Tuple[str, str]], k: int) -> str:
    """
    nodes: lista di ISO_A3 (es. ['ARG','BRA',...])
    edges: lista di coppie (u,v) con u < v (adiacenze)
    k: numero colori
    """
    # Unicità e ordine stabile
    nodes = list(dict.fromkeys(nodes))
    # Normalizza edges come coppie ordinate e uniche
    edges = sorted(set(tuple(sorted(e)) for e in edges))

    # Sanity check
    for (u, v) in edges:
        if u not in nodes or v not in nodes:
            raise ValueError(f"Edge {u}-{v} si riferisce a un nodo inesistente.")

    parts = []
    parts.append(_emit_define_xor_k(k))
    parts.append("; ───────────── nodes")
    for iso in nodes:
        parts.append(_emit_node_block(iso, k))
    parts.append(_emit_edges(edges, k))
    parts.append("(check-sat)")
    parts.append("(get-model)")
    return "\n".join(parts)
