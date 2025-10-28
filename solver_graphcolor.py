# solver_graphcolor.py
from typing import Dict, List, Tuple, Optional
import re

try:
    import networkx as nx  # per fallback greedy
except Exception:
    nx = None

from z3_runner import run_z3_safely

def _preamble_xorn(k: int) -> str:
    # xorn_k: or(...k) AND at-most-1(...)
    args = " ".join([f"(c{i} Bool)" for i in range(1, k+1)])
    vars_ = " ".join([f"c{i}" for i in range(1, k+1)])
    return f"(define-fun xorn_{k} ({args}) Bool (and (or {vars_}) ((_ at-most 1) {vars_})))"

def build_graphcolor_smt(nodes: List[str], edges: List[Tuple[str,str]], k: int) -> str:
    assert k >= 2
    lines = [_preamble_xorn(k), "; nodes"]
    for n in nodes:
        for i in range(1, k+1):
            lines.append(f"(declare-const {n}{i} Bool)")
        xs = " ".join([f"{n}{i}" for i in range(1, k+1)])
        lines.append(f"(assert (xorn_{k} {xs}))")
        lines.append("")

    lines.append("; edges (no same color on endpoints)")
    for (u, v) in edges:
        for i in range(1, k+1):
            lines.append(f"(assert (not (and {u}{i} {v}{i})))")

    lines.append("(check-sat)")
    lines.append("(get-model)")
    return "\n".join(lines)

def _parse_model_bools(model_txt: str) -> Dict[str, bool]:
    # (define-fun <name> () Bool true/false)
    out: Dict[str,bool] = {}
    if not model_txt:
        return out
    for m in re.finditer(r"\(define-fun\s+([^\s]+)\s+\(\)\s+Bool\s+(true|false)\)", model_txt):
        name, val = m.group(1), m.group(2)
        out[name] = (val == "true")
    return out

def solve_graph_coloring(nodes: List[str], edges: List[Tuple[str,str]], k: int) -> Tuple[str, Optional[Dict[str,int]], str]:
    """
    Ritorna: (status, assignment|None, raw_output)
    assignment: es. {'LOM': 2, 'LIG': 1, ...} con colori 1..k
    """
    smt = build_graphcolor_smt(nodes, edges, k)
    status, model, raw = run_z3_safely(smt, request_model=True)

    if status == "sat":
        bools = _parse_model_bools(model if model else raw)
        assign: Dict[str,int] = {}
        for n in nodes:
            for i in range(1, k+1):
                if bools.get(f"{n}{i}", False):
                    assign[n] = i
                    break
        # Sanity: se qualcosa è senza colore, tenta fallback greedy
        if len(assign) != len(nodes) and nx:
            g = nx.Graph()
            g.add_nodes_from(nodes)
            g.add_edges_from(edges)
            greedy = nx.coloring.greedy_color(g, strategy="largest_first")
            # greedy_color restituisce {node: color_index_0based}
            if greedy and max(greedy.values(), default=-1) + 1 <= k:
                return "sat", {n: greedy[n] + 1 for n in nodes}, raw or model
        return "sat", assign, raw or model

    if status == "unsat" and nx:
        # Fallback: prova greedy solo per proporre una demo parziale
        g = nx.Graph()
        g.add_nodes_from(nodes)
        g.add_edges_from(edges)
        greedy = nx.coloring.greedy_color(g, strategy="largest_first")
        if greedy and max(greedy.values(), default=-1) + 1 <= k:
            # In teoria SAT, ma Z3 ha dato unsat? Lo segnaliamo come "unknown"
            return "unknown", {n: greedy[n] + 1 for n in nodes}, raw or model

    return status, None, raw or model
