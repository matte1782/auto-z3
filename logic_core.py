from __future__ import annotations
from dataclasses import dataclass
from typing import List, Union, Iterable, Set

# ── AST minimale e sicuro (niente eval per il builder) ─────────────────────────
@dataclass
class Node:
    op: str
    args: List["Expr"]

Expr = Union[Node, str]   # foglia = nome variabile SMT

# Costruttori di base (core SMT-LIB v2)
def Var(x: str) -> str: return x
def Not(x: Expr) -> Node: return Node('not', [x])
def And(*xs: Expr) -> Node: return Node('and', list(xs))
def Or(*xs: Expr) -> Node: return Node('or', list(xs))
def Implies(a: Expr, b: Expr) -> Node: return Node('=>', [a, b])
def Iff(a: Expr, b: Expr) -> Node: return Node('=', [a, b])  # ↔ come '=' booleana
def Xor(a: Expr, b: Expr) -> Node: return Node('xor', [a, b])

def AtMost(*xs_and_k: Union[Expr, int]) -> Node:
    *xs, k = xs_and_k
    return Node('at-most', [k] + list(xs))

def ExactlyOne(*xs: Expr) -> Node:
    # (and (or xs) ((_ at-most 1) xs))
    return And(Or(*xs), AtMost(*xs, 1))

# ── Emitter SMT-LIB v2 (core + PB AtMost) ─────────────────────────────────────
def emit_expr(e: Expr) -> str:
    if isinstance(e, str):
        return e
    op = e.op
    parts = [emit_expr(a) if not isinstance(a, int) else str(a) for a in e.args]
    if op == 'not': return f"(not {parts[0]})"
    if op in ('and', 'or', 'xor', '=', '=>'): return f"({op} {' '.join(parts)})"
    if op == 'at-most':
        k, xs = parts[0], parts[1:]
        return f"((_ at-most {k}) {' '.join(xs)})"
    raise ValueError(f"Operatore non supportato: {op}")

def _collect_vars_rec(e: Expr, acc: Set[str]):
    if isinstance(e, str): 
        acc.add(e); return
    for a in e.args: _collect_vars_rec(a, acc)

def collect_vars(exprs: Iterable[Expr]) -> List[str]:
    acc: Set[str] = set()
    for e in exprs: _collect_vars_rec(e, acc)
    return sorted(acc, key=str)

# ── Utility SMT2 ───────────────────────────────────────────────────────────────
def declare_block(vars_: List[str]) -> str:
    # dedup e ordine stabile
    vs = []
    seen = set()
    for v in vars_:
        if v and v not in seen:
            vs.append(v); seen.add(v)
    return "\n".join(f"(declare-const {v} Bool)" for v in vs)

def assert_line(s: str) -> str: return f"(assert {s})"
def check_sat() -> str: return "(check-sat)"
def get_model() -> str: return "(get-model)"

def preamble_xor3() -> str:
    return (
        "(define-fun xor3 ((x Bool) (y Bool) (z Bool)) Bool\n"
        "  (and (or x y z) ((_ at-most 1) x y z))\n"
        ")\n"
    )
