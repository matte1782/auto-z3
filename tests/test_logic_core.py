import re
import time

import pytest

from logic_core import (
    And,
    ExactlyOne,
    Iff,
    Implies,
    Not,
    Or,
    Var,
    Xor,
    assert_line,
    check_sat,
    declare_block,
    emit_expr,
)
from z3_runner import run_z3_safely


def _paren_balanced(s: str) -> bool:
    c = 0
    for ch in s:
        if ch == "(":
            c += 1
        elif ch == ")":
            c -= 1
        if c < 0:
            return False
    return c == 0


def _run(smt: str, get_model=True):
    return run_z3_safely(smt, request_model=get_model)


def test_no_Node_leak_in_emit():
    p, q, r = Var("p"), Var("q"), Var("r")
    e = And(Implies(p, q), Or(Not(q), r), Xor(p, r))
    s = emit_expr(e)
    assert "Node(" not in s
    assert _paren_balanced(s)


def test_tautology_complex():
    # (p→q) ∧ (q→r) ∧ p ⇒ r  (tautologia dell’implicazione composta)
    p, q, r = Var("p"), Var("q"), Var("r")
    phi = Implies(And(Implies(p, q), Implies(q, r), p), r)
    smt = "\n".join(
        [
            declare_block(["p", "q", "r"]),
            assert_line(f"(not {emit_expr(phi)})"),
            check_sat(),
        ]
    )
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat", f"Expected unsat, got {status}\n{smt}\n{raw}"


def test_inference_unsat_on_neg_conclusion():
    # Premesse: p, p→q  | Conclusione: q  ⇒ assert(not q) ⇒ UNSAT
    p, q = Var("p"), Var("q")
    smt = "\n".join(
        [
            declare_block(["p", "q"]),
            assert_line(emit_expr(p)),
            assert_line(emit_expr(Implies(p, q))),
            assert_line(f"(not {emit_expr(q)})"),
            check_sat(),
        ]
    )
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat"


def test_equivalence():
    # p↔q  eq  (p→q)∧(q→p)
    p, q = Var("p"), Var("q")
    left = Iff(p, q)
    right = And(Implies(p, q), Implies(q, p))
    smt = "\n".join(
        [
            declare_block(["p", "q"]),
            assert_line(f"(not (= {emit_expr(left)} {emit_expr(right)}))"),
            check_sat(),
        ]
    )
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat"


def test_exactly_one_decl():
    xs = ["a", "b", "c", "d"]
    smt = "\n".join(
        [
            declare_block(xs),
            assert_line(emit_expr(ExactlyOne(*[Var(x) for x in xs]))),
            check_sat(),
        ]
    )
    status, model, raw = _run(smt)
    assert status == "sat"
    # Dovrebbe assegnare esattamente uno a true nel modello
    if model:
        trues = len(re.findall(r"\(define-fun\s+(a|b|c|d)\s+\(\)\s+Bool\s+true\)", model))
        assert trues == 1, f"ExactlyOne viola il modello: {trues} true\n{model}"


@pytest.mark.parametrize("n", [1, 2, 3, 5, 8])
def test_perf_scaling(n):
    # mini benchmark: catena di implicazioni su n variabili
    vs = [f"x{i}" for i in range(n)]
    V = [Var(v) for v in vs]
    conj = And(*[Implies(V[i], V[i + 1]) for i in range(len(V) - 1)]) if n > 1 else V[0]
    phi = Implies(And(conj, V[0]), V[-1])
    smt = "\n".join([declare_block(vs), assert_line(f"(not {emit_expr(phi)})"), check_sat()])
    t0 = time.perf_counter()
    status, model, raw = _run(smt, get_model=False)
    dt = time.perf_counter() - t0
    assert status == "unsat"
    assert dt < 2.0, f"Rallentamento anomalo: {dt:.3f}s"
