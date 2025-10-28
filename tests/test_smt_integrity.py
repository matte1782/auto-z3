import re
from logic_core import Var, And, Or, Not, emit_expr, declare_block, assert_line, check_sat
from z3_runner import run_z3_safely

def _balanced(s: str) -> bool:
    c=0
    for ch in s:
        if ch=="(": c+=1
        elif ch==")": c-=1
        if c<0: return False
    return c==0

def test_smtlib_integrity_basic():
    p,q,r = Var("p"), Var("q"), Var("r")
    phi = And(Or(p,q), Not(And(q,r)))
    smt = "\n".join([
        declare_block(["p","q","r"]),
        assert_line(emit_expr(phi)),
        check_sat()
    ])
    assert "Node(" not in smt
    assert _balanced(smt)
    status, model, raw = run_z3_safely(smt, request_model=True)
    assert status == "sat"
