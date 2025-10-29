# tests/test_logic_stress.py
import random
import time
from typing import List

from logic_core import assert_line, check_sat, declare_block
from z3_runner import run_z3_safely


def _run(smt: str, get_model: bool = False):
    return run_z3_safely(smt, request_model=get_model)


def _mk_planted_sat_3cnf(n_vars: int, m_clauses: int, seed: int = 1337) -> str:
    """
    Build a 3-CNF with a planted random assignment so it's guaranteed SAT.
    We generate each clause so that at least one literal is satisfied by 'assign'.
    """
    rng = random.Random(seed)
    vars_ = [f"x{i}" for i in range(1, n_vars + 1)]
    assign = {v: rng.choice([True, False]) for v in vars_}

    clauses: List[str] = []
    for _ in range(m_clauses):
        lits = []
        chosen = rng.sample(vars_, 3)
        # Ensure at least one literal agrees with the planted assignment
        sat_pos = rng.randrange(3)
        for j, v in enumerate(chosen):
            if j == sat_pos:
                lit = v if assign[v] else f"(not {v})"
            else:
                # random polarity
                lit = v if rng.random() < 0.5 else f"(not {v})"
            lits.append(lit)
        clause = f"(or {' '.join(lits)})"
        clauses.append(clause)

    lines = [declare_block(vars_)]
    for cl in clauses:
        lines.append(assert_line(cl))
    lines.append(check_sat())
    return "\n".join(lines)


def test_large_random_cnf_sat_scalability():
    """50 vars, 200 random 3-CNF clauses with planted solution ⇒ SAT, time bound sanity check."""
    smt = _mk_planted_sat_3cnf(n_vars=50, m_clauses=200, seed=2025)
    t0 = time.perf_counter()
    status, model, raw = _run(smt, get_model=False)
    dt = time.perf_counter() - t0

    assert status == "sat", f"Expected SAT for planted 3-CNF, got {status}.\n{raw}"
    # generous limit to avoid CI flakiness; adjust if machines are slow/fast
    assert dt < 5.0, f"Unexpected slowdown on planted 3-CNF (50/200): {dt:.2f}s"


def test_trivial_contradiction_unsat():
    """Minimal UNSAT sanity check on large var sets: assert x and (not x)."""
    vars_ = [f"x{i}" for i in range(1, 51)]
    lines = [
        declare_block(vars_),
        assert_line("x1"),
        assert_line("(not x1)"),
        check_sat(),
    ]
    smt = "\n".join(lines)
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat", f"Expected UNSAT for x ∧ ¬x, got {status}.\n{raw}"
