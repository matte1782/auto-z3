# tests/test_fol_beta_min.py
# Minimal FOL (βeta) tests by emitting SMT-LIB directly.
# We avoid importing the app's internal FOL helpers to keep tests stable.

from z3_runner import run_z3_safely


def _run(smt: str, get_model: bool = False):
    return run_z3_safely(smt, request_model=get_model)


def test_fol_universal_implication_unsat():
    """
    ∀x (P(x) → Q(x)), P(a), ¬Q(a)  ⇒  UNSAT
    """
    smt = """
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (=> (P x) (Q x))))
(assert (P a))
(assert (not (Q a)))
(check-sat)
"""
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat", f"Expected UNSAT, got {status}.\n{raw}"


def test_fol_exists_sat():
    """
    ∃x P(x) is SAT when domain is non-empty and P is unconstrained.
    """
    smt = """
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const a U)
(assert (exists ((x U)) (P x)))
(check-sat)
(get-model)
"""
    status, model, raw = _run(smt, get_model=True)
    assert status == "sat", f"Expected SAT, got {status}.\n{raw}"
    assert "(define-fun P" in model, "Model should interpret predicate P."


def test_fol_binary_predicate_consistency_unsat():
    """
    Add a binary predicate R/2 with functional inconsistency:
      - ∀x ∀y (R(x,y) → S(x)) and ∀x ¬S(x) and ∃x∃y R(x,y)  ⇒  UNSAT
    """
    smt = """
(declare-sort U 0)
(declare-fun R (U U) Bool)
(declare-fun S (U) Bool)
(assert (forall ((x U) (y U)) (=> (R x y) (S x))))
(assert (forall ((x U)) (not (S x))))
(assert (exists ((x U) (y U)) (R x y)))
(check-sat)
"""
    status, model, raw = _run(smt, get_model=False)
    assert status == "unsat", (
        f"Expected UNSAT for inconsistent binary predicate theory, got {status}.\n{raw}"
    )
