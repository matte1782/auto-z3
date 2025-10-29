# fol_core.py — FOL mini-core + SMT-LIB2 + grounding (v1)

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Dict, List, Optional, Union


# -----------------------
# Terms & Formulas (AST)
# -----------------------
@dataclass
class Term:
    op: str  # 'var' | 'const' | 'func'
    name: str
    args: List[Term]


def VarT(name: str) -> Term:
    return Term("var", name, [])


def Const(name: str) -> Term:
    return Term("const", name, [])


def Func(name: str, *args: Term) -> Term:
    return Term("func", name, list(args))


@dataclass
class Fml:
    op: str  # 'pred' | 'eq' | 'not' | 'and' | 'or' | '=>' | 'iff' | 'forall' | 'exists'
    name: Optional[str]
    args: List[Union[Fml, Term]]
    bind: List[str] = None  # bound var names for quantifiers


def Pred(name: str, *ts: Term) -> Fml:
    return Fml("pred", name, list(ts))


def Eq(a: Term, b: Term) -> Fml:
    return Fml("eq", None, [a, b])


def Not(p: Fml) -> Fml:
    return Fml("not", None, [p])


def And(*ps: Fml) -> Fml:
    return Fml("and", None, list(ps))


def Or(*ps: Fml) -> Fml:
    return Fml("or", None, list(ps))


def Implies(a: Fml, b: Fml) -> Fml:
    return Fml("=>", None, [a, b])


def Iff(a: Fml, b: Fml) -> Fml:
    return Fml("iff", None, [a, b])


def ForAll(vars_: List[str], body: Fml) -> Fml:
    return Fml("forall", None, [body], bind=list(vars_))


def Exists(vars_: List[str], body: Fml) -> Fml:
    return Fml("exists", None, [body], bind=list(vars_))


# -----------------------
# Emissione SMT-LIB2
# -----------------------
def emit_term(t: Term) -> str:
    if t.op in ("var", "const"):
        return t.name
    # func
    return f"({t.name} {' '.join(emit_term(a) for a in t.args)})"


def emit_fml(phi: Fml) -> str:
    if phi.op == "pred":
        return f"({phi.name} {' '.join(emit_term(a) for a in phi.args)})"
    if phi.op == "eq":
        a, b = phi.args
        return f"(= {emit_term(a)} {emit_term(b)})"
    if phi.op == "not":
        return f"(not {emit_fml(phi.args[0])})"
    if phi.op in ("and", "or", "=>", "iff"):
        a = [emit_fml(x) for x in phi.args]
        smt_op = phi.op if phi.op != "iff" else "="
        return f"({smt_op} {' '.join(a)})"
    if phi.op in ("forall", "exists"):
        assert phi.bind is not None
        binder = "forall" if phi.op == "forall" else "exists"
        # Tutte le var sono del sort U
        binders = " ".join(f"({v} U)" for v in phi.bind)
        return f"({binder} ({binders}) {emit_fml(phi.args[0])})"
    raise ValueError(f"Operatore formula non supportato: {phi.op}")


# -----------------------
# Sostituzione & Grounding
# -----------------------
def subst_term(t: Term, env: Dict[str, Term]) -> Term:
    if t.op == "var" and t.name in env:
        return env[t.name]
    if t.op == "func":
        return Func(t.name, *(subst_term(a, env) for a in t.args))
    return t


def subst_fml(phi: Fml, env: Dict[str, Term]) -> Fml:
    if phi.op == "pred":
        return Pred(phi.name, *(subst_term(a, env) for a in phi.args))
    if phi.op == "eq":
        a, b = phi.args
        return Eq(subst_term(a, env), subst_term(b, env))
    if phi.op in ("not", "and", "or", "=>", "iff"):
        return Fml(phi.op, None, [subst_fml(x, env) for x in phi.args])
    if phi.op in ("forall", "exists"):
        # Evita di sostituire bound vars
        body_env = {k: v for k, v in env.items() if k not in phi.bind}
        return Fml(phi.op, None, [subst_fml(phi.args[0], body_env)], bind=list(phi.bind))
    raise ValueError(f"Operatore formula non supportato in subst: {phi.op}")


def ground_quantifiers(phi: Fml, domain_consts: List[str]) -> Fml:
    """Espande forall/exists su dominio finito: combina tutte le assegnazioni."""
    if phi.op == "forall":
        vars_ = phi.bind or []
        body = phi.args[0]
        if not vars_:
            return ground_quantifiers(body, domain_consts)
        combos = product(domain_consts, repeat=len(vars_))
        conjuncts = []
        for tup in combos:
            env = {v: Const(c) for v, c in zip(vars_, tup)}
            conjuncts.append(ground_quantifiers(subst_fml(body, env), domain_consts))
        return And(*conjuncts) if conjuncts else And()
    if phi.op == "exists":
        vars_ = phi.bind or []
        body = phi.args[0]
        if not vars_:
            return ground_quantifiers(body, domain_consts)
        combos = product(domain_consts, repeat=len(vars_))
        disjuncts = []
        for tup in combos:
            env = {v: Const(c) for v, c in zip(vars_, tup)}
            disjuncts.append(ground_quantifiers(subst_fml(body, env), domain_consts))
        return Or(*disjuncts) if disjuncts else Or()
    # discendi
    if phi.op in ("not", "and", "or", "=>", "iff", "pred", "eq"):
        if phi.op in ("pred", "eq"):
            return phi
        return Fml(phi.op, None, [ground_quantifiers(x, domain_consts) for x in phi.args])
    return phi


# -----------------------
# DSL sicura per UI
# -----------------------
def make_env(
    preds: Dict[str, int],
    funs: Dict[str, int],
    consts: List[str],
    vars_for_dsl: List[str],
) -> Dict[str, object]:
    """
    Crea un env per eval sicuro:
      - nomi dei predicati/funzioni sono callables che costruiscono Pred/Func
      - variabili e costanti sono Terms
      - operatori logici: Not/And/Or/Implies/Iff, Eq
    """
    env = {
        "Not": Not,
        "And": And,
        "Or": Or,
        "Implies": Implies,
        "Iff": Iff,
        "Eq": Eq,
        # costruttori term/fml espliciti se servono:
        "VarT": VarT,
        "Const": Const,
        "Func": Func,
        "Pred": Pred,
    }
    for c in consts:
        env[c] = Const(c)
    for v in vars_for_dsl:
        env[v] = VarT(v)
    for name, ar in preds.items():

        def _mk_pred(nm=name, arity=ar):
            def _inner(*args):
                if len(args) != arity:
                    raise ValueError(f"Predicato {nm}/{arity}: forniti {len(args)} arg.")
                return Pred(nm, *args)

            return _inner

        env[name] = _mk_pred()
    for name, ar in funs.items():

        def _mk_fun(nm=name, arity=ar):
            def _inner(*args):
                if len(args) != arity:
                    raise ValueError(f"Funzione {nm}/{arity}: forniti {len(args)} arg.")
                return Func(nm, *args)

            return _inner

        env[name] = _mk_fun()
    return env


# -----------------------
# SMT-LIB builder
# -----------------------
def build_smt2_universe(
    domain_consts: List[str],
    predicates: Dict[str, int],
    functions: Dict[str, int],
    facts: List[str],
    formulas: List[Fml],
    task: str = "sat",  # "sat" | "validity" | "inference"
    inference_goal: Optional[Fml] = None,
    use_grounding: bool = True,
) -> str:
    """
    Genera SMT-LIB2:
      (declare-sort U 0)
      (declare-const a U) ...
      (declare-fun P (U U) Bool) ...
      + assert(fatti)
      + assert(formule/task)
    """
    lines = []
    lines.append("; FOL module (U = universo)")
    lines.append("(declare-sort U 0)")
    # costanti (universo)
    for c in domain_consts:
        lines.append(f"(declare-const {c} U)")
    # funzioni/predicati
    for f, ar in functions.items():
        dom = " ".join(["U"] * ar)
        lines.append(f"(declare-fun {f} ({dom}) U)")
    for p, ar in predicates.items():
        dom = " ".join(["U"] * ar)
        lines.append(f"(declare-fun {p} ({dom}) Bool)")
    lines.append("")

    # parser semplicissimo per fatti ground: es. P(a,b), Eq(f(a), b) oppure a=b
    def _emit_fact(s: str) -> str:
        s = s.strip()
        if not s:
            return ""
        if "=" in s and not s.startswith("Eq("):
            lhs, rhs = [t.strip() for t in s.split("=", 1)]
            return f"(assert (= {lhs} {rhs}))"
        # P(a,b) o Eq(f(a),b)
        return f"(assert {s})"

    for ft in facts:
        e = _emit_fact(ft)
        if e:
            lines.append(e)

    # formule
    def _emit(phi: Fml) -> str:
        ph = phi
        if use_grounding:
            ph = ground_quantifiers(phi, domain_consts)
        return f"(assert {emit_fml(ph)})"

    if task == "sat":
        for ph in formulas:
            lines.append(_emit(ph))
        lines.append("(check-sat)")
    elif task == "validity":
        # validità di una sola formula: assert (not φ)
        assert len(formulas) == 1, "Validity: attesa una sola formula"
        ph = formulas[0]
        if use_grounding:
            ph = ground_quantifiers(ph, domain_consts)
        lines.append(f"(assert (not {emit_fml(ph)}))")
        lines.append("(check-sat)")
    else:  # inference: facts/formulas ⊢ goal
        assert inference_goal is not None, "Inference: serve la conclusione"
        for ph in formulas:
            lines.append(_emit(ph))
        goal = inference_goal
        if use_grounding:
            goal = ground_quantifiers(goal, domain_consts)
        lines.append(f"(assert (not {emit_fml(goal)}))")
        lines.append("(check-sat)")

    return "\n".join(lines) + ("\n" if not lines[-1].endswith("\n") else "")
