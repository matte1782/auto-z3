#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
validate_benchmarks.py
Independent validator for Auto-Z3 benchmarks and artifacts.

Fixes:
- Adds project root to sys.path so `import z3_runner` works when executed from scripts/.
- If import still fails, loads z3_runner.py via SourceFileLoader as a fallback.

Run:
  python scripts/validate_benchmarks.py --bench-dir tests/_artifacts
  python scripts/validate_benchmarks.py --bench-dir tests/_artifacts --fail-on-warn
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

# ── PATH BOOTSTRAP: ensure repo root is importable
THIS_FILE = Path(__file__).resolve()
REPO_ROOT = THIS_FILE.parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

# Try normal import; if it fails, fall back to direct file loading
try:
    from z3_runner import run_z3_safely
except Exception:
    try:
        from importlib.machinery import SourceFileLoader
        zr_path = REPO_ROOT / "z3_runner.py"
        if not zr_path.exists():
            raise FileNotFoundError(f"z3_runner.py not found at {zr_path}")
        z3_mod = SourceFileLoader("z3_runner", str(zr_path)).load_module()
        run_z3_safely = z3_mod.run_z3_safely  # type: ignore[attr-defined]
    except Exception as ex:
        print("[validator] FATAL: cannot import z3_runner.run_z3_safely:", ex, file=sys.stderr)
        sys.exit(2)

# ──────────────────────────────────────────────────────────────────────────────
# Discovery
# ──────────────────────────────────────────────────────────────────────────────

def discover_smt2(root: str) -> List[str]:
    out = []
    for d, _, files in os.walk(root):
        for fn in files:
            if fn.endswith(".smt2"):
                out.append(os.path.join(d, fn))
    return sorted(out)

# ──────────────────────────────────────────────────────────────────────────────
# Tiny SMT-LIB tokenizer + parser
# ──────────────────────────────────────────────────────────────────────────────

_TOKEN = re.compile(r"""\s*(;[^\n]*\n|[()]|"(?:[^"\\]|\\.)*"|[^\s()]+)""")

def _tokenize(s: str) -> List[str]:
    tokens, pos = [], 0
    while pos < len(s):
        m = _TOKEN.match(s, pos)
        if not m: break
        tok = m.group(1); pos = m.end()
        if not tok.strip(): continue
        if tok.startswith(";"):  # comment
            continue
        tokens.append(tok)
    return tokens

def _parse(tokens: List[str], i: int = 0) -> Tuple[Any, int]:
    if i >= len(tokens): raise ValueError("Unexpected EOF")
    t = tokens[i]
    if t == "(":
        out, i = [], i + 1
        while i < len(tokens) and tokens[i] != ")":
            node, i = _parse(tokens, i)
            out.append(node)
        if i >= len(tokens) or tokens[i] != ")": raise ValueError("Unbalanced parens")
        return out, i + 1
    if t == ")": raise ValueError("Unexpected ')'")
    return t, i + 1

def parse_smt2(s: str) -> List[Any]:
    tokens = _tokenize(s)
    exprs, i = [], 0
    while i < len(tokens):
        node, i = _parse(tokens, i)
        exprs.append(node)
    return exprs

# ──────────────────────────────────────────────────────────────────────────────
# Model parsing
# ──────────────────────────────────────────────────────────────────────────────

_MODEL_BOOL = re.compile(
    r"\(define-fun\s+([A-Za-z0-9_\-\.]+)\s+\(\)\s+Bool\s+(true|false)\s*\)",
    re.MULTILINE
)

def parse_bool_model(model_text: str) -> Dict[str, bool]:
    return {sym: (val == "true") for sym, val in _MODEL_BOOL.findall(model_text or "")}

# ──────────────────────────────────────────────────────────────────────────────
# Evaluator (Bool subset)
# ──────────────────────────────────────────────────────────────────────────────

class EvalEnv:
    def __init__(self, model: Dict[str, bool]):
        self.model = dict(model)  # symbol -> bool
        self.fun_defs: Dict[str, Tuple[List[str], Any]] = {}  # name -> (args, body)

    def define_fun(self, name: str, arg_names: List[str], body: Any):
        self.fun_defs[name] = (arg_names, body)

    def _lookup(self, sym: str) -> bool:
        if sym in self.model: return self.model[sym]
        self.model[sym] = False  # default false if missing
        return False

    def eval(self, sexpr: Any) -> bool:
        if isinstance(sexpr, str):
            if sexpr in ("true", "false"): return sexpr == "true"
            return self._lookup(sexpr)
        if not isinstance(sexpr, list) or not sexpr:
            raise ValueError(f"Bad node: {sexpr}")
        op, args = sexpr[0], sexpr[1:]

        if op == "true": return True
        if op == "false": return False
        if op == "not":
            assert len(args) == 1
            return not self.eval(args[0])
        if op == "and":
            return all(self.eval(a) for a in args)
        if op == "or":
            return any(self.eval(a) for a in args)
        if op == "=>":
            assert len(args) == 2
            return (not self.eval(args[0])) or self.eval(args[1])
        if op == "=":
            assert len(args) == 2
            return self.eval(args[0]) == self.eval(args[1])
        if op == "xor":
            assert len(args) == 2
            return self.eval(args[0]) ^ self.eval(args[1])

        # ((_ at-most k) ...)
        if isinstance(op, list) and len(op) == 3 and op[0] == "_" and op[1] == "at-most":
            k = int(op[2])
            return sum(1 for a in args if self.eval(a)) <= k

        # function call (e.g., xor3)
        if isinstance(op, str) and op in self.fun_defs:
            formals, body = self.fun_defs[op]
            if len(formals) != len(args):
                raise ValueError(f"Arity mismatch for {op}: {len(formals)} vs {len(args)}")
            saved = {}
            try:
                for n, ex in zip(formals, args):
                    saved[n] = self.model.get(n, None)
                    self.model[n] = self.eval(ex)
                return self.eval(body)
            finally:
                for n, old in saved.items():
                    if old is None: self.model.pop(n, None)
                    else: self.model[n] = old

        # variable fallback
        if isinstance(op, str):
            return self._lookup(op)

        raise ValueError(f"Unsupported operator: {op}")

# ──────────────────────────────────────────────────────────────────────────────
# Extractors
# ──────────────────────────────────────────────────────────────────────────────

def collect_asserts_and_defs(exprs: List[Any]) -> Tuple[List[Any], List[Tuple[str, List[str], Any]]]:
    asserts, fun_defs = [], []
    for e in exprs:
        if isinstance(e, list) and e:
            h = e[0]
            if h == "assert" and len(e) == 2:
                asserts.append(e[1])
            elif h == "define-fun" and len(e) >= 5:
                name = e[1]
                arg_decl = e[2]
                body = e[4]
                args = [p[0] for p in arg_decl] if isinstance(arg_decl, list) else []
                fun_defs.append((name, args, body))
    return asserts, fun_defs

def maybe_extract_map_graph(exprs: List[Any]) -> Tuple[set, set, int]:
    nodes, edges, K = set(), set(), -1

    # infer K from (define-fun xorK ...)
    for e in exprs:
        if isinstance(e, list) and len(e) >= 5 and e[0] == "define-fun":
            name = e[1]
            if isinstance(name, str) and name.startswith("xor") and name[3:].isdigit():
                K = int(name[3:])

    def _base(sym: str) -> str:
        return sym.rsplit("_", 1)[0] if "_" in sym else sym

    for e in exprs:
        if isinstance(e, list) and len(e) == 2 and e[0] == "assert":
            body = e[1]
            if isinstance(body, list) and len(body) == 2 and body[0] == "not":
                inner = body[1]
                if isinstance(inner, list) and len(inner) == 3 and inner[0] == "and":
                    a, b = inner[1], inner[2]
                    if isinstance(a, str) and isinstance(b, str):
                        u, v = sorted((_base(a), _base(b)))
                        if u != v:
                            edges.add((u, v)); nodes.update([u, v])
    return nodes, edges, K

def max_clique_lower_bound(nodes: set, edges: set, max_try: int = 6) -> int:
    from itertools import combinations
    adj = {u: set() for u in nodes}
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    best = 1
    nl = sorted(nodes)
    for r in range(2, max_try + 1):
        for comb in combinations(nl, r):
            if all((comb[j] in adj[comb[i]]) for i in range(r) for j in range(i+1, r)):
                best = r
    return best

# ──────────────────────────────────────────────────────────────────────────────
# Validation
# ──────────────────────────────────────────────────────────────────────────────

class ValidationError(Exception): pass

def validate_instance(path: str, fail_on_warn: bool = False) -> None:
    with open(path, "r", encoding="utf-8") as f:
        smt = f.read()

    status, model_txt, raw = run_z3_safely(smt, request_model=True)

    exprs = parse_smt2(smt)
    asserts, fun_defs = collect_asserts_and_defs(exprs)

    if status == "sat":
        model = parse_bool_model(model_txt)
        env = EvalEnv(model)
        for (n, args, body) in fun_defs:
            env.define_fun(n, args, body)

        for i, a in enumerate(asserts, 1):
            if not env.eval(a):
                raise ValidationError(
                    f"[SAT] Assertion #{i} evaluates to FALSE under returned model "
                    f"in {os.path.basename(path)}.\nAssert: {a}\n"
                )
        print(f"[OK] {os.path.basename(path)} — SAT model validates {len(asserts)} asserts.")

    elif status == "unsat":
        nodes, edges, K = maybe_extract_map_graph(exprs)
        if nodes and edges and K >= 0:
            clique_lb = max_clique_lower_bound(nodes, edges, max_try=6)
            if clique_lb > K:
                print(f"[OK] {os.path.basename(path)} — UNSAT consistent (K={K} < clique {clique_lb}).")
            else:
                msg = (f"[WARN] {os.path.basename(path)} — UNSAT but clique lower bound "
                       f"is {clique_lb} with K={K}. Review recommended.")
                print(msg)
                if fail_on_warn:
                    raise ValidationError(msg)
        else:
            print(f"[OK] {os.path.basename(path)} — UNSAT (non-map or no K detected).")

    else:
        raise ValidationError(f"[ERROR] {os.path.basename(path)} — Solver status: {status}\n{raw}")

# ──────────────────────────────────────────────────────────────────────────────
# CLI
# ──────────────────────────────────────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser(description="Validate Auto-Z3 benchmarks/models independently.")
    ap.add_argument("--bench-dir", default="tests/_artifacts", help="Directory to scan for .smt2 files")
    ap.add_argument("--fail-on-warn", action="store_true", help="Treat UNSAT consistency warnings as failures")
    args = ap.parse_args()

    smt_files = discover_smt2(args.bench_dir)
    if not smt_files:
        print(f"[validator] No .smt2 files found under: {args.bench_dir}", file=sys.stderr)
        sys.exit(1)

    failures = 0
    for p in smt_files:
        try:
            validate_instance(p, fail_on_warn=args.fail_on_warn)
        except ValidationError as ex:
            print(str(ex), file=sys.stderr)
            failures += 1
        except Exception as ex:
            print(f"[validator] Unexpected error on {p}: {ex}", file=sys.stderr)
            failures += 1

    if failures:
        print(f"[validator] FAILURES: {failures}", file=sys.stderr)
        sys.exit(1)
    print("[validator] All benchmark instances validated successfully.")
    sys.exit(0)

if __name__ == "__main__":
    main()
