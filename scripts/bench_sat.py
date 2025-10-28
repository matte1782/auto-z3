# ───────────────────────────────────────────────────────────────
# bench_sat.py — benchmark suite for Auto-Z3
# ───────────────────────────────────────────────────────────────
import os
import sys
import time
import json
import argparse

# ✅ Fix: ensure project root is in sys.path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from logic_core import Var, Not, And, Or, Implies, ExactlyOne, emit_expr, declare_block, assert_line, check_sat
from z3_runner import run_z3_safely

# ───────────────────────────────────────────────────────────────
# Helpers
# ───────────────────────────────────────────────────────────────
def bench_case(name, smt, outdir, request_model=False):
    """Run one benchmark case and store .smt2 output + JSON summary."""
    t0 = time.perf_counter()
    status, model, raw = run_z3_safely(smt, request_model=request_model)
    dt = time.perf_counter() - t0

    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, f"{name}.smt2"), "w", encoding="utf-8") as f:
        f.write(smt)

    return {"name": name, "status": status, "time_s": round(dt, 4)}

def mk_chain_unsat(n):
    """Generate (p1 → p2 → ... → pn) ∧ p1 ⇒ pn : tautology ⇒ unsat."""
    vs = [f"x{i}" for i in range(n)]
    V = [Var(v) for v in vs]
    conj = And(*[Implies(V[i], V[i+1]) for i in range(len(V)-1)]) if n > 1 else V[0]
    phi = Implies(And(conj, V[0]), V[-1])
    smt = "\n".join([
        declare_block(vs),
        assert_line(f"(not {emit_expr(phi)})"),
        check_sat()
    ])
    return smt

# ───────────────────────────────────────────────────────────────
# Main
# ───────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(description="Benchmark SAT performance of Auto-Z3")
    ap.add_argument("--out", default="bench_out", help="Output directory for .smt2 and JSON results")
    args = ap.parse_args()
    outdir = args.out

    results = []
    for n in [4, 8, 16, 32, 64]:
        smt = mk_chain_unsat(n)
        res = bench_case(f"chain_unsat_{n}", smt, outdir, request_model=False)
        results.append(res)

    print("name,status,time_s")
    for r in results:
        print(f"{r['name']},{r['status']},{r['time_s']}")

    with open(os.path.join(outdir, "results.json"), "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)

if __name__ == "__main__":
    main()
