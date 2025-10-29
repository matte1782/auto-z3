import time

from z3_runner import run_z3_safely


def _xorN_def(n: int) -> str:
    args = " ".join(f"(c{i} Bool)" for i in range(n))
    syms = " ".join(f"c{i}" for i in range(n))
    return f"(define-fun xor{n} ({args}) Bool\n  (and (or {syms}) ((_ at-most 1) {syms}))\n)"


def _mk_smt_from_adj(adj: dict[str, set[str]], n_colors: int):
    # Dichiarazioni: per ogni ISO_A3 → Bool per ciascun colore 0..n-1
    countries = sorted(adj.keys())
    lines = [_xorN_def(n_colors), "", "; ───────────── nodes"]
    for iso in countries:
        for k in range(n_colors):
            lines.append(f"(declare-const {iso}_{k} Bool)")
        args = " ".join(f"{iso}_{k}" for k in range(n_colors))
        lines.append(f"(assert (xor{n_colors} {args}))")
        lines.append("")
    # Edge constraints: per ogni (u,v) vietiamo stesso colore
    lines.append("; ───────────── edges")
    done = set()
    for u in countries:
        for v in adj[u]:
            if (v, u) in done or u == v:
                continue
            done.add((u, v))
            for k in range(n_colors):
                lines.append(f"(assert (not (and {u}_{k} {v}_{k})))")
    lines += ["(check-sat)"]
    return "\n".join(lines)


def _run(smt, get_model=True):
    return run_z3_safely(smt, request_model=get_model)


def _count_true(model_text, iso, n):
    cnt = 0
    for k in range(n):
        key = f"(define-fun {iso}_{k} () Bool\n    true)"
        if key in model_text:
            cnt += 1
    return cnt


def test_south_america_unsat_3colors(south_adj, paths):
    smt = _mk_smt_from_adj(south_adj, 3)
    status, model, raw = _run(smt, get_model=False)
    # Atteso UNSAT (clique K4: BOL, BRA, PAR, ARG)
    assert status == "unsat", f"Sud America a 3 colori dovrebbe essere UNSAT, got {status}\n{raw}"
    # Salva per revisione manuale
    outp = paths["artifacts"] + "/south_america_3colors.smt2"
    with open(outp, "w", encoding="utf-8") as f:
        f.write(smt)


def test_south_america_sat_4colors(south_adj, paths):
    smt = _mk_smt_from_adj(south_adj, 4)
    t0 = time.perf_counter()
    status, model, raw = _run(smt, get_model=True)
    dt = time.perf_counter() - t0
    assert status == "sat", f"Sud America a 4 colori deve essere SAT, got {status}\n{raw}"
    # Verifica esattamente un colore per nodo
    for iso in sorted(south_adj.keys()):
        assert _count_true(model, iso, 4) == 1, f"{iso} non ha ExactlyOne nel modello"
    assert dt < 5.0, f"Solving troppo lento: {dt:.2f}s"
    outp = paths["artifacts"] + "/south_america_4colors.smt2"
    with open(outp, "w", encoding="utf-8") as f:
        f.write(smt)


def test_central_america_sat_3colors(central_adj, paths):
    smt = _mk_smt_from_adj(central_adj, 3)
    status, model, raw = _run(smt, get_model=True)
    assert status == "sat", f"America Centrale a 3 colori atteso SAT, got {status}\n{raw}"
    for iso in sorted(central_adj.keys()):
        assert _count_true(model, iso, 3) == 1
    outp = paths["artifacts"] + "/central_america_3colors.smt2"
    with open(outp, "w", encoding="utf-8") as f:
        f.write(smt)
