# app_zen.py
import streamlit as st
from typing import List
from logic_core import *
from z3_runner import run_z3_safely
from prof_templates import TEMPLATE_TAUTO, TEMPLATE_EQUIV, TEMPLATE_INFER, TEMPLATE_SAT, TEMPLATE_COLORING, TEMPLATE_XORn

st.set_page_config(page_title="Auto-Z3 — STRICT + Builder (prof style)", layout="wide")
st.title("Auto-Z3 — STRICT + Builder (SMT-LIB v2)")

st.sidebar.header("Modalità")
mode = st.sidebar.selectbox(
    "Scegli la modalità",
    ["Builder formule (STRICT)", "Preset comuni (con esempi del prof)", "Coloring K", "Tester veloce"],
    help="Tutto è guidato: zero frasi libere, output SMT-LIB v2 pronto per Z3."
)

def help_info(txt: str): st.caption(f"ℹ️ {txt}")

def code_and_download(smt: str, fname: str, status: str, model: str, raw: str):
    st.subheader("Output Z3")
    st.write(f"**Status:** `{status}`")
    if status == "sat" and model.strip():
        st.code(model, language="lisp")
    elif raw.strip():
        st.code(raw, language="text")
    st.subheader("SMT-LIB v2 generato")
    st.code(smt, language="lisp")
    st.download_button("⬇️ Scarica .smt2", smt, file_name=fname, mime="text/plain")

# ============ 1) BUILDER ============
if mode.startswith("Builder"):
    st.subheader("Builder visuale di formule annidate")
    help_info("Costruisci formule complesse selezionando sotto-formule e inglobandole in un operatore. Sintassi SMT-LIB v2 garantita.")

    vars_line = st.text_input("Variabili booleane (spazio-separate)", value="p q r s",
                              help="Saranno dichiarate come Bool in SMT-LIB.")
    vars_ = [v for v in vars_line.split() if v]

    # Stato builder
    if "pool" not in st.session_state: st.session_state.pool: List[Expr] = vars_.copy()
    if "phi_idx" not in st.session_state: st.session_state.phi_idx = None

    colL, colR = st.columns([1,1])
    with colL:
        st.markdown("**Sotto-formule disponibili**")
        if st.button("🔁 Resetta pool alle variabili"):
            st.session_state.pool = vars_.copy(); st.session_state.phi_idx = None
        for i, e in enumerate(st.session_state.pool):
            pretty = emit_expr(e) if isinstance(e, Node) else e
            st.write(f"[{i}] {pretty}")

        st.divider()
        st.markdown("**Crea nuova sotto-formula**")
        select_ids = st.multiselect("Indici da inglobare", options=list(range(len(st.session_state.pool))),
                                    help="NOT richiede 1; AND/OR ≥2; IMPLIES/IFF/XOR esattamente 2.")
        op = st.selectbox("Operatore", ["Not","And","Or","Implies","Iff","Xor"],
                          help="XOR è lo XOR booleano standard SMT-LIB.")
        if st.button("➕ Ingloba"):
            if not select_ids:
                st.warning("Seleziona almeno una sotto-formula.")
            else:
                items = [st.session_state.pool[i] for i in select_ids]
                try:
                    if op=="Not" and len(items)==1: newf = Not(items[0])
                    elif op=="And" and len(items)>=2: newf = And(*items)
                    elif op=="Or" and len(items)>=2: newf = Or(*items)
                    elif op=="Implies" and len(items)==2: newf = Implies(items[0], items[1])
                    elif op=="Iff" and len(items)==2: newf = Iff(items[0], items[1])
                    elif op=="Xor" and len(items)==2: newf = Xor(items[0], items[1])
                    else: st.warning("Cardinalità argomenti non corretta per l’operatore scelto."); raise ValueError
                    st.session_state.pool.append(newf)
                    st.success(f"Nuova sotto-formula: indice {len(st.session_state.pool)-1}")
                except Exception: pass

        phi_pick = st.number_input("Indice formula principale Φ", min_value=0,
                                   max_value=max(0, len(st.session_state.pool)-1),
                                   value=(st.session_state.phi_idx or 0))
        if st.button("✅ Imposta Φ"): st.session_state.phi_idx = int(phi_pick)

    with colR:
        st.markdown("**Anteprima Φ (SMT-LIB)**")
        if st.session_state.phi_idx is not None and st.session_state.phi_idx < len(st.session_state.pool):
            phi = st.session_state.pool[st.session_state.phi_idx]
            phi_smt = emit_expr(phi)
            st.code(phi_smt, language="lisp")
        else:
            st.info("Imposta Φ per proseguire.")

        st.markdown("---")
        st.markdown("**Task su Φ**")
        task = st.selectbox("Seleziona task",
                            ["Tautologia (assert (not Φ))", "SAT (assert Φ)", "Equivalenza (Φ = Ψ)", "Inferenza (Premesse ⊢ Φ)"],
                            help="La GUI genera SMT-LIB v2 “stile prof”.")
        getm = st.checkbox("Richiedi modello (solo se SAT)", value=True)

        extras = ""
        if task == "Equivalenza (Φ = Ψ)":
            psi_str = st.text_input("Ψ (DSL: And/Or/Not/Implies/Iff/Xor)", value="Implies(p,q)")
            env = {v: Var(v) for v in vars_}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
            try:
                psi = eval(psi_str, {"__builtins__": {}}, env); psi_smt = emit_expr(psi)
                extras = psi_smt; st.caption("Anteprima Ψ (SMT-LIB):"); st.code(psi_smt, language="lisp")
            except Exception: st.warning("Ψ non valida."); psi = None
        elif task == "Inferenza (Premesse ⊢ Φ)":
            prem_txt = st.text_area("Premesse (DSL, una per riga)", height=120,
                                    placeholder="Implies(PS,PJ)\nXor(PE,PS)\nNot(PJ)")
            extras = prem_txt

        if st.button("▶️ Genera & Verifica con Z3"):
            decls = declare_block(vars_)
            if st.session_state.phi_idx is None:
                st.warning("Imposta Φ prima di procedere."); st.stop()
            phi = st.session_state.pool[st.session_state.phi_idx]; phi_smt = emit_expr(phi)
            body = []
            if task.startswith("Tautologia"): body += [assert_line(f"(not {phi_smt})")]
            elif task.startswith("SAT"): body += [assert_line(phi_smt)]
            elif task.startswith("Equivalenza"):
                if not extras: st.warning("Definisci Ψ valida."); st.stop()
                body += [assert_line(f"(not (= {phi_smt} {extras}))")]
            else:
                lines = [ln.strip() for ln in extras.splitlines() if ln.strip()]
                env = {v: Var(v) for v in vars_}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
                for ln in lines: body.append(assert_line(emit_expr(eval(ln, {"__builtins__": {}}, env))))
                body.append(assert_line(f"(not {phi_smt})"))
            smt = "\n".join([decls, "\n".join(body), check_sat()])
            status, model, raw = run_z3_safely(smt if getm else smt)
            code_and_download(smt, "builder.smt2", status, model, raw)

# ============ 2) PRESET ============
elif mode.startswith("Preset"):
    st.subheader("Template guidati (con esempi del professore)")
    tabs = st.tabs(["Tautologia","Inferenza","SAT","Equivalenza","ExactlyOne / XOR-n"])

    # ---- Tautologia
    with tabs[0]:
        colA, colB = st.columns([1,1])
        with colA:
            preset = st.selectbox("Carica esempio del professore", ["—"] + list(TEMPLATE_TAUTO.keys()))
        with colB:
            default_vars = "p q r"
            if preset != "—":
                vs = TEMPLATE_TAUTO[preset]["vars"]
                parts = TEMPLATE_TAUTO[preset]["parts"]
                st.session_state.tau_vars = " ".join(vs)
                st.session_state.tau_parts = "\n".join(parts)
        vars_line = st.text_input("Variabili", value=st.session_state.get("tau_vars", default_vars))
        vs = [v for v in vars_line.split() if v]
        lines = st.text_area("Sotto-formule (DSL una per riga)", height=120,
                             value=st.session_state.get("tau_parts","Implies(Implies(p,q),p)"))
        if st.button("▶️ Verifica Tautologia"):
            env = {v: Var(v) for v in vs}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
            parts = [eval(ln.strip(), {"__builtins__": {}}, env) for ln in lines.splitlines() if ln.strip()]
            phi = parts[0] if len(parts)==1 else And(*parts)
            smt = "\n".join([declare_block(vs), assert_line(f"(not {emit_expr(phi)})"), check_sat()])
            status, model, raw = run_z3_safely(smt)
            code_and_download(smt, "tautology.smt2", status, model, raw)

    # ---- Inferenza
    with tabs[1]:
        colA, colB = st.columns([1,1])
        with colA:
            preset = st.selectbox("Carica esempio del professore", ["—"] + list(TEMPLATE_INFER.keys()))
        if preset != "—":
            data = TEMPLATE_INFER[preset]
            st.session_state.inf_vars = " ".join(data["vars"])
            st.session_state.inf_prem = "\n".join(data["premises"])
            st.session_state.inf_conc = data["conclusion"]
        vars_line = st.text_input("Variabili", value=st.session_state.get("inf_vars","PE PS PJ"))
        vs = [v for v in vars_line.split() if v]
        prem_txt = st.text_area("Premesse (DSL una per riga)", height=130,
                                value=st.session_state.get("inf_prem","Xor(PE,PS)\nImplies(PS,PJ)\nNot(PJ)"))
        conc = st.text_input("Conclusione (DSL)", value=st.session_state.get("inf_conc","PE"))
        if st.button("▶️ Verifica Inferenza"):
            env = {v: Var(v) for v in vs}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
            body = [assert_line(emit_expr(eval(ln.strip(), {"__builtins__": {}}, env)))
                    for ln in prem_txt.splitlines() if ln.strip()]
            body.append(assert_line(f"(not {emit_expr(eval(conc, {'__builtins__': {}}, env))})"))
            smt = "\n".join([declare_block(vs), "\n".join(body), check_sat()])
            status, model, raw = run_z3_safely(smt)
            code_and_download(smt, "inference.smt2", status, model, raw)

    # ---- SAT
    with tabs[2]:
        colA, colB = st.columns([1,1])
        with colA:
            preset = st.selectbox("Carica esempio del professore", ["—"] + list(TEMPLATE_SAT.keys()))
        if preset != "—":
            data = TEMPLATE_SAT[preset]
            st.session_state.sat_vars = " ".join(data["vars"])
            st.session_state.sat_asserts = "\n".join(data["asserts"])
            st.session_state.sat_getm = data.get("get_model", True)
            st.session_state.sat_scope = data.get("scope", False)
        vars_line = st.text_input("Variabili", value=st.session_state.get("sat_vars","p q"))
        vs = [v for v in vars_line.split() if v]
        asserts = st.text_area("Assert (DSL per riga)", height=120,
                               value=st.session_state.get("sat_asserts","And(Or(p,q), Implies(p,q))"))
        getm = st.checkbox("Richiedi modello", value=st.session_state.get("sat_getm", True))
        use_scope = st.checkbox("Usa push/pop", value=st.session_state.get("sat_scope", False))
        if st.button("▶️ Verifica SAT"):
            env = {v: Var(v) for v in vs}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
            body = [assert_line(emit_expr(eval(ln.strip(), {"__builtins__": {}}, env)))
                    for ln in asserts.splitlines() if ln.strip()]
            body.append(check_sat())
            core = "\n".join(body)
            smt = "\n".join([declare_block(vs), wrap_push_pop(core) if use_scope else core])
            status, model, raw = run_z3_safely(smt if getm else smt)
            code_and_download(smt, "sat.smt2", status, model, raw)

    # ---- Equivalenza
    with tabs[3]:
        colA, colB = st.columns([1,1])
        with colA:
            preset = st.selectbox("Carica esempio del professore", ["—"] + list(TEMPLATE_EQUIV.keys()))
        if preset != "—":
            data = TEMPLATE_EQUIV[preset]
            st.session_state.eq_vars = " ".join(data["vars"])
            st.session_state.eq_f1 = data["f1"]
            st.session_state.eq_f2 = data["f2"]
        vars_line = st.text_input("Variabili", value=st.session_state.get("eq_vars","p q r"))
        vs = [v for v in vars_line.split() if v]
        f1 = st.text_input("f1 (DSL)", value=st.session_state.get("eq_f1","Implies(Or(p,q), r)"))
        f2 = st.text_input("f2 (DSL)", value=st.session_state.get("eq_f2","And(Implies(p,r), Implies(q,r))"))
        if st.button("▶️ Verifica Equivalenza"):
            env = {v: Var(v) for v in vs}; env.update({"Not":Not,"And":And,"Or":Or,"Implies":Implies,"Iff":Iff,"Xor":Xor})
            e1 = emit_expr(eval(f1, {"__builtins__": {}}, env))
            e2 = emit_expr(eval(f2, {"__builtins__": {}}, env))
            smt = "\n".join([declare_block(vs), assert_line(f"(not (= {e1} {e2}))"), check_sat()])
            status, model, raw = run_z3_safely(smt)
            code_and_download(smt, "equivalence.smt2", status, model, raw)

    # ---- ExactlyOne / XOR-n
    with tabs[4]:
        colA, colB = st.columns([1,1])
        with colA:
            preset = st.selectbox("Carica esempio", ["—"] + list(TEMPLATE_XORn.keys()))
        if preset != "—":
            data = TEMPLATE_XORn[preset]
            st.session_state.xor_vars = " ".join(data["vars"])
        vars_line = st.text_input("Variabili", value=st.session_state.get("xor_vars","a b c d"))
        xs = [v for v in vars_line.split() if v]
        if st.button("▶️ Genera & Verifica ExactlyOne"):
            decls = declare_block(xs)
            smt = "\n".join([decls, assert_line(emit_expr(ExactlyOne(*xs))), check_sat()])
            status, model, raw = run_z3_safely(smt)
            code_and_download(smt, "exactlyone.smt2", status, model, raw)

# ============ 3) COLORING K ============
elif mode.startswith("Coloring"):
    st.subheader("Coloring a K colori (builder guidato)")
    help_info("Per ogni nodo X generiamo X1..XK ∈ Bool con ExactlyOne; per ogni arco (u,v) vietiamo lo stesso colore su entrambi. (Cardinalità via PB `((_ at-most 1) ...)`).")

    colA, colB = st.columns([1,1])
    with colA:
        preset = st.selectbox("Carica esempio del professore", ["—"] + list(TEMPLATE_COLORING.keys()))
        if preset != "—":
            data = TEMPLATE_COLORING[preset]
            st.session_state.col_K = data["K"]
            st.session_state.col_nodes = data["nodes"]
            st.session_state.col_edges = data["edges"]
    with colB:
        pass

    K = st.number_input("K (colori)", min_value=2, max_value=10, value=st.session_state.get("col_K",3))
    nodes_line = st.text_input("Nodi (spazio-separati)",
                               value=st.session_state.get("col_nodes","Bel Gua ElS Hon Nic CR Pan"))
    edges_text = st.text_area("Archi u,v (uno per riga)", height=140,
                              value=st.session_state.get("col_edges","Bel,Gua\nElS,Hon\nElS,Gua\nGua,Hon\nNic,Hon\nNic,CR\nNic,Pan"))
    ask_model = st.checkbox("Mostra un modello (se SAT)", value=True)

    if st.button("▶️ Genera SMT-LIB + Verifica"):
        nodes = [n.strip() for n in nodes_line.split() if n.strip()]
        # validazioni base
        errs = []
        if len(set(nodes)) != len(nodes): errs.append("Nodi duplicati.")
        bad_edges = []
        edges = []
        for ln in edges_text.splitlines():
            if not ln.strip(): continue
            if "," not in ln: bad_edges.append(ln); continue
            u,v = [t.strip() for t in ln.split(",",1)]
            if u not in nodes or v not in nodes: bad_edges.append(ln); continue
            if u==v: bad_edges.append(ln); continue
            edges.append((u,v))
        if bad_edges: st.error("Archi mal formati o riferiti a nodi inesistenti: " + ", ".join(bad_edges)); st.stop()

        # SMT-LIB
        lines = ["; K-coloring","; nodes & ExactlyOne"]
        for n in nodes:
            decls = [f"(declare-const {n}{c} Bool)" for c in range(1,K+1)]
            lines += decls
            xs = [f"{n}{c}" for c in range(1,K+1)]
            lines.append(assert_line(emit_expr(ExactlyOne(*xs))))
            lines.append("")
        lines.append("; edges constraints")
        for (u,v) in edges:
            for c in range(1,K+1):
                lines.append(assert_line(f"(not (and {u}{c} {v}{c}))"))
        lines.append(check_sat())
        smt = "\n".join(lines)
        status, model, raw = run_z3_safely(smt if ask_model else smt)

        # Riassunto modello (solo il colore vero per nodo)
        if status=="sat" and model:
            summary = []
            for n in nodes:
                chosen = None
                for c in range(1,K+1):
                    token = f"(define-fun {n}{c} () Bool\n    true)"
                    if token in model:
                        chosen = c; break
                summary.append(f"{n} → colore {chosen if chosen else '?'}")
            st.markdown("**Assegnazione colori (dal modello):**")
            st.code("\n".join(summary), language="text")

        code_and_download(smt, "coloringK.smt2", status, model, raw)

# ============ 4) TESTER ============
else:
    st.subheader("Tester veloce SMT-LIB")
    help_info("Incolla SMT-LIB già pronto (o generato qui) e verifica. Il modello viene richiesto *solo se* `sat`.")
    smt = st.text_area("SMT-LIB", height=220, placeholder="(declare-const p Bool)\n(assert p)\n(check-sat)")
    if st.button("▶️ Verifica"):
        status, model, raw = run_z3_safely(smt)
        code_and_download(smt, "manual.smt2", status, model, raw)
