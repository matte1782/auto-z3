# app_fol.py — UI Streamlit FOL (quantificatori) + grafico
import re
from typing import Dict

import streamlit as st

from fol_core import Exists, ForAll, build_smt2_universe, make_env
from z3_runner import run_z3_safely

st.set_page_config(page_title="Auto-Z3 — FOL (Quantificatori)", layout="wide")
st.title("Auto-Z3 — FOL (First-Order Logic)")

st.caption(
    "Guidato, semplice: dominio finito, simboli, fatti, quantificatori. "
    "Per risultati deterministici usa **Espansione su dominio finito** (consigliata)."
)

# --- Stato
if "preds" not in st.session_state:
    st.session_state.preds: Dict[str, int] = {}
if "funs" not in st.session_state:
    st.session_state.funs: Dict[str, int] = {}

# --- Colonne macro
colL, colR = st.columns([1.1, 1])

with colL:
    st.subheader("1) Dominio, Predicati, Funzioni")
    dom_line = st.text_input("Costanti del dominio (spazio-separate)", value="a b c")
    consts = [c for c in dom_line.split() if c]

    with st.expander("Predicati (nome / arità)", expanded=True):
        c1, c2, c3 = st.columns([1.2, 0.6, 0.6])
        pname = c1.text_input("Nome predicato", placeholder="P")
        parity = c2.number_input("Arità", min_value=0, max_value=4, step=1, value=2)
        addp = c3.button("➕ Aggiungi")
        if addp and pname:
            st.session_state.preds[pname] = int(parity)
        # elenco
        for nm, ar in list(st.session_state.preds.items()):
            st.text_input(
                f"{nm}/{ar}",
                value=f"{nm} : {ar}",
                key=f"pred_{nm}",
                disabled=True,
                label_visibility="collapsed",
            )
            if st.button(f"🗑️ Rimuovi {nm}", key=f"delp_{nm}"):
                st.session_state.preds.pop(nm, None)

    with st.expander("Funzioni (nome / arità)", expanded=False):
        c1, c2, c3 = st.columns([1.2, 0.6, 0.6])
        fname = c1.text_input("Nome funzione", placeholder="f")
        farity = c2.number_input("Arità ", min_value=0, max_value=4, step=1, value=1)
        addf = c3.button("➕ Aggiungi", key="addf")
        if addf and fname:
            st.session_state.funs[fname] = int(farity)
        for nm, ar in list(st.session_state.funs.items()):
            st.text_input(
                f"{nm}/{ar}",
                value=f"{nm} : {ar}",
                key=f"fun_{nm}",
                disabled=True,
                label_visibility="collapsed",
            )
            if st.button(f"🗑️ Rimuovi {nm}", key=f"delf_{nm}"):
                st.session_state.funs.pop(nm, None)

    st.subheader("2) Fatti (ground) — opzionali")
    facts_text = st.text_area(
        "Un fatto per riga (es.: P(a,b), Eq(f(a),b), a=b)",
        height=110,
        placeholder="Human(a)\nLoves(a,b)\nEq(f(a), a)",
    )
    facts = [ln.strip() for ln in facts_text.splitlines() if ln.strip()]

with colR:
    st.subheader("3) Formula con quantificatori")
    qmode = st.selectbox(
        "Selettore",
        ["SAT (assiomi + formula)", "Validità (tautologia)", "Conseguenza logica (⊢)"],
    )
    use_ground = st.checkbox(
        "Espansione su dominio finito (consigliata)",
        value=True,
        help="Sostituisce i quantificatori con AND/OR su tutte le costanti del dominio.",
    )
    ask_model = st.checkbox("Richiedi modello (solo se SAT)", value=True)

    st.markdown("**Quantificatori & DSL**")
    st.caption(
        "Scrivi variabili (spazio-separate), poi la formula interna in DSL. "
        "Predicati/funzioni sono chiamabili come in matematica: `P(x,y)`, `f(x)`. "
        "Operatori: `Not, And, Or, Implies, Iff, Eq`."
    )
    vars_line = st.text_input("Variabili quantificate (es.: x y)", value="x y")
    qvars = [v for v in vars_line.split() if v]
    qtype = st.selectbox(
        "Tipo quantificatore", ["∀ ForAll", "∃ Exists", "Nessuno (formula ground)"]
    )
    inner_str = st.text_input(
        "Formula interna (DSL)",
        value="Implies(P(x,y), P(y,x))",
        help="Esempi: P(x), And(P(x), Q(y)), Implies(Eq(f(x),y), R(y))",
    )

    # goal per conseguenza
    goal_str = ""
    if qmode.startswith("Conseguenza"):
        goal_str = st.text_input(
            "Conclusione (DSL, stessa sintassi)",
            value="Exists([x], P(x,x))".replace("[", "").replace("]", ""),
            help="Puoi anche usare ForAll/Exists combinati in DSL, o formula ground.",
        )

    # Prepara env DSL
    env = make_env(st.session_state.preds, st.session_state.funs, consts, qvars)

    # Costruisci formula dall'input DSL
    def parse_formula(expr: str):
        return eval(expr, {"__builtins__": {}}, env)

    # Applica quantificatore esterno se richiesto
    def wrap_quantifier(phi):
        if qtype.startswith("∀"):
            return ForAll(qvars, phi) if qvars else phi
        if qtype.startswith("∃"):
            return Exists(qvars, phi) if qvars else phi
        return phi

    st.markdown("---")
    if st.button("▶️ Genera SMT-LIB + Verifica"):
        try:
            base = parse_formula(inner_str)
            main_phi = wrap_quantifier(base)

            smt_task = (
                "sat"
                if qmode.startswith("SAT")
                else ("validity" if qmode.startswith("Validità") else "inference")
            )
            formulas = [main_phi] if smt_task != "inference" else []
            goal = None
            if smt_task == "inference":
                goal = parse_formula(goal_str)

            smt = build_smt2_universe(
                domain_consts=consts,
                predicates=st.session_state.preds,
                functions=st.session_state.funs,
                facts=facts,
                formulas=formulas,
                task=smt_task,
                inference_goal=goal,
                use_grounding=use_ground,
            )

            status, model, raw = run_z3_safely(smt, request_model=ask_model)
            # Output
            st.subheader("Verifica")
            badge = {
                "sat": "✅ SAT",
                "unsat": "🧱 UNSAT",
                "unknown": "❔ UNKNOWN",
                "error": "⚠️ ERROR",
            }.get(status, status)
            st.markdown(f"**Stato:** {badge}")
            if status == "sat" and model.strip():
                st.markdown("**Modello (estratto):**")
                st.code(model, language="lisp")
            else:
                st.code(raw.strip(), language="text")
            st.subheader("SMT-LIB v2 generato")
            st.code(smt, language="lisp")
            st.download_button("⬇️ Scarica .smt2", smt, file_name="fol.smt2", mime="text/plain")

        except Exception as ex:
            st.error(f"Errore nella DSL o nei parametri: {ex}")

st.markdown("---")
st.subheader("4) Visualizza un predicato binario come grafo (dai fatti)")
st.caption(
    "Se hai scritto fatti ground come `Edge(a,b)` o `Loves(a,b)`, seleziona il predicato per vedere il grafo."
)
picks = [k for k, v in (st.session_state.preds or {}).items() if v == 2]
if picks:
    pname = st.selectbox("Predicato binario", picks)
    edges = []
    for ln in (ln.strip() for ln in st.session_state.get("facts_cache", []) + []):
        # (non usata; manteniamo compatibilità futura)
        pass
    # Estrai coppie direttamente dai fatti_text (più semplice/robusto)
    raw_lines = st.session_state.get("facts_raw_cache") or None
else:
    pname = None

# aggiorna cache raw
st.session_state["facts_raw_cache"] = (
    facts_text.splitlines() if "facts_text" else facts_text.splitlines()
)

if pname:
    pairs = []
    pat = re.compile(
        rf"^\s*{re.escape(pname)}\s*\(\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*\)\s*$"
    )
    for ln in facts:
        m = pat.match(ln)
        if m:
            pairs.append((m.group(1), m.group(2)))

    if pairs:
        dot = "digraph G {\n" + "\n".join(f'  "{u}" -> "{v}";' for u, v in pairs) + "\n}"
        st.graphviz_chart(dot)
    else:
        st.info("Nessuna coppia trovata nei fatti per questo predicato.")
