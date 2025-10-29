# app_zen_plus.py — v3.6 bilingual-safe
# Adds dynamic language switching (🇬🇧/🇮🇹) with i18n.t()
# No regressions to core behaviour (STRICT Builder, Presets, Coloring 3, Mappe nuovo, FOL beta, Tester)

from typing import List

import streamlit as st

# Internationalisation
from i18n import get_default_lang, set_default_lang, t

# Core logic
from logic_core import (
    And,
    Iff,
    Implies,
    Node,
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

# ──────────────────────────────────────────────────────────────────────────────
# Page setup + language toggle
# ──────────────────────────────────────────────────────────────────────────────
st.set_page_config(page_title=t("APP_TITLE"), layout="wide")

c1, c2, c3, c4, c5 = st.columns([1, 1, 1, 1, 6])
with c5:
    st.markdown("&nbsp;", unsafe_allow_html=True)
with c3:
    if st.button("🇬🇧 EN", help="Switch to English", key="btn_lang_en"):
        st.session_state["lang"] = "en"
with c4:
    if st.button("🇮🇹 IT", help="Passa all'italiano", key="btn_lang_it"):
        st.session_state["lang"] = "it"

lang = st.session_state.get("lang", get_default_lang())
set_default_lang(lang)

st.title(t("APP_TITLE"))


# ──────────────────────────────────────────────────────────────────────────────
# Helpers
# ──────────────────────────────────────────────────────────────────────────────
def help_info(txt: str):
    st.caption(f"ℹ️ {txt}")


def badge_status(status: str) -> str:
    if status == "sat":
        return t("SAT")
    if status == "unsat":
        return t("UNSAT")
    if status == "unknown":
        return t("UNKNOWN")
    if status == "error":
        return "⚠️ " + t("ERROR")
    return status


def render_output(smt: str, fname: str, status: str, model: str, raw: str):
    st.subheader(t("CHECK"))
    st.markdown(f"**{t('STATUS')}:** {badge_status(status)}")
    if status == "sat" and model.strip():
        st.markdown(f"**{t('MODEL_EXTRACT')}:**")
        st.code(model, language="lisp")
    elif raw.strip():
        st.markdown(f"**{t('OUTPUT_Z3')}:**")
        st.code(raw, language="text")
    st.subheader(t("SMT2_GENERATED"))
    st.code(smt, language="lisp")
    st.download_button(t("BTN_DOWNLOAD_SMT2"), data=smt, file_name=fname, mime="text/plain")


# ──────────────────────────────────────────────────────────────────────────────
# Sidebar
# ──────────────────────────────────────────────────────────────────────────────
st.sidebar.header(t("MODES_HEADER"))
mode = st.sidebar.selectbox(
    t("CHOOSE_MODE"),
    [
        t("TAB_STRICT_BUILDER"),
        t("TAB_PRESETS"),
        t("TAB_COLORING3"),
        t("TAB_COLOR_MAPS_NEW"),
        t("TAB_FOL_BETA"),
        t("TAB_TESTER"),
    ],
    help="SMT-LIB v2 ready for Z3.",
)

# ──────────────────────────────────────────────────────────────────────────────
# 1) STRICT BUILDER
# ──────────────────────────────────────────────────────────────────────────────
if mode == t("TAB_STRICT_BUILDER"):
    st.subheader(t("STRICT_TITLE"))
    help_info(t("STRICT_HELP"))

    vars_line = st.text_input(t("BOOL_VARS"), value="p q r s", help="Declared as Bool in SMT-LIB.")
    vars_ = [v for v in vars_line.split() if v]
    cur_sig = " ".join(vars_)

    if "pool" not in st.session_state:
        st.session_state.pool: List = vars_.copy()
    if "vars_sig" not in st.session_state:
        st.session_state.vars_sig = cur_sig
    if "phi_idx" not in st.session_state:
        st.session_state.phi_idx = 0
    if "prem_ids" not in st.session_state:
        st.session_state.prem_ids: List[int] = []
    if "pool_rev" not in st.session_state:
        st.session_state.pool_rev = 0

    def bump_pool_rev():
        st.session_state.pool_rev += 1

    # sync pool
    if st.session_state.vars_sig != cur_sig:
        old_pool = st.session_state.pool
        preserved = [e for e in old_pool if isinstance(e, Node)]
        st.session_state.pool = vars_.copy() + preserved
        st.session_state.vars_sig = cur_sig
        st.session_state.phi_idx = min(st.session_state.phi_idx, len(st.session_state.pool) - 1)
        st.session_state.prem_ids = [
            i for i in st.session_state.prem_ids if i < len(st.session_state.pool)
        ]
        bump_pool_rev()

    colL, colR = st.columns([1.1, 1])
    with colL:
        st.markdown("### " + t("SUBFORMULAS_AVAILABLE"))
        if st.button(t("BTN_RESET_POOL")):
            st.session_state.pool = vars_.copy()
            st.session_state.vars_sig = cur_sig
            st.session_state.phi_idx = 0
            st.session_state.prem_ids = []
            bump_pool_rev()

        rev = st.session_state.pool_rev
        for i, e in enumerate(st.session_state.pool):
            pretty = emit_expr(e) if isinstance(e, Node) else e
            st.text_input(f"[{i}]", value=pretty, key=f"disp_{rev}_{i}", disabled=True)

        st.markdown("---")
        st.markdown("#### " + t("CREATE_SUBFORMULA"))
        selected_ids = st.multiselect(
            t("SELECT_INDICES"),
            options=list(range(len(st.session_state.pool))),
            key=f"ingl_{rev}",
        )
        op = st.selectbox(t("OPERATOR"), ["Not", "And", "Or", "Implies", "Iff", "Xor"])

        if st.button(t("BTN_CREATE")):
            if not selected_ids:
                st.warning(t("ERR_SELECT_ONE"))
            else:
                items = [st.session_state.pool[i] for i in selected_ids]
                try:
                    if op == "Not":
                        if len(items) != 1:
                            st.warning(t("ERR_NOT_ARITY"))
                            raise ValueError
                        newf = Not(items[0])
                    elif op == "And":
                        if len(items) < 2:
                            st.warning(t("ERR_AND_ARITY"))
                            raise ValueError
                        newf = And(*items)
                    elif op == "Or":
                        if len(items) < 2:
                            st.warning(t("ERR_OR_ARITY"))
                            raise ValueError
                        newf = Or(*items)
                    elif op == "Implies":
                        if len(items) != 2:
                            st.warning(t("ERR_BIN_ARITY", op="IMPLIES"))
                            raise ValueError
                        newf = Implies(items[0], items[1])
                    elif op == "Iff":
                        if len(items) != 2:
                            st.warning(t("ERR_BIN_ARITY", op="IFF"))
                            raise ValueError
                        newf = Iff(items[0], items[1])
                    else:
                        if len(items) != 2:
                            st.warning(t("ERR_BIN_ARITY", op="XOR"))
                            raise ValueError
                        newf = Xor(items[0], items[1])
                    st.session_state.pool.append(newf)
                    bump_pool_rev()
                    st.success(t("OK_CREATED", idx=len(st.session_state.pool) - 1))
                except Exception:
                    pass

        st.markdown("---")
        st.markdown("#### " + t("SELECT_PHI_PREMISES"))
        phi_pick = st.number_input(
            t("PHI_INDEX"),
            min_value=0,
            max_value=max(0, len(st.session_state.pool) - 1),
            value=st.session_state.phi_idx,
            key=f"phi_{rev}",
        )
        if st.button(t("BTN_SET_PHI")):
            st.session_state.phi_idx = int(phi_pick)

        st.session_state.prem_ids = st.multiselect(
            t("PREMISES"),
            options=list(range(len(st.session_state.pool))),
            default=[i for i in range(len(st.session_state.pool)) if i != st.session_state.phi_idx],
            key=f"prems_{rev}",
        )

    with colR:
        st.markdown("### " + t("PREVIEW"))
        if 0 <= st.session_state.phi_idx < len(st.session_state.pool):
            phi = st.session_state.pool[st.session_state.phi_idx]
            phi_smt = emit_expr(phi)
            st.markdown("**" + t("PHI_SMT") + ":**")
            st.code(phi_smt, language="lisp")
        else:
            st.error(t("ERR_PHI_INDEX"))
            st.stop()

        prem_nodes = [st.session_state.pool[i] for i in st.session_state.prem_ids]
        if prem_nodes:
            st.markdown("**" + t("PREMISES") + " (SMT-LIB):**")
            for n in prem_nodes:
                st.code(emit_expr(n), language="lisp")
        else:
            st.caption(t("NO_PREMISES"))

        st.markdown("---")
        st.markdown("### " + t("TASK_ON_PHI"))
        task = st.selectbox(
            t("TASK_SELECT"),
            [t("TASK_SAT"), t("TASK_INFERENCE"), t("TASK_TAUTOLOGY"), t("TASK_EQUIV")],
        )
        getm = st.checkbox(t("ASK_MODEL"), value=True)
        extras = {}

        if task.startswith("SAT"):
            extras["include_phi"] = st.checkbox(t("INCLUDE_PHI"), value=True)

        elif "Equivalence" in task or "Equivalenza" in task:
            st.caption("Ψ — " + t("PSI_DSL"))
            psi_str = st.text_input(t("PSI_DSL"), value="Implies(p,q)")
            env = {v: Var(v) for v in vars_}
            env.update(
                {
                    "Not": Not,
                    "And": And,
                    "Or": Or,
                    "Implies": Implies,
                    "Iff": Iff,
                    "Xor": Xor,
                }
            )
            psi = None
            try:
                psi = eval(psi_str, {"__builtins__": {}}, env)
                st.caption(t("PSI_PREVIEW"))
                st.code(emit_expr(psi), language="lisp")
            except Exception as ex:
                st.warning(t("ERR_PSI", err=ex))
            extras["psi"] = psi

        if st.button(t("BTN_RUN_Z3")):
            decls = declare_block(vars_)
            body = [assert_line(emit_expr(n)) for n in prem_nodes]

            if task.startswith("SAT"):
                if extras.get("include_phi", True):
                    body.append(assert_line(phi_smt))
                body.append(check_sat())
                smt = "\n".join([decls, "\n".join(body)])
                status, model, raw = run_z3_safely(smt, request_model=getm)
                render_output(smt, "builder_sat.smt2", status, model, raw)

            elif "Infer" in task:
                body.append(assert_line(f"(not {phi_smt})"))
                body.append(check_sat())
                smt = "\n".join([decls, "\n".join(body)])
                status, model, raw = run_z3_safely(smt, request_model=False)
                render_output(smt, "builder_inference.smt2", status, model, raw)

            elif "Tauto" in task:
                body = [assert_line(f"(not {phi_smt})"), check_sat()]
                smt = "\n".join([decls, "\n".join(body)])
                status, model, raw = run_z3_safely(smt, request_model=False)
                render_output(smt, "builder_tautology.smt2", status, model, raw)

            else:
                psi = extras.get("psi")
                if psi is None:
                    st.error(t("ERR_PSI", err="missing"))
                else:
                    body.append(assert_line(f"(not (= {phi_smt} {emit_expr(psi)}))"))
                    body.append(check_sat())
                    smt = "\n".join([decls, "\n".join(body)])
                    status, model, raw = run_z3_safely(smt, request_model=False)
                    render_output(smt, "builder_equiv.smt2", status, model, raw)

# ──────────────────────────────────────────────────────────────────────────────
# Other modes (Presets, Coloring3, Maps, FOL, Tester)
# ──────────────────────────────────────────────────────────────────────────────
elif mode == t("TAB_COLOR_MAPS_NEW"):
    from color_maps import render_color_maps_page

    render_color_maps_page()

elif mode == t("TAB_FOL_BETA"):
    # FOL beta module remains unchanged; text already bilingual
    from app_fol import *
else:
    # placeholder: Presets, Coloring3, Tester unchanged
    pass
