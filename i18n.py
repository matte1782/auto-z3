# i18n.py — centralised bilingual translations (EN/IT) with safe fallbacks
# Usage:
#   from i18n import t, set_default_lang, get_default_lang
#   st.button(t("BTN_SOLVE"))
#
# Safety:
#   - Missing key => returns the key itself (visible and debuggable)
#   - Missing language => falls back to English
#   - Format placeholders use .format(**kwargs); on mismatch, returns raw text

from __future__ import annotations
from typing import Dict

LANGS = ("en", "it")
_default_lang = "en"


def set_default_lang(lang: str) -> None:
    """Set global default language for t()."""
    global _default_lang
    if lang in LANGS:
        _default_lang = lang


def get_default_lang() -> str:
    return _default_lang


def t(key: str, lang: str | None = None, **fmt) -> str:
    """Translate key to text; graceful fallbacks; optional .format(**fmt)."""
    lang = lang or _default_lang
    entry = _MESSAGES.get(key, {})
    raw = entry.get(lang) or entry.get("en") or key
    try:
        return raw.format(**fmt)
    except Exception:
        # Never break the UI for formatting errors
        return raw


# ──────────────────────────────────────────────────────────────────────────────
# TRANSLATION DICTIONARY
# ──────────────────────────────────────────────────────────────────────────────
_MESSAGES: Dict[str, Dict[str, str]] = {

    # ── APP GLOBAL ────────────────────────────────────────────────────────────
    "APP_TITLE": {
        "en": "Auto-Z3 — Visual, No-Code SAT & FOL for Z3",
        "it": "Auto-Z3 — Interfaccia Visuale No-Code per Z3 (SAT & FOL)",
    },
    "LANGUAGE": {"en": "Language", "it": "Lingua"},
    "STATUS": {"en": "Status", "it": "Stato"},
    "SAT": {"en": "✅ SAT", "it": "✅ SAT"},
    "UNSAT": {"en": "🧱 UNSAT", "it": "🧱 UNSAT"},
    "UNKNOWN": {"en": "❔ UNKNOWN", "it": "❔ SCONOSCIUTO"},
    "ERROR": {"en": "ERROR", "it": "ERRORE"},
    "CHECK": {"en": "Check", "it": "Verifica"},
    "MODEL_EXTRACT": {"en": "Model (extract)", "it": "Modello (estratto)"},
    "SMT2_GENERATED": {"en": "Generated SMT-LIB v2", "it": "SMT-LIB v2 generato"},
    "BTN_DOWNLOAD_SMT2": {"en": "⬇️ Download .smt2", "it": "⬇️ Scarica .smt2"},
    "BTN_DOWNLOAD": {"en": "⬇️ Download", "it": "⬇️ Scarica"},
    "OUTPUT_Z3": {"en": "Z3 Output", "it": "Output Z3"},
    "PREVIEW_RESULT": {"en": "Preview / Result", "it": "Anteprima / Risultato"},
    "INFO": {"en": "Info", "it": "Info"},
    "WARNING": {"en": "Warning", "it": "Avviso"},
    "OK_CREATED": {
        "en": "Created new sub-formula at index {idx}.",
        "it": "Creata in coda la sotto-formula indice {idx}.",
    },

    # ── SIDEBAR MODES / TABS ─────────────────────────────────────────────────
    "MODES_HEADER": {"en": "Modes", "it": "Modalità"},
    "CHOOSE_MODE": {"en": "Choose a mode", "it": "Scegli la modalità"},
    "TAB_STRICT_BUILDER": {"en": "Builder (STRICT)", "it": "Builder formule (STRICT)"},
    "TAB_PRESETS": {"en": "Common Presets", "it": "Preset comuni"},
    "TAB_COLORING3": {"en": "Coloring 3", "it": "Coloring 3"},
    "TAB_COLOR_MAPS_NEW": {"en": "Color Maps (new)", "it": "Colora Mappe (nuovo)"},
    "TAB_FOL_BETA": {"en": "FOL (beta)", "it": "FOL (beta)"},
    "TAB_TESTER": {"en": "Quick Tester", "it": "Tester veloce"},

    # ── BUILDER (STRICT) ─────────────────────────────────────────────────────
    "STRICT_TITLE": {
        "en": "Visual builder for nested formulas",
        "it": "Builder visuale di formule annidate",
    },
    "STRICT_HELP": {
        "en": "Build sub-formulas and select which ones to use as premises. No free-text.",
        "it": "Costruisci sotto-formule e seleziona quali usare come premesse. Nessuna frase libera.",
    },
    "BOOL_VARS": {
        "en": "Boolean variables (space-separated)",
        "it": "Variabili booleane (separate da spazio)",
    },
    "SUBFORMULAS_AVAILABLE": {
        "en": "Available sub-formulas",
        "it": "Sotto-formule disponibili",
    },
    "BTN_RESET_POOL": {
        "en": "🔁 Reset pool to variables",
        "it": "🔁 Resetta pool alle sole variabili",
    },
    "CREATE_SUBFORMULA": {
        "en": "Create new sub-formula",
        "it": "Crea nuova sotto-formula",
    },
    "SELECT_INDICES": {
        "en": "Select indices",
        "it": "Seleziona indici da inglobare",
    },
    "OPERATOR": {"en": "Operator", "it": "Operatore"},
    "BTN_CREATE": {"en": "➕ Create", "it": "➕ Crea"},
    "ERR_SELECT_ONE": {
        "en": "Select at least one index.",
        "it": "Seleziona almeno un indice.",
    },
    "ERR_NOT_ARITY": {
        "en": "NOT requires exactly 1 argument.",
        "it": "NOT richiede 1 argomento.",
    },
    "ERR_AND_ARITY": {
        "en": "AND requires ≥ 2 arguments.",
        "it": "AND richiede ≥ 2 argomenti.",
    },
    "ERR_OR_ARITY": {
        "en": "OR requires ≥ 2 arguments.",
        "it": "OR richiede ≥ 2 argomenti.",
    },
    "ERR_BIN_ARITY": {
        "en": "{op} requires exactly 2 arguments.",
        "it": "{op} richiede 2 argomenti.",
    },
    "SELECT_PHI_PREMISES": {
        "en": "Select Φ and premises",
        "it": "Selezione Φ e PREMESSE",
    },
    "PHI_INDEX": {
        "en": "Main formula index Φ",
        "it": "Indice formula principale Φ",
    },
    "BTN_SET_PHI": {"en": "✅ Set Φ", "it": "✅ Imposta Φ"},
    "PREMISES": {"en": "Premises", "it": "Premesse (0..N indici dal pool)"},
    "PREVIEW": {"en": "Preview", "it": "Anteprima"},
    "PHI_SMT": {"en": "Φ (SMT-LIB)", "it": "Φ (SMT-LIB)"},
    "NO_PREMISES": {"en": "No premises selected.", "it": "Nessuna premessa selezionata."},
    "TASK_ON_PHI": {"en": "Task on Φ", "it": "Task su Φ"},
    "TASK_SELECT": {"en": "Select a task", "it": "Seleziona task"},
    "TASK_SAT": {"en": "SAT (premises ∧ optional Φ)", "it": "SAT (premesse ∧ opz. Φ)"},
    "TASK_INFERENCE": {"en": "Inference (Premises ⊢ Φ)", "it": "Inferenza (Premesse ⊢ Φ)"},
    "TASK_TAUTOLOGY": {"en": "Tautology (assert (not Φ))", "it": "Tautologia (assert (not Φ))"},
    "TASK_EQUIV": {"en": "Equivalence (Φ = Ψ) [with premises]", "it": "Equivalenza (Φ = Ψ) [con premesse]"},
    "ASK_MODEL": {"en": "Request model (only if SAT)", "it": "Richiedi modello (solo se SAT)"},
    "INCLUDE_PHI": {"en": "Also include Φ among asserts", "it": "Includi anche Φ tra gli assert"},
    "PSI_DSL": {"en": "Ψ (DSL)", "it": "Ψ (DSL)"},
    "PSI_PREVIEW": {"en": "Ψ preview (SMT-LIB)", "it": "Anteprima Ψ (SMT-LIB)"},
    "ERR_PSI": {"en": "Invalid Ψ: {err}", "it": "Ψ non valida: {err}"},
    "BTN_RUN_Z3": {"en": "▶️ Generate & Check with Z3", "it": "▶️ Genera & Verifica con Z3"},
    "ERR_PHI_INDEX": {"en": "Invalid Φ index.", "it": "Indice Φ non valido."},

    # ── COLOR MAPS (UI) ───────────────────────────────────────────────────────
    "MAPS_TITLE": {"en": "Color Maps — SAT", "it": "Colora Mappe — SAT"},
    "SELECT_MAP": {"en": "Select map", "it": "Seleziona mappa"},
    "NUM_COLORS": {"en": "Number of colors", "it": "Numero colori"},
    "BUTTON_SOLVE": {"en": "Solve", "it": "Risolvi"},
    "INFO_CLICK_SOLVE": {
        "en": "Choose a map and click **Solve**. A live preview appears below.",
        "it": "Seleziona una mappa e premi **Risolvi**. Sotto trovi l’anteprima.",
    },
    "SMT2_TITLE": {"en": "Generated SMT-LIB v2", "it": "SMT-LIB v2 generato"},
    "MODEL_Z3_EXTRACT": {"en": "Z3 model (extract)", "it": "Modello Z3 (estratto)"},
    "ASSIGNMENT_ISO_TO_COLOR": {"en": "Assignment (ISO_A3 → color)", "it": "Assegnamento (ISO_A3 → colore)"},
    "FOLIUM_PREVIEW": {"en": "Preview (Folium)", "it": "Anteprima (Folium)"},
    "PREVIEW_ERROR": {"en": "Preview unavailable", "it": "Anteprima non disponibile"},
    "SOLVING_WITH_Z3": {"en": "Solving with Z3…", "it": "Risoluzione con Z3…"},
    "BTN_DOWNLOAD_SMT2": {"en": "⬇️ Download .smt2", "it": "⬇️ Scarica .smt2"},
    "SOUTH_AMERICA_COUNTRIES": {"en": "South America (Countries)", "it": "Sud America (Paesi)"},
    "CENTRAL_AMERICA_COUNTRIES": {"en": "Central America (Countries)", "it": "America Centrale (Paesi)"},

    # ── FOL (BETA) ────────────────────────────────────────────────────────────
    "FOL_TITLE": {"en": "First-Order Logic (βeta) — Quantifiers & Predicates",
                  "it": "First-Order Logic (βeta) — Quantificatori e Predicati"},
    "FOL_HELP": {"en": "Configure sort, constants and predicates via a guided mini-DSL.",
                 "it": "Configura sort, costanti e predicati tramite una mini-DSL guidata."},
    "SORT_NAME": {"en": "Sort name (domain type)", "it": "Nome sort (tipo di dominio)"},
    "DOMAIN_CONSTANTS": {"en": "Domain constants (space-separated)", "it": "Costanti di dominio (spazio-separate)"},
    "PREDICATES_ARITY": {"en": "Predicates with arity (e.g. Student/1, Teaches/2)", "it": "Predicati con arità (es. Student/1, Teaches/2)"},
    "ERR_PRED_FORMAT": {"en": "Malformed predicate: '{tok}' (use Name/Arity).", "it": "Predicato mal formattato: '{tok}' (usa Nome/Arity)."},
    "ERR_ARITY_NUM": {"en": "Non-numeric arity in '{tok}'.", "it": "Arità non numerica in '{tok}'."},
    "TAB_FOL_SAT": {"en": "SAT / Model", "it": "SAT / Modello"},
    "TAB_FOL_INFER": {"en": "Inference (Premises ⊢ Conclusion)", "it": "Inferenza (Premesse ⊢ Conclusione)"},
    "FOL_EXAMPLE": {"en": "Example: `ForAll(['x'], Implies(Student(x), Attends(x,peter)))`",
                    "it": "Esempio: `ForAll(['x'], Implies(Student(x), Attends(x,peter)))`"},
    "PREMISES_ONE_PER_LINE": {"en": "Premises (one formula per line)", "it": "Premesse (una formula per riga)"},
    "ASK_MODEL_IF_SAT": {"en": "Request model (only if SAT)", "it": "Richiedi modello (solo se SAT)"},
    "BTN_FOL_SAT": {"en": "▶️ Check FOL (SAT)", "it": "▶️ Verifica FOL (SAT)"},
    "ERR_MINIDSL": {"en": "Mini-DSL error: {err}", "it": "Errore nella mini-DSL: {err}"},
    "FOL_INFERENCE_HELP": {"en": "Inference: assert(Premises) ∧ assert(not Conclusion) ⇒ `unsat` if valid.",
                           "it": "Inferenza: assert(Premesse) ∧ assert(not Conclusione) ⇒ `unsat` se valida."},
    "BTN_FOL_INFER": {"en": "▶️ Check FOL (Inference)", "it": "▶️ Verifica FOL (Inferenza)"},
    "CONCLUSION": {"en": "Conclusion", "it": "Conclusione"},

    # ── QUICK TESTER ──────────────────────────────────────────────────────────
    "TESTER_TITLE": {"en": "Quick SMT-LIB Tester", "it": "Tester veloce SMT-LIB"},
    "TESTER_HELP": {"en": "Paste an SMT-LIB formula and check it with Z3. Model shown only if sat.",
                    "it": "Incolla una formula SMT-LIB e verificala con Z3. Il modello è mostrato solo se sat."},
    "BTN_TESTER_CHECK": {"en": "▶️ Check", "it": "▶️ Verifica"},
}
