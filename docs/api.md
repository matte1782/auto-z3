# ⚙️ Auto-Z3 — API Reference (v0.9)

---

## 🇬🇧 **English Version**

### Overview
The API of Auto-Z3 is intentionally minimal and transparent.  
Each module exposes functions that correspond to a clear logical or operational step — from formula creation to solver execution and model validation.

All modules are **pure Python**, with no hidden state. This allows deterministic behavior, easy testing, and educational clarity.

---

### 1. `core.logic_core`
Defines the propositional logic primitives and utilities for generating valid SMT-LIB expressions.

#### Key Classes & Functions
| Function / Class | Description |
|------------------|-------------|
| `Var(name)` | Defines a boolean variable node. |
| `Not(expr)` | Negation of a logical expression. |
| `And(*exprs)` | Conjunction of multiple expressions. |
| `Or(*exprs)` | Disjunction of multiple expressions. |
| `Implies(a,b)` | Logical implication. |
| `Iff(a,b)` | Bi-conditional (a ↔ b). |
| `Xor(a,b)` | Exclusive OR. |
| `ExactlyOne(*vars)` | True if exactly one variable is True. |
| `emit_expr(expr)` | Converts a Node or composite formula into valid SMT-LIB syntax. |
| `declare_block(vars)` | Creates SMT declarations for variables. |
| `assert_line(expr)` | Formats an assert statement. |
| `check_sat()` | Adds the `(check-sat)` command. |

---

### 2. `core.solver_adapters`
Provides a unified interface to connect external solvers like Z3 or future backends.

#### Example Interface
```python
class ISolverAdapter:
    def solve(self, smt: str) -> tuple[str, str, str]:
        """Executes the solver and returns (status, model, raw_output)."""

    def get_model(self) -> str:
        """Returns the solver model if SAT."""

    def get_unsat_core(self) -> list[str]:
        """Returns the unsat core if available."""
```

---

### 3. `core.z3_runner`
Safely runs the Z3 solver with proper error handling and timeout management.

| Function | Description |
|-----------|-------------|
| `run_z3_safely(smt: str, request_model: bool = True)` | Executes Z3 in a controlled environment. Returns `(status, model, raw_output)` with graceful fallbacks for syntax errors or timeouts. |

---

### 4. `color_maps.solver`
Builds SMT-LIB problems for graph or map coloring.

| Function | Description |
|-----------|-------------|
| `build_map_smt(nodes, edges, k)` | Generates SMT-LIB v2 for k-coloring problem based on adjacency data. Ensures unique declaration and XOR-k constraints. |

---

### 5. `color_maps.color_apply`
Applies the color assignment from the solver model to a GeoJSON map.

| Function | Description |
|-----------|-------------|
| `inject_colors(geojson_path, assignment, palette)` | Reads GeoJSON, adds color properties (FILL/STROKE) per country ISO, and returns the colored map as dictionary. |

---

### 6. `color_maps.folium_sat`
Handles map rendering using Folium and Streamlit-Folium.

| Function | Description |
|-----------|-------------|
| `render_sat_map(geojson_path, assignment)` | Renders a Folium map based on SAT model assignment. Fits viewport automatically. |

---

### 7. `app_fol`
Implements the beta First-Order Logic interface with quantifiers, constants, and predicates.

| Function | Description |
|-----------|-------------|
| `make_env(preds, funs, consts, vars)` | Builds DSL environment mapping symbols to callable constructors. |
| `build_smt2_universe(...)` | Expands FOL formula to finite domain and emits full SMT-LIB v2. |

---

### 8. `i18n`
Manages internationalization for UI text.

| Function | Description |
|-----------|-------------|
| `t(key, lang=None, **fmt)` | Returns translated text with safe fallbacks. |
| `set_default_lang(lang)` | Sets global default language. |
| `get_default_lang()` | Returns current active language. |

---

### 9. `tests`
Contains full test and benchmark suite.

| File | Purpose |
|-------|----------|
| `test_logic_core.py` | Unit tests for formula builder and emitter. |
| `test_maps.py` | Tests for map coloring SMT generation. |
| `test_fol.py` | Tests for FOL encoding and quantifier expansion. |
| `validate_benchmarks.py` | Revalidates SAT/UNSAT model correctness and runtime. |

---

## 🇮🇹 **Versione Italiana**

### Panoramica
L’API di Auto-Z3 è volutamente minima e trasparente.  
Ogni modulo espone funzioni che corrispondono a passaggi logici precisi — dalla creazione di formule all’esecuzione del solver e alla validazione del modello.

Tutti i moduli sono **in puro Python**, senza stato nascosto, garantendo comportamento deterministico, facilità di test e chiarezza didattica.

---

### 1. `core.logic_core`
Definisce le primitive della logica proposizionale e gli strumenti per generare espressioni SMT-LIB valide.

| Funzione / Classe | Descrizione |
|------------------|-------------|
| `Var(name)` | Definisce un nodo variabile booleana. |
| `Not(expr)` | Negazione di un’espressione logica. |
| `And(*exprs)` | Congiunzione di più espressioni. |
| `Or(*exprs)` | Disgiunzione di più espressioni. |
| `Implies(a,b)` | Implicazione logica. |
| `Iff(a,b)` | Bi-condizionale (a ↔ b). |
| `Xor(a,b)` | XOR (o esclusivo). |
| `ExactlyOne(*vars)` | Vero se esattamente una variabile è vera. |
| `emit_expr(expr)` | Converte un nodo o formula in sintassi SMT-LIB valida. |
| `declare_block(vars)` | Crea dichiarazioni SMT per le variabili. |
| `assert_line(expr)` | Formatta una linea di assert. |
| `check_sat()` | Aggiunge il comando `(check-sat)`. |

---

### 2. `core.solver_adapters`
Fornisce un’interfaccia unificata per connettere solver esterni come Z3 o futuri backend.

#### Esempio di interfaccia
```python
class ISolverAdapter:
    def solve(self, smt: str) -> tuple[str, str, str]:
        """Esegue il solver e restituisce (status, modello, output grezzo)."""

    def get_model(self) -> str:
        """Restituisce il modello del solver se SAT."""

    def get_unsat_core(self) -> list[str]:
        """Restituisce l’unsat core se disponibile."""
```

---

### 3. `core.z3_runner`
Esegue Z3 in modo sicuro, gestendo errori e timeout.

| Funzione | Descrizione |
|-----------|-------------|
| `run_z3_safely(smt: str, request_model: bool = True)` | Esegue Z3 in un ambiente controllato. Restituisce `(status, model, raw_output)` con gestione sicura di errori o timeout. |

---

### 4. `color_maps.solver`
Genera problemi di colorazione grafi in formato SMT-LIB.

| Funzione | Descrizione |
|-----------|-------------|
| `build_map_smt(nodes, edges, k)` | Genera un file SMT-LIB v2 per problemi di k-coloring basati su grafi di adiacenza. |

---

### 5. `color_maps.color_apply`
Applica gli assegnamenti di colore del modello a una mappa GeoJSON.

| Funzione | Descrizione |
|-----------|-------------|
| `inject_colors(geojson_path, assignment, palette)` | Legge il GeoJSON, aggiunge proprietà di colore (FILL/STROKE) per ogni ISO e restituisce la mappa colorata. |

---

### 6. `color_maps.folium_sat`
Gestisce la visualizzazione delle mappe con Folium e Streamlit-Folium.

| Funzione | Descrizione |
|-----------|-------------|
| `render_sat_map(geojson_path, assignment)` | Visualizza una mappa Folium basata sul modello SAT. Regola automaticamente i limiti della vista. |

---

### 7. `app_fol`
Implementa il modulo FOL (logica del primo ordine) con quantificatori, costanti e predicati.

| Funzione | Descrizione |
|-----------|-------------|
| `make_env(preds, funs, consts, vars)` | Crea un ambiente DSL che mappa simboli a costruttori invocabili. |
| `build_smt2_universe(...)` | Espande formule FOL su dominio finito e genera SMT-LIB completo. |

---

### 8. `i18n`
Gestisce l’internazionalizzazione dell’interfaccia utente.

| Funzione | Descrizione |
|-----------|-------------|
| `t(key, lang=None, **fmt)` | Restituisce il testo tradotto con fallback sicuro. |
| `set_default_lang(lang)` | Imposta la lingua predefinita globale. |
| `get_default_lang()` | Restituisce la lingua attiva corrente. |

---

### 9. `tests`
Contiene tutti i test e benchmark.

| File | Scopo |
|-------|-------|
| `test_logic_core.py` | Test unitari per builder ed emitter di formule. |
| `test_maps.py` | Test per la generazione SMT delle mappe. |
| `test_fol.py` | Test per l’encoding FOL e l’espansione dei quantificatori. |
| `validate_benchmarks.py` | Ricontrolla la correttezza dei modelli SAT/UNSAT e i tempi di esecuzione. |

---

> The API is built for precision, readability, and transparency — ideal for both research and classroom use.

