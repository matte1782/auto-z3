# 🏗️ Auto-Z3 — Architecture Overview (v0.9)

> *“Clarity of architecture is clarity of thought.” 

---

## 🇬🇧 **System Overview (English)**

### 1. Core Design Principles
Auto‑Z3 follows a **modular and transparent** architecture designed for educational clarity, reproducibility, and extensibility.  
Each layer is logically independent yet communicates through minimal, well-defined interfaces.

**Guiding principles:**
- **Separation of concerns** — UI, logic, and solver remain isolated.
- **Reproducibility** — every generated SMT-LIB file can be exported and rechecked independently.
- **Didactic transparency** — each transformation step is visible and explainable.

### 2. Module Structure

```
auto-z3/
│
├── core/
│   ├── logic_core.py          ← defines propositional logic, nodes, emitters
│   ├── solver_adapters.py     ← interfaces (Z3, CNF, etc.)
│   └── z3_runner.py           ← safe execution wrapper for Z3 solver
│
├── color_maps/
│   ├── ui.py                  ← Streamlit interface for map coloring
│   ├── solver.py              ← builds SMT-LIB for graph coloring
│   ├── color_apply.py         ← injects color assignments into GeoJSON
│   └── folium_sat.py          ← renders SAT-colored map with Folium
│
├── app_zen_plus.py            ← main bilingual Streamlit app
├── app_fol.py                 ← FOL (First-Order Logic) module (βeta)
├── i18n.py                    ← internationalization handler
└── tests/                     ← unit + regression + benchmark tests
```

### 3. Data Flow (Simplified)

```text
User → Streamlit UI → Logic Builder / Map UI → SMT-LIB Generator → Z3 Adapter → Result
                                                        ↓
                                                 Model Validator
                                                        ↓
                                                 Visualization (SAT / UNSAT)
```

### 4. Logical Layers

| Layer | Description | Key Files |
|--------|--------------|------------|
| **UI Layer** | Streamlit interface, bilingual text rendering. | `app_zen_plus.py`, `color_maps/ui.py` |
| **Logic Layer** | Expression trees, formula builders, FOL parsers. | `logic_core.py`, `app_fol.py` |
| **Solver Layer** | Handles Z3 communication, error recovery, proof options. | `solver_adapters.py`, `z3_runner.py` |
| **Visualization Layer** | Displays results, maps, and model interpretation. | `folium_sat.py`, `color_apply.py` |

### 5. Future Extensions
- MUS/MCS Explorer module (v1.0+)
- Proof trace export (.drat)
- Plugin system for new solvers (Minisat, PySAT, CVC5)
- UI snapshot regression testing

---

## 🇮🇹 **Panoramica del sistema (Italiano)**

### 1. Principi di progettazione
Auto‑Z3 segue un’architettura **modulare e trasparente**, pensata per la chiarezza didattica, la riproducibilità e l’estendibilità.  
Ogni livello è indipendente ma comunica tramite interfacce minime e ben definite.

**Principi guida:**
- **Separazione dei ruoli** — interfaccia, logica e solver restano isolati.
- **Riproducibilità** — ogni file SMT-LIB generato è esportabile e verificabile in modo indipendente.
- **Trasparenza didattica** — ogni passaggio di trasformazione è visibile e spiegabile.

### 2. Struttura dei moduli

```
auto-z3/
│
├── core/
│   ├── logic_core.py          ← definisce logica proposizionale, nodi, emitter
│   ├── solver_adapters.py     ← interfacce (Z3, CNF, ecc.)
│   └── z3_runner.py           ← esecuzione sicura del solver Z3
│
├── color_maps/
│   ├── ui.py                  ← interfaccia Streamlit per colorazione mappe
│   ├── solver.py              ← genera SMT-LIB per colorazione grafi
│   ├── color_apply.py         ← applica colori alle regioni nel GeoJSON
│   └── folium_sat.py          ← visualizza mappa colorata con Folium
│
├── app_zen_plus.py            ← app principale bilingue (Streamlit)
├── app_fol.py                 ← modulo FOL (logica del primo ordine) in beta
├── i18n.py                    ← gestione internazionalizzazione (traduzioni)
└── tests/                     ← test unitari, di regressione e benchmark
```

### 3. Flusso dei dati (semplificato)

```text
Utente → Interfaccia Streamlit → Builder logico / UI mappa → Generatore SMT-LIB → Adapter Z3 → Risultato
                                                           ↓
                                                  Validatore del modello
                                                           ↓
                                                  Visualizzazione (SAT / UNSAT)
```

### 4. Livelli logici

| Livello | Descrizione | File principali |
|----------|--------------|-----------------|
| **UI Layer** | Interfaccia Streamlit bilingue. | `app_zen_plus.py`, `color_maps/ui.py` |
| **Logic Layer** | Alberi di espressioni, costruttori di formule, parser FOL. | `logic_core.py`, `app_fol.py` |
| **Solver Layer** | Gestione comunicazione con Z3, recupero errori, opzioni proof. | `solver_adapters.py`, `z3_runner.py` |
| **Visualization Layer** | Visualizzazione risultati, mappe e interpretazione modelli. | `folium_sat.py`, `color_apply.py` |

### 5. Estensioni future
- Modulo MUS/MCS Explorer (v1.0+)
- Esportazione proof trace (.drat)
- Sistema plugin per nuovi solver (Minisat, PySAT, CVC5)
- Test di regressione per snapshot UI


