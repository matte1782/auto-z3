# Auto‑Z3: A Visual, No‑Code SAT & FOL Interface for Z3

*An open educational toolkit for SAT and FOL experimentation*

Auto‑Z3 is a visual front‑end to the Z3 SMT solver.  It lets you build propositional formulas, reason about them using SAT‑based methods, and colour maps via graph colouring constraints—all through a modern Streamlit interface.  A beta editor for first‑order logic (FOL) formulas is also included.  The project was conceived and implemented by **Matteo Panzeri**, a student of Artificial Intelligence at the University of Pavia, with some boilerplate generated with the help of a large language model.

## Table of Contents

1. [Motivation & Goals](#motivation--goals)
2. [Architecture Overview](#architecture-overview)
3. [Installation](#installation)
4. [Quick Examples](#quick-examples)
5. [How Map Colouring Works](#how-map-colouring-works)
6. [Testing & Benchmark](#testing--benchmark)
7. [Roadmap](#roadmap)
8. [Known Issues / Limitations](#known-issues--limitations)
9. [Contributing](#contributing)
10. [Citation](#citation)
11. [License & Credits](#license--credits)

## Motivation & Goals

Formal reasoning and satisfiability solvers are fundamental in computer science research, yet they can be intimidating for newcomers.  Auto‑Z3 bridges this gap by providing:

* A **visual, no‑code environment** for building propositional logic formulas, checking satisfiability, verifying tautologies, and testing logical inferences.
* A **map‑colouring interface** that leverages SAT to assign colours to countries or regions while enforcing adjacency constraints.
* A **beta FOL editor** for experimenting with quantified formulas and predicates.

Whether you teach logic, prototype research ideas or simply want an approachable way to learn about SMT solving, Auto‑Z3 allows you to explore without writing SMT‑LIB by hand or invoking Z3 directly.

## Architecture Overview

Auto‑Z3 is structured into modular Python components.  An ASCII diagram of the high‑level architecture is shown below:

```
app_zen_plus.py        ┐
                        │  Streamlit UI
logic_core.py          ┤  AST & SMT‑LIB emitter
z3_runner.py           │  Safe wrapper around the Z3 solver
color_maps/solver.py   │  Builds SAT formulas for map colouring
color_maps/folium_sat.py│  Renders coloured maps via Folium
color_maps/color_apply.py│ Applies colour palette to GeoJSON
color_maps/preview_folium.py │ Previews base maps
scripts/make_geojson_americas.py ──┐  Prepares GeoJSON & adjacency
scripts/bench_sat.py               └─ Benchmarks SMT solving
tests/                    ── Unit tests (logic_core, map colouring, SMT integrity)
```

### Module summary

* **logic_core.py** – Defines an abstract syntax tree (AST) for propositional logic (`Node`, `Var`, `Not`, `And`, `Or`, `Implies`, `Iff`, `Xor`, `ExactlyOne`) and emits correct SMT‑LIB v2.  It guards against invalid constructs (e.g. parentheses mismatch) and supports scoped assertions.
* **z3_runner.py** – Executes Z3 in a safe subprocess.  It automatically calls `(get-model)` only when the solver reports `sat`.  It returns `sat`, `unsat` or `unknown`, along with the model and raw output.
* **color_maps/solver.py** – Converts a country adjacency graph into an SMT formula for graph colouring.  Each country gets one Boolean per colour.  A custom xorK definition enforces “exactly one colour per country”, and adjacency constraints forbid the same colour on neighbours.
* **color_maps/folium_sat.py** – Uses Folium to render coloured maps from GeoJSON using the SAT assignments and a palette.  It provides zoomable, interactive maps.
* **color_maps/color_apply.py** – Applies an Apple‑inspired palette to GeoJSON features based on solver assignments.  Colours and strokes are stored in feature properties (FILL, STROKE).
* **color_maps/preview_folium.py** – Previews base maps quickly with neutral colours before solving.
* **app_zen_plus.py** – Streamlit frontend combining all features: a builder for logic formulas, preset exercises, colouring of arbitrary maps, a FOL beta editor and a raw SMT tester.
* **scripts/make_geojson_americas.py** – Downloads and simplifies Natural Earth data, generating `data/geo/*.geojson` and `data/adj/*.json` for South and Central America.  Normalises fields to `ISO_A3` and `NAME` and computes adjacency lists.
* **scripts/bench_sat.py** – Benchmarks Z3 on unsatisfiable chains of implications of various lengths (4,8,16,32,64).  Saves SMT instances and prints solve times.
* **scripts/validate_benchmarks.py** – Independently re‑evaluates benchmark results: for SAT formulas it verifies every assertion under the returned model; for map colouring it checks that UNSAT claims are justified by clique lower bounds.  This script gives additional assurance that test outputs are logically valid.
* **tests/** – Contains unit tests:
  * **test_logic_core.py** verifies the SMT emitter (no `Node(` leaks, balanced parentheses) and common logical constructs (tautologies, inferences, equivalences, `ExactlyOne`) using Z3.
  * **test_map_coloring.py** checks that South America is UNSAT with 3 colours (due to a clique of size 4), SAT with 4 colours, and SAT for Central America with 3 colours; it also ensures the model assigns exactly one colour per country.
  * **test_smt_integrity.py** ensures the emitter produces valid SMT‑LIB with balanced parentheses.

## Installation

Auto‑Z3 runs on **Python 3.8+** and requires `z3‑solver`, `streamlit`, `geopandas` and `folium`.  To install and start the app:

```bash
# Clone the repository
git clone https://github.com/matteopanzeri/auto-z3.git
cd auto-z3

# Create an isolated environment (recommended)
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Launch the Streamlit app
streamlit run app_zen_plus.py
```

On first run, the app will download the Z3 Python bindings, load Streamlit and Geopandas, and prepare base maps.  When ready, open your browser at [localhost:8501](http://localhost:8501/).

## Quick Examples

### Propositional Logic

1. Open the **Builder formule (STRICT)** tab.
2. Enter variables (e.g. `p q r`).
3. Build sub‑formulas using the visual constructor (AND/OR/IMPLIES/IFF/XOR).
4. Select any sub‑formulas as **premises** and set the main formula Φ.
5. Choose a task: **SAT**, **Inference** or **Tautology** and press **Genera & Verifica**.

The app displays the generated SMT‑LIB and the solver’s result.  Inferences are checked by adding `(not Φ)` to the premises; tautologies simply assert `(not Φ)` and look for UNSAT.

*Screenshot placeholder*: `!SOON UPDATED'

### Map Colouring

1. Open **Colora Mappe (nuovo)**.
2. Choose a dataset: *Sud America (Paesi)* or *America Centrale (Paesi)*.
3. Select the number of colours (2–8).  By graph theory, 3 or 4 are typical for these maps.
4. Click **Risolvi**.  If colourable, the map animates with a smooth fill; otherwise the solver reports UNSAT and the UI flashes red briefly.

*Screenshot placeholder*: `!SOON UPDATED'

### FOL (Beta)

The **First‑Order Logic (βeta)** tab lets you experiment with quantified formulas such as:

```python
ForAll(['x'], Implies(Student(x), Attends(x, lecture)))
Exists(['y'], And(Student(y), Loves(y, pizza)))
```

Current features include `Not`, `And`, `Or`, `Implies`, `Iff`, `Xor`, equality `Eq(a,b)`, arbitrary predicates (e.g. `Loves/2`) and universal/existential quantifiers over a named sort.  FOL support is experimental; report any issues in the issue tracker.

*Screenshot placeholder*: `![FOL_beta](/docs/img/fol_beta.png)`

## How Map Colouring Works

Map colouring is modelled as a SAT problem.  For a map with **N** regions and **K** colours:

* Each region `i` has `K` boolean variables `i_0`, `i_1`, …, `i_{K‑1}`, one for each colour.
* A helper function `xorK` (a generalisation of `xor3`) enforces that exactly one of these booleans is true:

  ```
  (define-fun xorK ((c0 Bool) … (cK‑1 Bool)) Bool
    (and (or c0 … cK‑1) ((_ at-most 1) c0 … cK‑1)))
  ```

* For each region `i`, we assert `(xorK i_0 … i_{K‑1})`.
* For every adjacent pair of regions `(u,v)` and each colour `c`, we assert `(not (and u_c v_c))`.  This forbids neighbours from sharing the same colour.

If Z3 returns **unsat**, then the map cannot be coloured with **K** colours; for example, the South American countries `(Bolivia, Brazil, Paraguay, Argentina)` form a clique of size 4, so 3 colours are insufficient.  Our tests confirm:

| Map                     | K colours | Solver result |
|-------------------------|-----------|---------------|
| South America (Paesi)   | 3         | **UNSAT** (clique 4) |
| South America (Paesi)   | 4         | **SAT** |
| South America (Paesi)   | 5         | **SAT** |
| Central America (Paesi) | 3         | **SAT** |

## Testing & Benchmark

Auto‑Z3 includes a robust test suite to ensure correctness and reproducibility.  Running the tests is as simple as:

```bash
pytest -q --maxfail=1 --disable-warnings --junitxml=tests/_artifacts/junit-report.xml
```

All 20 tests currently pass in under one second on a typical laptop.  The test suite covers:

* **SMT‑LIB emitter correctness**: ensures no internal `Node(` structures leak into output and that parentheses are balanced.
* **Logical constructs**: checks tautologies like `((p→q)∧(q→r)∧p)→r`, inference patterns (`p,p→q ⊢ q`), equivalences (`p↔q` and `(p→q)∧(q→p)`), and `ExactlyOne` constraints on multiple variables.
* **Map colouring**: verifies South America is unsatisfiable with 3 colours (due to K4), satisfiable with 4 and 5 colours, and that Central America is satisfiable with 3 colours.  Models are checked to ensure exactly one colour per country.
* **SMT integrity**: ensures generated SMT files always have balanced parentheses and no stray `Node(` strings.

### Benchmarks

To measure solver performance, run:

```bash
python scripts/bench_sat.py --out tests/_artifacts
```

This script generates unsatisfiable implication chains of lengths 4, 8, 16, 32 and 64.  The results on a reference machine show solve times under ~0.05 seconds:

```
name,status,time_s
chain_unsat_4,unsat,0.06
chain_unsat_8,unsat,0.02
chain_unsat_16,unsat,0.04
chain_unsat_32,unsat,0.04
chain_unsat_64,unsat,0.05
```

### Model Validation

To increase confidence, the script `scripts/validate_benchmarks.py` re‑checks every SMT instance after benchmarks:

* For **SAT** results, it parses the Z3 model and independently evaluates every `assert` to ensure the assignment satisfies each constraint.
* For **UNSAT** map‑colouring results, it extracts the graph and colour count and checks that a clique lower bound justifies unsatisfiability (for example, South America contains a clique of size 4, so UNSAT is expected for K < 4).

Validation outputs confirm all benchmarks are logically sound:

```
[OK] central_america_3colors.smt2 — SAT model validates 35 asserts.
[OK] south_america_3colors.smt2 — UNSAT consistent (K=3 < clique 4).
[OK] south_america_4colors.smt2 — SAT model validates 105 asserts.
[OK] south_america_5colors.smt2 — SAT model validates 128 asserts.
…
[validator] All benchmark instances validated successfully.
```

## Roadmap

| Version   | Key features                                                         | Status  |
|----------:|---------------------------------------------------------------------|:-------:|
| **v0.9‑beta** | Core Streamlit UI; strict SAT builder; preset exercises; map colouring for South/Central America | ✅ |
| **v1.0**       | Complete FOL support (quantifiers, n‑ary predicates); improved map UI (legend, export) | 🚧 |
| **v1.1**       | Model export (JSON/CSV), REST API endpoints, multiple map datasets                 | ⏳ |
| **v2.0**       | Plugin system for new logics (e.g. linear arithmetic), advanced visualisations      | 🧩 |

Community feedback is welcome to refine these milestones.  Please share ideas via issues or pull requests.

## Known Issues / Limitations

* **Map data simplification** – The included GeoJSON files are simplified for performance.  Borders are approximate; minor adjacency relationships may be lost.  Feel free to regenerate `data/geo` from Natural Earth using `scripts/make_geojson_americas.py`.
* **FOL module is a beta** – Quantifiers and complex predicates are still experimental.  There is no model display for FOL yet.  Report test cases or suggestions via the issue tracker.
* **Mobile support** – Streamlit pages render best on desktop screens.  Touch interactions may not be fully supported.
* **Large SAT instances** – Z3 handles moderate SAT formulas quickly, but extremely large or deeply nested expressions may time out.  Consider breaking problems into smaller parts.

## Contributing

Auto‑Z3 is an open‑source project.  Contributions are encouraged!  To contribute:

1. **Open an issue** describing a bug or feature.  Include steps to reproduce and, if applicable, minimal SMT‑LIB examples.
2. **Fork the repository** and create a descriptive branch name (e.g. `fix-map-adj-sat`, `feature-fol-predicates`).
3. **Add tests** to `tests/` that reproduce your bug or demonstrate your new feature.  Running `pytest` should pass after your changes.
4. **Run the validator** (`scripts/validate_benchmarks.py`) on any new benchmarks to ensure results are logically sound.
5. Submit a **pull request** summarising your changes and linking to the issue.  Follow Python PEP 8 style and keep UI changes consistent with the existing design.

We use GitHub Actions for continuous integration.  Contributions that include new data (GeoJSON) must clearly state the source and licence.

## Citation

If you use Auto‑Z3 in academic work, please cite it as follows:

```bibtex
@software{Panzeri_AutoZ3_2025,
  author       = {Matteo Panzeri},
  title        = {Auto‑Z3: A Visual, No‑Code Interface to Z3},
  year         = {2025},
  url          = {https://github.com/matteopanzeri/auto-z3},
  note         = {Open‑source educational toolkit for SAT and FOL experimentation}
}
```

We gratefully acknowledge the SMT‑LIB standard and the Z3 solver community for their foundational work.

## License & Credits

This project is released under the **MIT License**.  See the `LICENSE` file for the full text.  In short, you are free to use, copy, modify and distribute this software, as long as the original copyright notice is included.

```
MIT License
© 2025 Matteo Panzeri

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

…
```

### Ownership and Attribution

Auto‑Z3 was conceived and implemented by **Matteo Panzeri**.  Some boilerplate code (e.g. UI scaffolding) was written with the help of a generative language model, but the architecture, design and integration are fully original.  When adapting the code for research or teaching, please credit the original author.

---

Thank you for exploring **Auto‑Z3**.  We hope it becomes a valuable tool in your logic courses, workshops and research projects.

## Acknowledgments

This project was inspired by the *Computational Logic* course at the University of Milan (Università degli Studi di Milano).
