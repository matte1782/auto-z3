# 🎓 Auto-Z3 Teaching Guide (v0.9)

> *An open learning resource for logic, SAT, and model reasoning — written by Matteo Panzeri.*

---

## 🇬🇧 **English Version**

### 1. Purpose of this Guide
Auto‑Z3 is designed as a **teaching and learning companion** for logic courses, computational reasoning, and AI foundations.  
It bridges abstract logic with visual, interactive experimentation.

This guide provides instructors and students with **ready‑to‑use lessons**, **guided experiments**, and **classroom examples** built directly into Auto‑Z3.

---

### 2. Learning Objectives
By the end of these exercises, students should be able to:

1. Construct propositional and first‑order formulas using a no‑code visual builder.
2. Translate logical formulas into SMT‑LIB v2 form.
3. Use Z3 to check satisfiability, inference, and equivalence.
4. Understand how model validation and UNSAT reasoning work.
5. Apply SAT solving to real‑world problems — such as **map coloring**, **Sudoku**, and **graph constraints**.

---

### 3. Course Integration
Auto‑Z3 can be used in various courses:

| Course Type | Example Use |
|--------------|--------------|
| **Intro to Logic / CS Foundations** | Building truth tables, verifying tautologies. |
| **Artificial Intelligence (Undergraduate)** | Constraint solving, symbolic reasoning. |
| **Formal Methods / Verification** | Exploring SMT‑LIB encoding, UNSAT cores. |
| **Discrete Mathematics** | Graph coloring, SAT reductions. |
| **Education / Didactics of Logic** | Guided exercises for logic understanding. |

---

### 4. Module-by-Module Exercises

#### 🧩 A. Propositional Logic (Builder Mode)
**Goal:** Learn logical structure and equivalence.

**Steps:**
1. Open *Builder (STRICT)* tab.
2. Declare variables: `p q r`.
3. Create sub‑formulas using logical operators.
   - Example: `Implies(p, q)`, `And(p, Not(q))`.
4. Set main formula Φ and premises.
5. Choose **task type**: `SAT`, `Inference`, `Tautology`, or `Equivalence`.
6. Click **Generate & Verify with Z3**.

**Discussion point:** How does Z3 decide satisfiability? What does the returned model represent?

**Instructor Tip:** Encourage students to modify one operator (e.g., `Or` → `And`) and observe how the logical outcome changes.

---

#### 🌈 B. Map Coloring (Graph SAT Problems)
**Goal:** Apply SAT solving to combinatorial constraints.

**Steps:**
1. Select *Color Maps (new)* tab.
2. Choose dataset: `South America` or `Central America`.
3. Select **number of colors** `k`.
4. Click **Solve**.
5. Observe SAT / UNSAT result and inspect colored map.
6. Export `.smt2` file or colored GeoJSON.

**Extension:** Try `k = 3`, `k = 4`, `k = 5` and discuss the minimum satisfiable coloring.

**Learning focus:**
- Understanding constraints `(not (and u_i v_i))`.
- Relation between **clique size** and **chromatic number**.

**Instructor Tip:** Connect to the *Four Color Theorem* as a historical context.

---

#### 🔍 C. First‑Order Logic (FOL βeta)
**Goal:** Understand quantifiers, predicates, and finite domains.

**Steps:**
1. Open *FOL (beta)* tab.
2. Define constants (e.g., `peter joan mary`).
3. Define predicates: `Student/1, Attends/2`.
4. Write formula: `ForAll(['x'], Implies(Student(x), Attends(x, peter)))`.
5. Click **Check SAT** or **Inference**.

**Discussion point:** How do quantifiers expand over the finite domain? What does “SAT” mean for quantified logic?

**Extension:** Use `Exists` instead of `ForAll` and observe differences.

---

#### 🧮 D. Puzzles and Presets (coming v1.0)
Auto‑Z3 will soon include preset examples:
- **Sudoku 4×4 / 9×9** using Boolean encoding.
- **Graph 3‑coloring random instances.**
- **Logic quiz** (auto‑graded exercises for students).

These allow instructors to assign **hands‑on labs** or **mini‑projects** without setup.

---

### 5. Assessment Suggestions
| Method | Example |
|---------|----------|
| Short Quiz | Identify which formula is a tautology. |
| Debug Task | Give students a flawed formula, ask them to fix it. |
| Open Challenge | “Encode and solve a Sudoku with 16 cells.” |
| Reflection | “Describe in your own words what ‘unsat’ means.” |

---

### 6. Recommended Class Flow

| Phase | Duration | Activity |
|--------|-----------|-----------|
| **Intro** | 10 min | Present logical operators and interface. |
| **Practice 1** | 15 min | Propositional Builder exercise. |
| **Practice 2** | 20 min | Map Coloring SAT visualization. |
| **Discussion** | 10 min | Interpreting Z3 output and UNSAT reasoning. |
| **Homework** | — | FOL examples + mini puzzle (Sudoku / 3‑color). |

---

### 7. Export & Sharing
Auto‑Z3 automatically allows exporting:
- Generated SMT‑LIB v2 files.
- Z3 model outputs.
- Colored maps (GeoJSON).

These can be integrated into Jupyter notebooks, reports, or further experiments.

---

### 8. Pedagogical Value Summary
Auto‑Z3 emphasizes:
- **Interactivity:** logic as exploration, not theory only.
- **Transparency:** every formula is visible in SMT‑LIB form.
- **Universality:** applicable from high school logic to graduate‑level AI.
- **Open Science:** fully inspectable code and data.

---

## 🇮🇹 **Versione Italiana**

### 1. Scopo della guida
Auto‑Z3 è pensato come **strumento didattico e interattivo** per corsi di logica, ragionamento computazionale e basi dell’intelligenza artificiale.  
Collega la logica astratta con l’esperimento pratico e visuale.

Questa guida fornisce a docenti e studenti **lezioni pronte all’uso**, **esperimenti guidati** e **esempi per il laboratorio**, integrati direttamente nell’app Auto‑Z3.

---

### 2. Obiettivi di apprendimento
Alla fine degli esercizi, lo studente sarà in grado di:
1. Costruire formule proposizionali e del primo ordine con un builder visuale.
2. Tradurre formule logiche in formato SMT‑LIB v2.
3. Utilizzare Z3 per verificare soddisfacibilità, inferenza ed equivalenza.
4. Comprendere la validazione dei modelli e il significato di UNSAT.
5. Applicare la logica a problemi reali: **colorazione mappe**, **Sudoku**, **vincoli di grafi**.

---

### 3. Integrazione nei corsi
| Tipo di corso | Utilizzo suggerito |
|----------------|--------------------|
| **Logica / Fondamenti CS** | Costruzione tabelle di verità, verifica di tautologie. |
| **Intelligenza Artificiale (laurea)** | Risoluzione di vincoli e ragionamento simbolico. |
| **Metodi Formali / Verifica** | Esplorazione encoding SMT‑LIB e UNSAT core. |
| **Matematica Discreta** | Colorazione grafi e riduzioni SAT. |
| **Didattica della logica** | Esercizi interattivi per la comprensione logica. |

---

### 4. Esercizi per modulo

#### 🧩 A. Logica proposizionale (Builder)
**Obiettivo:** comprendere struttura ed equivalenza logica.

**Passaggi:**
1. Apri la scheda *Builder (STRICT)*.
2. Definisci le variabili: `p q r`.
3. Crea sotto‑formule con operatori logici.
   - Esempio: `Implies(p, q)`, `And(p, Not(q))`.
4. Imposta la formula principale Φ e le premesse.
5. Scegli **tipo di task**: `SAT`, `Inferenza`, `Tautologia`, `Equivalenza`.
6. Clicca **Genera & Verifica con Z3**.

**Discussione:** come decide Z3 la soddisfacibilità? Cosa rappresenta il modello restituito?

**Suggerimento docente:** chiedere agli studenti di cambiare un operatore (`Or` → `And`) e discutere come varia il risultato.

---

#### 🌈 B. Colorazione mappe (SAT su grafi)
**Obiettivo:** applicare SAT solving a vincoli combinatori.

**Passaggi:**
1. Seleziona la scheda *Colora Mappe (nuovo)*.
2. Scegli dataset: `Sud America` o `America Centrale`.
3. Imposta **numero colori** `k`.
4. Clicca **Risolvi**.
5. Osserva risultato SAT / UNSAT e la mappa colorata.
6. Esporta `.smt2` o GeoJSON colorato.

**Estensione:** prova con `k = 3`, `k = 4`, `k = 5` e confronta il minimo numero di colori possibile.

**Concetti chiave:**
- Vincoli `(not (and u_i v_i))` tra regioni adiacenti.
- Relazione tra **clique** e **numero cromatico**.

**Suggerimento docente:** collega l’attività al *Teorema dei quattro colori*.

---

#### 🔍 C. Logica del primo ordine (FOL βeta)
**Obiettivo:** comprendere quantificatori, predicati e domini finiti.

**Passaggi:**
1. Apri la scheda *FOL (beta)*.
2. Definisci costanti (es.: `peter joan mary`).
3. Definisci predicati: `Student/1, Attends/2`.
4. Scrivi formula: `ForAll(['x'], Implies(Student(x), Attends(x, peter)))`.
5. Clicca **Verifica FOL (SAT)** o **Inferenza**.

**Discussione:** come vengono espansi i quantificatori sul dominio finito? Cosa significa “SAT” in logica quantificata?

**Estensione:** usa `Exists` al posto di `ForAll` e confronta i risultati.

---

#### 🧮 D. Puzzle e preset (in arrivo v1.0)
Saranno presto inclusi esempi come:
- **Sudoku 4×4 / 9×9** (encoding booleano).
- **Grafi 3‑colorabili casuali.**
- **Quiz logici** con correzione automatica.

Ideali per esercitazioni di laboratorio o mini‑progetti.

---

### 5. Valutazione suggerita
| Metodo | Esempio |
|---------|----------|
| Quiz breve | Identificare quale formula è tautologia. |
| Esercizio debug | Dare una formula errata e chiedere di correggerla. |
| Sfida aperta | “Codifica e risolvi un Sudoku 4×4.” |
| Discussione riflessiva | “Spiega con parole tue cosa significa UNSAT.” |

---

### 6. Struttura di lezione consigliata
| Fase | Durata | Attività |
|-------|----------|-----------|
| **Introduzione** | 10 min | Presentazione operatori logici e interfaccia. |
| **Esercizio 1** | 15 min | Builder proposizionale. |
| **Esercizio 2** | 20 min | Colorazione mappe SAT. |
| **Discussione** | 10 min | Interpretazione output Z3 e UNSAT. |
| **Compito** | — | Esercizi FOL + mini‑puzzle. |

---

### 7. Esportazione e condivisione
Auto‑Z3 consente di esportare:
- File SMT‑LIB v2 generati.
- Output del modello Z3.
- Mappe colorate (GeoJSON).

Utilizzabili in notebook, relazioni o esperimenti.

---

### 8. Valore didattico
Auto‑Z3 valorizza:
- **Interattività:** la logica come esplorazione, non solo teoria.
- **Trasparenza:** ogni formula è visibile in formato SMT‑LIB.
- **Universalità:** utile dal liceo all’università.  
- **Open Science:** codice e dati totalmente ispezionabili.

---

> Version 0.9 — A foundation for teaching logic through interactivity, precision, and open access.

