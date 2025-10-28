# 🤝 Contributing to Auto-Z3 (v0.9)

> *“A logical system is only as robust as the clarity of its contributors.” — Alan Turing (simulated)*

Thank you for contributing to **Auto-Z3**, the visual, no-code SAT and FOL solver for education and research.  
Please follow this short guide to ensure consistency, quality, and scientific reproducibility.

---

## 🇬🇧 **ENGLISH VERSION**

### 🧩 1. Fork, Branch, PR — The Basic Flow

1. **Fork** the repository on GitHub.
2. **Clone** your fork locally:
   ```bash
   git clone https://github.com/<your-username>/auto-z3.git
   cd auto-z3
   ```
3. **Create a descriptive branch**:
   ```bash
   git checkout -b feat/new-feature
   ```
4. Make your changes → run all tests (see below).
5. **Commit** with clear and semantic messages.
6. **Push** and open a **Pull Request** to `main`.

---

### 🧠 2. Commit Style (Turing‑Style)

Each commit should start with a **semantic prefix**:

| Type | Use | Example |
|------|------|----------|
| `feat:` | new feature or enhancement | `feat: add unsat-core visualization` |
| `fix:` | bug fix or test fix | `fix: handle missing SMT assertions` |
| `docs:` | documentation, README, tutorials | `docs: update README for v1.0` |
| `test:` | add or modify tests | `test: add benchmark validation for FOL` |
| `refactor:` | code restructuring without logic change | `refactor: modularize solver adapters` |
| `chore:` | maintenance, CI, dependencies | `chore: update requirements.txt` |

> **Turing’s Rule:** A commit must express one complete logical thought.

---

### 🧪 3. Run Tests Before Commit

Before opening a Pull Request:
```bash
pytest -q --disable-warnings
```
All tests must pass (✅). If they don’t, fix the issue or open a *draft PR* with a technical explanation.

---

### 🧱 4. Code Style

- Python ≥ 3.8, PEP8 compliant.
- Use `black` to format:
  ```bash
  black .
  ```
- Avoid ambiguous variable/function names.
- Comment only to add *insight*, not redundancy.

---

### 🔬 5. Contribution Principles

- Every new feature must be **testable** and **reproducible**.
- Maintain backward compatibility with prior versions (≥ 0.9).
- Don’t introduce new dependencies without prior discussion in the PR.
- *“Make it explainable before making it fast.”*

---

### 🧾 6. PR Checklist

Each Pull Request must include:

- ✅ Short description of the change
- 🔍 Reference to any related issue (`Closes #123`)
- 🧪 Local test results (`pytest` passed)
- 📚 Documentation updates, if applicable

---

Thank you for helping build **Auto‑Z3** logically, elegantly, and transparently.  
Each verified contribution brings us closer to an open academic platform, as Turing envisioned.

---

## 🇮🇹 **VERSIONE ITALIANA**

### 🧩 1. Fork, Branch, PR — Il flusso base

1. **Forka** la repository su GitHub.  
2. **Clona** il tuo fork localmente:
   ```bash
   git clone https://github.com/<tuo-username>/auto-z3.git
   cd auto-z3
   ```
3. **Crea un branch descrittivo**:
   ```bash
   git checkout -b feat/nuova-funzionalita
   ```
4. Apporta le modifiche → esegui i test (vedi sotto).
5. Esegui il **commit** con messaggi chiari e coerenti.
6. **Push** e apri una **Pull Request** su `main`.

---

### 🧠 2. Stile dei commit (Turing‑style)

Ogni commit deve iniziare con un *prefisso semantico*:

| Tipo | Uso | Esempio |
|------|------|----------|
| `feat:` | nuova feature o miglioramento | `feat: add unsat-core visualization` |
| `fix:` | correzione bug o test | `fix: handle missing SMT assertions` |
| `docs:` | documentazione, README, tutorial | `docs: update README for v1.0` |
| `test:` | aggiunta o modifica test | `test: add benchmark validation for FOL` |
| `refactor:` | ristrutturazione del codice senza cambiare la logica | `refactor: modularize solver adapters` |
| `chore:` | manutenzione, CI, dipendenze | `chore: update requirements.txt` |

> **Regola di Turing:** ogni commit deve rappresentare un solo pensiero logico completo.

---

### 🧪 3. Test prima del commit

Prima di aprire una Pull Request:
```bash
pytest -q --disable-warnings
```
Tutti i test devono passare (✅).  
In caso contrario, correggi l’errore o apri una *draft PR* con spiegazione tecnica.

---

### 🧱 4. Stile del codice

- Python ≥ 3.8, conforme PEP8.  
- Usa `black` per la formattazione:
  ```bash
  black .
  ```
- Evita nomi ambigui per variabili o funzioni.  
- Commenta solo per aggiungere *intuizione*, non per ripetere il codice.

---

### 🔬 5. Principi di contributo

- Ogni nuova funzionalità deve essere **testabile** e **riproducibile**.  
- Mantieni la compatibilità con le versioni precedenti (≥ 0.9).  
- Non introdurre nuove dipendenze senza discuterle nella PR.  
- *“Meglio spiegabile che veloce.”*

---

### 🧾 6. Checklist della Pull Request

Ogni Pull Request deve contenere:

- ✅ Breve descrizione del cambiamento  
- 🔍 Riferimento a eventuali issue (`Closes #123`)  
- 🧪 Risultati test locali (`pytest` passato)  
- 📚 Aggiornamento documentazione se necessario

---

Grazie per contribuire a **Auto‑Z3** in modo logico, elegante e trasparente.  
Ogni contributo solido e verificato avvicina il progetto a una piattaforma accademica aperta, come avrebbe voluto Turing.

