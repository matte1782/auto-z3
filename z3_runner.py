# z3_runner.py  — v2.1 (stable triple-return)
import subprocess, tempfile, os, re
from typing import Tuple

STATUS_RE = re.compile(r'^(sat|unsat|unknown)\s*$', re.M)

def _extract_status(stdout: str) -> str:
    m = STATUS_RE.search(stdout or "")
    return m.group(1) if m else "error"

def run_z3_safely(smt2_text: str, request_model: bool = True) -> Tuple[str, str, str]:
    """
    Ritorna SEMPRE una tripla: (status, model_text, raw_stdout)
    - status ∈ {'sat','unsat','unknown','error'}
    - model_text è valorizzato solo se status == 'sat' (altrimenti stringa vuota)
    - raw_stdout è sempre lo stdout completo dell'ultima run
    """
    # assicura newline finale
    smt2_text = smt2_text if smt2_text.endswith("\n") else smt2_text + "\n"

    # scrivi su file temporaneo
    with tempfile.NamedTemporaryFile(delete=False, suffix=".smt2", mode="w", encoding="utf-8") as f:
        f.write(smt2_text)
        path = f.name

    try:
        # 1) prima esecuzione per lo status
        p = subprocess.run(["z3", "-smt2", path], capture_output=True, text=True)
        out = (p.stdout or "")
        status = _extract_status(out)

        model = ""
        # 2) se vogliamo il modello e siamo sat: chiedilo (solo se non già presente)
        if request_model and status == "sat" and "(get-model)" not in smt2_text:
            with open(path, "a", encoding="utf-8") as f2:
                f2.write("(get-model)\n")
            p2 = subprocess.run(["z3", "-smt2", path], capture_output=True, text=True)
            out2 = (p2.stdout or "")
            # Il modello inizia dalla prima parentesi aperta dopo la riga "sat"
            # (non è obbligatorio, ma rende l’output più pulito in UI)
            i = out2.find("(")
            model = out2[i:] if i != -1 else out2
            return (status, model.strip(), out2.strip())

        # caso non-sat / non richiediamo model / già presente get-model
        if status == "sat":
            # prova a estrarre un eventuale modello presente in out
            i = out.find("(")
            model = out[i:] if i != -1 else ""
        return (status, model.strip(), out.strip())

    finally:
        try:
            os.unlink(path)
        except Exception:
            pass
