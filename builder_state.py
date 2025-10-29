from dataclasses import dataclass, field
from typing import List, Optional

from logic_core import Expr


@dataclass
class BuilderState:
    pool: List[Expr] = field(default_factory=list)  # elenco sotto-formule
    phi_idx: Optional[int] = None  # indice formula principale
    undo: List[List[Expr]] = field(default_factory=list)
    redo: List[List[Expr]] = field(default_factory=list)

    def snapshot(self):
        self.undo.append(self.pool.copy())
        self.redo.clear()

    def reset_to_vars(self, vars_: List[str]):
        self.snapshot()
        self.pool = list(vars_)
        self.phi_idx = None

    def push(self, e: Expr):
        self.snapshot()
        self.pool.append(e)

    def delete_indices(self, idxs: List[int]):
        if not idxs:
            return
        self.snapshot()
        keep = [e for i, e in enumerate(self.pool) if i not in set(idxs)]
        self.pool = keep
        if self.phi_idx is not None and self.phi_idx >= len(self.pool):
            self.phi_idx = len(self.pool) - 1 if self.pool else None

    def set_phi(self, i: int):
        self.phi_idx = max(0, min(i, len(self.pool) - 1)) if self.pool else None

    def do_undo(self):
        if not self.undo:
            return
        self.redo.append(self.pool.copy())
        self.pool = self.undo.pop()

    def do_redo(self):
        if not self.redo:
            return
        self.undo.append(self.pool.copy())
        self.pool = self.redo.pop()
