#!/usr/bin/env python3
import os, ast, sys
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[1]
SRC_DIRS = [ROOT]  # scan whole repo

def module_name_from_path(p: Path) -> str:
    rel = p.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    if parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)

def find_py_files():
    for d in SRC_DIRS:
        for p in d.rglob("*.py"):
            if any(skip in p.parts for skip in (".venv", ".pytest_cache", "__pycache__", "tests", "data")):
                continue
            yield p

def parse_imports(p: Path):
    try:
        tree = ast.parse(p.read_text(encoding="utf-8"))
    except Exception:
        return set()
    mods = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for n in node.names:
                mods.add(n.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                mods.add(node.module.split(".")[0])
    return mods

def main():
    files = list(find_py_files())
    mod_by_path = {p: module_name_from_path(p) for p in files}
    path_by_mod = {v: k for k, v in mod_by_path.items()}

    deps = defaultdict(set)
    for p in files:
        imps = parse_imports(p)
        for m in imps:
            if m in path_by_mod:
                deps[mod_by_path[p]].add(m)

    # Roots: entrypoints + tests (don’t scan tests for imports here)
    roots = set()
    for ep in ["app_zen_plus", "scripts.bench_sat", "scripts.validate_benchmarks"]:
        if ep in path_by_mod:
            roots.add(ep)

    # Reachability
    reachable = set(roots)
    changed = True
    while changed:
        changed = False
        for a, imps in deps.items():
            if a in reachable:
                for b in imps:
                    if b not in reachable:
                        reachable.add(b); changed = True
            # Also add any module that imports a reachable module (looser union)
            if any(b in reachable for b in imps) and a not in reachable:
                reachable.add(a); changed = True

    unreachable = [p for p, mod in mod_by_path.items() if mod not in reachable]

    print("== Reachable modules ==")
    for mod in sorted(reachable):
        if mod in path_by_mod:
            print("  ", path_by_mod[mod].relative_to(ROOT))

    print("\n== Potentially orphan .py files (manual review) ==")
    for p in sorted(unreachable):
        print("  ", p.relative_to(ROOT))

    print("\nNOTE: This is static and conservative. Review before deleting.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
