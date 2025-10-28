# ───────────────────────────────────────────────────────────────
# conftest.py — setup test environment for Auto-Z3
# ───────────────────────────────────────────────────────────────
import os
import sys
import json
import pytest

# ✅ Fix: ensure the project root is visible for imports
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

# ───────────────────────────────────────────────────────────────
# Directory paths (relative to project root)
# ───────────────────────────────────────────────────────────────
DATA_GEO = os.path.join(ROOT, "data", "geo")
DATA_ADJ = os.path.join(ROOT, "data", "adj")

@pytest.fixture(scope="session")
def paths():
    """Global test paths for fixtures and artifact output."""
    return {
        "root": ROOT,
        "geo": DATA_GEO,
        "adj": DATA_ADJ,
        "south_adj": os.path.join(DATA_ADJ, "south_america_neighbors.json"),
        "central_adj": os.path.join(DATA_ADJ, "central_america_neighbors.json"),
        "artifacts": os.path.join(ROOT, "tests", "_artifacts"),
    }

@pytest.fixture(scope="session", autouse=True)
def ensure_artifacts(paths):
    """Ensure artifact directory exists before running tests."""
    os.makedirs(paths["artifacts"], exist_ok=True)

# ───────────────────────────────────────────────────────────────
# Utility loader for adjacency JSON (handles both formats)
# ───────────────────────────────────────────────────────────────
def _load_adj(path):
    with open(path, "r", encoding="utf-8") as f:
        obj = json.load(f)

    # Support both adjacency-list {A:[B,C]} and edge-list {"edges":[[A,B],...]}
    if isinstance(obj, dict) and "edges" in obj:
        edges = obj["edges"]
        nodes = sorted({n for e in edges for n in e})
        neigh = {n: set() for n in nodes}
        for a, b in edges:
            neigh[a].add(b)
            neigh[b].add(a)
        return neigh
    elif isinstance(obj, dict):
        return {k: set(v) for k, v in obj.items()}
    else:
        raise ValueError(f"Unsupported adjacency format in {path}")

@pytest.fixture(scope="session")
def south_adj(paths):
    """Adjacency for South America."""
    return _load_adj(paths["south_adj"])

@pytest.fixture(scope="session")
def central_adj(paths):
    """Adjacency for Central America."""
    return _load_adj(paths["central_adj"])
