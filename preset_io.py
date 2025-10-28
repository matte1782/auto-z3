# preset_io.py
import yaml

SCHEMA_KEYS = {
    "tautology": {"name","vars","parts"},
    "equivalence": {"name","vars","f1","f2"},
    "inference": {"name","vars","premises","conclusion"},
    "sat": {"name","vars","asserts","get_model","scope"},
    "coloring": {"name","K","nodes","edges"},
    "exactlyone": {"name","vars"},
}

def presets_to_yaml(state_dicts):
    """state_dicts = {
         'tautology': [{'name':..., 'vars':[...], 'parts':[...]}], ... }"""
    return yaml.safe_dump(state_dicts, sort_keys=True, allow_unicode=True)

def yaml_to_presets(yaml_text):
    data = yaml.safe_load(yaml_text)
    if not isinstance(data, dict):
        raise ValueError("YAML malformato: atteso dict di categorie.")
    for cat, items in data.items():
        if cat not in SCHEMA_KEYS:
            raise ValueError(f"Categoria sconosciuta: {cat}")
        if not isinstance(items, list):
            raise ValueError(f"'{cat}' deve essere una lista di voci.")
        for it in items:
            miss = SCHEMA_KEYS[cat] - set(it.keys())
            if miss:
                raise ValueError(f"Voce '{cat}' incompleta: mancano {sorted(miss)}")
    return data

def merge_presets(session, new_data):
    """Mette in session_state i nuovi preset, sovrascrivendo per 'name'."""
    for cat, items in new_data.items():
        bucket = session.setdefault(f"usr_{cat}", [])
        existing_names = {x["name"]: i for i,x in enumerate(bucket)}
        for it in items:
            name = it["name"]
            if name in existing_names:
                bucket[existing_names[name]] = it
            else:
                bucket.append(it)
