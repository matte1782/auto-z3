from __future__ import annotations

import math
from typing import Dict, List, Tuple

# =============================================================================
# GRAFHI/MAPPE DISPONIBILI
# - Europa (Paesi)   — country-level con confini terrestri principali
# - Italia (Regioni) — 20 regioni
# - Spagna (CCAA)    — 17 comunità (isole senza adiacenze terrestri)
# - Francia (Reg.16) — 13 regioni metropolitane (Corsica isolata)
# - Demo: America Centrale / Sud America
# =============================================================================


# -----------------------------------------------------------------------------#
#  EUROPA (PAESI) — nodi = Paesi, archi = confini terrestri principali
#  Nota: includiamo microstati e UK/IE/NOR/CH ecc. (niente isole senza confini)
# -----------------------------------------------------------------------------#
def europe_countries() -> Dict:
    regions = [
        # Nord/Ovest
        "ISL",
        "IRL",
        "GBR",
        "DNK",
        "NOR",
        "SWE",
        "FIN",
        # Baltici + Est
        "EST",
        "LVA",
        "LTU",
        "POL",
        "BLR",
        "UKR",
        "MDA",
        "RUS",
        # Centro
        "DEU",
        "NLD",
        "BEL",
        "LUX",
        "FRA",
        "CHE",
        "AUT",
        "CZE",
        "SVK",
        "HUN",
        # Sud/Est
        "SVN",
        "HRV",
        "BIH",
        "SRB",
        "MNE",
        "KOS",
        "MKD",
        "ALB",
        "GRC",
        "BGR",
        "ROU",
        "TUR",
        # Sud/Ovest
        "PRT",
        "ESP",
        "AND",
        "MCO",
        "ITA",
        "SMR",
        "VAT",
        "LIE",
    ]
    E = []

    def e(u, v):
        E.append((u, v))

    # Iberia/Francia
    e("PRT", "ESP")
    e("ESP", "FRA")
    e("ESP", "AND")
    e("FRA", "AND")
    e("FRA", "MCO")
    # Benelux / Francia / Germania
    e("FRA", "BEL")
    e("FRA", "LUX")
    e("FRA", "DEU")
    e("BEL", "NLD")
    e("BEL", "DEU")
    e("NLD", "DEU")
    e("LUX", "DEU")
    # Alpi
    e("FRA", "CHE")
    e("FRA", "ITA")
    e("CHE", "DEU")
    e("CHE", "ITA")
    e("CHE", "AUT")
    e("AUT", "DEU")
    e("AUT", "CZE")
    e("AUT", "SVK")
    e("AUT", "HUN")
    e("AUT", "SVN")
    e("ITA", "AUT")
    e("ITA", "SVN")
    e("CHE", "LIE")
    e("AUT", "LIE")
    e("ITA", "SMR")
    e("ITA", "VAT")
    # Balcani
    e("SVN", "HRV")
    e("HRV", "BIH")
    e("HRV", "SRB")
    e("HRV", "MNE")
    e("BIH", "SRB")
    e("SRB", "MNE")
    e("SRB", "KOS")
    e("SRB", "MKD")
    e("SRB", "BGR")
    e("SRB", "ROU")
    e("KOS", "MNE")
    e("KOS", "MKD")
    e("KOS", "ALB")
    e("ALB", "MKD")
    e("ALB", "MNE")
    e("ALB", "GRC")
    e("MKD", "GRC")
    e("MKD", "BGR")
    e("BGR", "GRC")
    e("BGR", "ROU")
    e("BGR", "TUR")
    e("ROU", "UKR")
    e("ROU", "HUN")
    e("ROU", "SRB")
    e("ROU", "MDA")
    # Visegrad/Centro-Est
    e("DEU", "CZE")
    e("CZE", "POL")
    e("CZE", "SVK")
    e("SVK", "POL")
    e("SVK", "UKR")
    e("HUN", "SVK")
    e("HUN", "UKR")
    e("HUN", "ROU")
    e("HUN", "SRB")
    e("HUN", "HRV")
    e("HUN", "SVN")
    # Baltici & Est
    e("POL", "LTU")
    e("POL", "BLR")
    e("POL", "DEU")  # Kaliningrad contatto con POL/ LTU
    e("LTU", "LVA")
    e("LTU", "BLR")
    e("LTU", "RUS")
    e("LVA", "EST")
    e("LVA", "BLR")
    e("EST", "RUS")
    e("FIN", "RUS")
    e("NOR", "RUS")
    e("FIN", "SWE")
    e("SWE", "NOR")
    # Nord/Ovest
    e("DNK", "DEU")
    e("IRL", "GBR")
    # Svizzera conn. ripetute già sopra

    return {"regions": regions, "edges": E}


# -----------------------------------------------------------------------------#
#  ITALIA (REGIONI)
# -----------------------------------------------------------------------------#
def italy_regions() -> Dict:
    R = [
        "PIE",
        "VDA",
        "LIG",
        "LOM",
        "TAA",
        "VEN",
        "FVG",
        "ER",
        "TOS",
        "UMB",
        "MAR",
        "LAZ",
        "ABR",
        "MOL",
        "CAM",
        "PUG",
        "BAS",
        "CAL",
        "SIC",
        "SAR",
    ]
    E = []

    def e(a, b):
        E.append((a, b))

    e("PIE", "VDA")
    e("PIE", "LOM")
    e("PIE", "LIG")
    e("VDA", "LOM")
    e("LIG", "PIE")
    e("LIG", "LOM")
    e("LIG", "ER")
    e("LIG", "TOS")
    e("LOM", "TAA")
    e("LOM", "VEN")
    e("LOM", "ER")
    e("LOM", "LIG")
    e("TAA", "VEN")
    e("VEN", "FVG")
    e("VEN", "ER")
    e("VEN", "LOM")
    e("ER", "VEN")
    e("ER", "LOM")
    e("ER", "LIG")
    e("ER", "TOS")
    e("ER", "MAR")
    e("TOS", "LIG")
    e("TOS", "ER")
    e("TOS", "UMB")
    e("TOS", "MAR")
    e("TOS", "LAZ")
    e("UMB", "MAR")
    e("UMB", "LAZ")
    e("UMB", "TOS")
    e("MAR", "ER")
    e("MAR", "UMB")
    e("MAR", "LAZ")
    e("MAR", "ABR")
    e("LAZ", "TOS")
    e("LAZ", "UMB")
    e("LAZ", "MAR")
    e("LAZ", "ABR")
    e("LAZ", "MOL")
    e("LAZ", "CAM")
    e("ABR", "MAR")
    e("ABR", "LAZ")
    e("ABR", "MOL")
    e("MOL", "ABR")
    e("MOL", "LAZ")
    e("MOL", "CAM")
    e("MOL", "PUG")
    e("CAM", "LAZ")
    e("CAM", "MOL")
    e("CAM", "PUG")
    e("CAM", "BAS")
    e("PUG", "MOL")
    e("PUG", "CAM")
    e("PUG", "BAS")
    e("BAS", "CAM")
    e("BAS", "PUG")
    e("BAS", "CAL")
    # SIC / SAR senza adiacenze terrestri
    return {"regions": R, "edges": E}


# -----------------------------------------------------------------------------#
#  SPAGNA (CCAA)
# -----------------------------------------------------------------------------#
def spain_ccaa() -> Dict:
    R = [
        "GAL",
        "AST",
        "CAN",
        "BAS",
        "NAV",
        "RIO",
        "ARA",
        "CAT",
        "VAL",
        "MUR",
        "AND",
        "CLM",
        "MAD",
        "EXT",
        "CYL",
        "BAL",
        "CNR",
    ]
    E = []

    def e(a, b):
        E.append((a, b))

    e("GAL", "AST")
    e("GAL", "CYL")
    e("AST", "CAN")
    e("AST", "CYL")
    e("CAN", "CYL")
    e("CAN", "BAS")
    e("CAN", "AST")
    e("BAS", "CYL")
    e("BAS", "NAV")
    e("NAV", "RIO")
    e("NAV", "ARA")
    e("NAV", "CYL")
    e("NAV", "BAS")
    e("RIO", "CYL")
    e("RIO", "ARA")
    e("RIO", "NAV")
    e("RIO", "BAS")
    e("ARA", "CAT")
    e("ARA", "VAL")
    e("ARA", "CLM")
    e("ARA", "RIO")
    e("ARA", "NAV")
    e("CAT", "ARA")
    e("CAT", "VAL")
    e("VAL", "CAT")
    e("VAL", "ARA")
    e("VAL", "CLM")
    e("VAL", "MUR")
    e("MUR", "VAL")
    e("MUR", "AND")
    e("MUR", "CLM")
    e("AND", "MUR")
    e("AND", "CLM")
    e("AND", "EXT")
    e("CLM", "MAD")
    e("CLM", "CYL")
    e("CLM", "ARA")
    e("CLM", "VAL")
    e("CLM", "MUR")
    e("CLM", "AND")
    e("CLM", "EXT")
    e("MAD", "CYL")
    e("MAD", "CLM")
    e("EXT", "CYL")
    e("EXT", "CLM")
    e("EXT", "AND")
    e("CYL", "GAL")
    e("CYL", "AST")
    e("CYL", "CAN")
    e("CYL", "BAS")
    e("CYL", "NAV")
    e("CYL", "RIO")
    e("CYL", "ARA")
    e("CYL", "MAD")
    e("CYL", "CLM")
    e("CYL", "EXT")
    # BAL, CNR senza adiacenze terrestri
    return {"regions": R, "edges": E}


# -----------------------------------------------------------------------------#
#  FRANCIA (Regioni 2016)
#  BRE, PDL, NOR, HDF, IDF, CVL, GES, BFC, NAQ, ARA, OCC, PAC, COR
#  (Corsica isolata)
# -----------------------------------------------------------------------------#
def france_regions() -> Dict:
    R = [
        "BRE",
        "PDL",
        "NOR",
        "HDF",
        "IDF",
        "CVL",
        "GES",
        "BFC",
        "NAQ",
        "ARA",
        "OCC",
        "PAC",
        "COR",
    ]
    E = []

    def e(a, b):
        E.append((a, b))

    # Ovest/Nord
    e("BRE", "PDL")
    e("BRE", "NOR")
    e("PDL", "BRE")
    e("PDL", "CVL")
    e("PDL", "NAQ")
    e("NOR", "BRE")
    e("NOR", "HDF")
    e("NOR", "IDF")
    e("NOR", "CVL")
    e("HDF", "NOR")
    e("HDF", "IDF")
    e("HDF", "GES")
    # Centro/Est
    e("IDF", "NOR")
    e("IDF", "HDF")
    e("IDF", "CVL")
    e("IDF", "GES")
    e("CVL", "PDL")
    e("CVL", "NOR")
    e("CVL", "IDF")
    e("CVL", "NAQ")
    e("CVL", "ARA")
    e("CVL", "BFC")
    e("GES", "HDF")
    e("GES", "IDF")
    e("GES", "BFC")
    e("BFC", "GES")
    e("BFC", "CVL")
    e("BFC", "ARA")
    # Sud/Ovest
    e("NAQ", "PDL")
    e("NAQ", "CVL")
    e("NAQ", "ARA")
    e("NAQ", "OCC")
    e("ARA", "BFC")
    e("ARA", "CVL")
    e("ARA", "NAQ")
    e("ARA", "OCC")
    e("ARA", "PAC")
    e("OCC", "NAQ")
    e("OCC", "ARA")
    e("OCC", "PAC")
    e("PAC", "ARA")
    e("PAC", "OCC")
    # COR senza adiacenze terrestri
    return {"regions": R, "edges": E}


# -----------------------------------------------------------------------------#
#  DEMO: America Centrale / Sud America  (coerenti coi tuoi SMT)
# -----------------------------------------------------------------------------#
def central_america() -> Dict:
    regions = ["Bel", "Gua", "ElS", "Hon", "Nic", "CR", "Pan"]
    edges = [
        ("Bel", "Gua"),
        ("ElS", "Hon"),
        ("ElS", "Gua"),
        ("Gua", "Hon"),
        ("Nic", "Hon"),
        ("Nic", "CR"),
        ("Nic", "Pan"),
    ]
    return {"regions": regions, "edges": edges}


def south_america() -> Dict:
    regions = [
        "Ven",
        "Col",
        "Ecu",
        "Per",
        "Guy",
        "Sur",
        "FGu",
        "Bra",
        "Bol",
        "Par",
        "Uru",
        "Arg",
        "Chi",
    ]
    edges = [
        ("Guy", "Ven"),
        ("Guy", "Bra"),
        ("Guy", "Sur"),
        ("Ven", "Col"),
        ("Ven", "Bra"),
        ("Bra", "Sur"),
        ("FGu", "Sur"),
        ("FGu", "Bra"),
        ("Col", "Ecu"),
        ("Col", "Per"),
        ("Col", "Bra"),
        ("Per", "Ecu"),
        ("Per", "Bra"),
        ("Per", "Bol"),
        ("Per", "Chi"),
        ("Bra", "Bol"),
        ("Par", "Bol"),
        ("Par", "Arg"),
        ("Arg", "Bol"),
        ("Chi", "Bol"),
        ("Bra", "Arg"),
        ("Bra", "Par"),
        ("Bra", "Uru"),
        ("Arg", "Chi"),
        ("Arg", "Uru"),
    ]
    return {"regions": regions, "edges": edges}


# =============================================================================
#  CATALOGO
# =============================================================================

CATALOG = {
    # Nome visibile -> (graph_fn, svg_fn)
    "Europa (Paesi)": (europe_countries, "svg_auto"),
    "Italia (Regioni)": (italy_regions, "svg_auto"),
    "Spagna (CCAA)": (spain_ccaa, "svg_auto"),
    "Francia (Regioni 2016)": (france_regions, "svg_auto"),
    "America Centrale (demo)": (central_america, "central_svg"),
    "Sud America (demo)": (south_america, "south_svg"),
}

# =============================================================================
#  SVG GENERATORS
#  - svg_auto: layout radiale elegante, id = nome regione (cliccabili)
#  - central_svg / south_svg: demo a rettangoli (come prima)
# =============================================================================


def svg_auto(graph: Dict, radius_step: int = 130) -> str:
    """Auto-layout radiale con transizioni morbide e hover pulito."""
    nodes = graph["regions"]
    N = len(nodes)
    # Disporre su due corone se tanti nodi
    inner = max(1, min(10, math.ceil(N / 2)))
    outer = N - inner
    w = 1200 if N > 14 else 900
    h = 800 if N > 14 else 600

    def polar(cx, cy, r, ang):
        return (cx + r * math.cos(ang), cy + r * math.sin(ang))

    cx, cy = w / 2, h / 2
    coords = {}
    # anello interno
    for i, name in enumerate(nodes[:inner]):
        ang = 2 * math.pi * (i / inner)
        x, y = polar(cx, cy, radius_step, ang)
        coords[name] = (x, y)
    # anello esterno
    for j, name in enumerate(nodes[inner:]):
        ang = 2 * math.pi * (j / max(1, outer))
        x, y = polar(cx, cy, 2 * radius_step, ang)
        coords[name] = (x, y)

    # edges (linee sottili)
    edges = graph["edges"]
    line_svg = []
    for u, v in edges:
        x1, y1 = coords[u]
        x2, y2 = coords[v]
        line_svg.append(
            f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="#d7dbe2" stroke-width="1.2" />'
        )

    # nodi
    nodes_svg = []
    for name, (x, y) in coords.items():
        nodes_svg.append(
            f'<g id="{name}" class="region" transform="translate({x - 40:.1f},{y - 20:.1f})">'
            f'  <rect width="80" height="40" rx="9" fill="#f6f7f9" stroke="#23272f" stroke-width="1.1"/>\n'
            f'  <text x="40" y="24" text-anchor="middle" font-family="ui-sans-serif,system-ui" '
            f'        font-size="12" fill="#2b2f36">{name}</text>'
            f"</g>"
        )

    return f"""
<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}">
  <style>
    .region {{ cursor: pointer; transition: transform .25s ease, opacity .25s ease; }}
    .region:hover {{ transform: translate(-40px,-20px) scale(1.04); }}
    text {{ user-select: none; }}
  </style>
  <g opacity="1.0">{"".join(line_svg)}</g>
  <g>{"".join(nodes_svg)}</g>
</svg>
""".strip()


# --- demo svg a scatole piatte (come prima) ----------------------------------


def central_svg() -> str:
    boxes = {
        "Bel": (10, 40),
        "Gua": (120, 40),
        "ElS": (230, 10),
        "Hon": (230, 70),
        "Nic": (340, 40),
        "CR": (450, 40),
        "Pan": (560, 40),
    }
    return _svg_from_boxes("650", "140", boxes)


def south_svg() -> str:
    boxes = {
        "Guy": (40, 10),
        "Sur": (140, 10),
        "FGu": (240, 10),
        "Ven": (40, 120),
        "Col": (140, 120),
        "Ecu": (240, 120),
        "Bra": (370, 120),
        "Per": (240, 230),
        "Bol": (370, 230),
        "Chi": (480, 230),
        "Par": (370, 340),
        "Arg": (480, 340),
        "Uru": (590, 340),
    }
    return _svg_from_boxes("700", "440", boxes)


def _svg_from_boxes(w: str, h: str, boxes: Dict[str, Tuple[int, int]]) -> str:
    rects = []
    for region, (x, y) in boxes.items():
        rects.append(
            f'<rect id="{region}" x="{x}" y="{y}" width="90" height="50" rx="8" '
            f'stroke="#222" stroke-width="1.2" fill="#f2f2f2" class="region"/>'
        )
    rects_svg = "\n  ".join(rects)
    return f"""
<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}">
  <style>
    .region {{
      cursor: pointer; transition: fill .35s ease, stroke .35s ease;
    }}
    .region:hover {{ stroke: #555; stroke-width: 2; }}
  </style>
  {rects_svg}
</svg>
""".strip()


# =============================================================================
#  HELPERS PUBBLICI
# =============================================================================


def list_countries() -> List[str]:
    return list(CATALOG.keys())


def get_graph(country_label: str) -> Dict:
    fn, _ = CATALOG[country_label]
    return fn()


def get_svg(country_label: str) -> str:
    _, svgname = CATALOG[country_label]
    # svg_auto richiede il grafo per disporre i nodi
    if svgname == "svg_auto":
        return svg_auto(get_graph(country_label))
    return globals()[svgname]()  # funzioni central/south demo
