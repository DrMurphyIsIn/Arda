"""BG R7 ledger-floor facets — m=0 (childless), m>=4 (collapse), and tax windows.

Completes the context-free floor layer: point `norm_num` facts for the childless
(m=0) and collapse-tail (m>=4) classes, and Bernstein positivities for the six tax
windows + below-window shapes.  These tests check every fact holds, ties each point
fact to the BG kernel's own certifier (faithfulness), validates the rational
brackets, and refuses a too-high floor.
"""
import importlib.util
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1].parent / "proof" / "verification"))

import g1_floor_certificates as G  # noqa: E402
from telperion import (  # noqa: E402
    BernsteinEmitter, ValidationReport, certify, emit, find_bernstein_certificate,
)
from telperion.emit_bernstein import bernstein_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_Y = sp.Symbol("y")


def _mod():
    gen = Path(__file__).resolve().parents[1] / "examples" / "bg_floor_r7_facets" / "generate.py"
    spec = importlib.util.spec_from_file_location("bgr7_gen", gen)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_all_point_facts_are_nonnegative():
    facts = _mod()._point_facts()
    assert len(facts) == 17 + 23  # m=0: 9 bareleaf + 7 nl2 + 1 tax(1,1,0); m>=4: 6+10+7
    for name, expr_s, val, comment in facts:
        assert val >= 0, (name, float(val))


def test_point_facts_match_the_kernel_certifier():
    # faithfulness: the BG kernel's own certify_floor_m0 / certify_collapse_m_ge_4 agree.
    from fractions import Fraction as Fr
    for a in range(1, 10):
        assert G.certify_floor_m0(a, 1, Fr(26, 500))
    for a in range(0, 7):
        assert G.certify_floor_m0(a, 2, Fr(54, 500))
    assert G.certify_floor_m0(1, 1, Fr(52, 1000))
    for a in range(1, 7):
        assert G.certify_collapse_m_ge_4(a, 0, Fr(27, 5000))
    for a in range(0, 10):
        assert G.certify_collapse_m_ge_4(a, 1, Fr(26, 500))
    for a in range(0, 7):
        assert G.certify_collapse_m_ge_4(a, 2, Fr(54, 500))


def test_every_window_cell_bernstein_certifies():
    cells = _mod()._window_specs()
    assert len(cells) >= 15                    # 5 tax shapes (1-4 cells) + 2 below-window
    for name, num, lo, hi in cells:
        assert find_bernstein_certificate(num, lo, hi, _Y, n_max=18) is not None, name


def test_window_taxonomy():
    names = {c[0] for c in _mod()._window_specs()}
    assert any("taxwin_a2_nl0_m1" in n for n in names)   # the tight (2,0,1) shape
    assert any("taxwin_a0_nl1_m1" in n for n in names)   # (0,1,1)
    assert any("belowwin_m2" in n for n in names) and any("belowwin_m3" in n for n in names)


def test_rational_brackets_are_valid():
    import math
    assert float(G.L_LO) <= math.log(621 / 64) / 11
    assert float(G.G_HI) >= math.log(3 / 2)
    # log1p_upper is a genuine upper bound at the anchors it uses
    from fractions import Fraction as Fr
    for u in (Fr(4, 9), Fr(1, 4), Fr(2, 5)):
        assert float(G.log1p_upper(u)) >= math.log(1 + float(u)) - 1e-12


def test_too_high_a_window_floor_is_refused():
    mod = _mod()
    from fractions import Fraction as Fr
    # the tight (2,0,1) tax shape at a 10x floor -> refused
    def yr(a, nl, m):
        k = a + nl + m
        ls, hs = Fr(1) / (G.T_HI + Fr(29, 1000)), Fr(1) / (G.T_LO - Fr(29, 1000))
        return (max(Fr(1, 10**6), (ls - (k + 1) - Fr(a, 3) - nl) / m),
                min(Fr(1, 2), (hs - (k + 1) - Fr(a, 3) - nl) / m))
    ylo, yhi = yr(2, 0, 1)
    cells = mod._window_cells(2, 0, 1, mod._rat(ylo), mod._rat(yhi), Fr(99, 500))  # 10x too high
    num, lo, hi = cells[0]
    fam = bernstein_family("FalseWin", (_Y,), GridSpec([("_", [0])]),
                           lambda pt: "false_win", spec=lambda pt: (num, lo, hi), n_max=20)
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a window floor 10x above the true minimum must be refused"


def test_emit_is_lint_clean_and_idempotent_with_heartbeats():
    mod = _mod()
    text = mod.build()
    assert "norm_num" in text and "ring" in text and "linarith" in text
    assert "nlinarith" not in text
    assert "R3Cert.R7CollapseMono.g_mono" in text or "g_mono" in text   # documents the collapse brick
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert mod.main(check=True) == 0


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "BernsteinEmitter" in REGISTRY
