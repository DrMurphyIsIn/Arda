"""Weil-form enclosure emitter (MIRRORMERE W3c value certificate): certificate, refusals,
pipeline, registry wiring, and the Arb backend's anchor gate.

The emitted theorem is the rational implication `lo <= W -> W <= hi -> 0 < W and W <= hi`; the
Lean kernel is the arbiter (the generated file compiles against bare Mathlib).  These are the
pre-CI self-checks: the three honest refusals, byte-stable rendering, full registry wiring, and
-- when python-flint is available -- that the Arb backend's closed forms still agree with the
DEFINING integrals of `WeilExplicit.autocorr` / `weilKernel` and with the independent zero-side
reading.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    WeilFormEnclosureEmitter,
    certify,
    emit,
    weil_form_certificate,
    weil_form_family,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_weil_form_enclosure import WeilFormData  # noqa: E402


# --- registry wiring --------------------------------------------------------

def test_kind_is_weil_form_enclosure():
    fam = weil_form_family("T", GridSpec([("case", [0])]), lambda pt: "t", spec=lambda pt: None)
    assert fam.kind == "weil_form_enclosure"


def test_emitter_for_round_trips():
    assert emitter_for("weil_form_enclosure").kind == "weil_form_enclosure"


def test_emitter_is_classified_and_has_adapter():
    from telperion.emitter_sensitivity import REGISTRY
    from telperion.negative_control_harness import ADAPTERS
    assert "WeilFormEnclosureEmitter" in REGISTRY
    assert "WeilFormEnclosureEmitter" in ADAPTERS


# --- the certificate and its refusals ---------------------------------------

def _data(lo, hi, **kw):
    return WeilFormData(label="t", lo=sp.Rational(lo), hi=sp.Rational(hi), **kw)


def test_positive_enclosure_certifies():
    cert = weil_form_certificate(_data("1.57", "1.58"))
    assert cert.sign == "pos"
    assert cert.margin > 0


def test_negative_enclosure_certifies_as_negative():
    cert = weil_form_certificate(_data("-2", "-1"))
    assert cert.sign == "neg"
    assert cert.margin > 0


def test_refuses_straddling_enclosure():
    with pytest.raises(ValueError, match="straddles zero"):
        weil_form_certificate(_data("-1/1000", "1/1000"))


def test_refuses_inconsistent_enclosure():
    with pytest.raises(ValueError, match="inconsistent enclosure"):
        weil_form_certificate(_data(2, 1))


def test_refuses_disjoint_zero_side_reading():
    """The E8 cross-check: a primes-side enclosure disjoint from the zero-side reading of the
    same functional is a normalisation bug, and must abort rather than ship."""
    with pytest.raises(ValueError, match="DISJOINT"):
        weil_form_certificate(_data("1.57", "1.58",
                                    zero_side_lo=sp.Rational(3), zero_side_hi=sp.Rational(4)))


def test_accepts_overlapping_zero_side_reading():
    cert = weil_form_certificate(_data("1.57", "1.58",
                                       zero_side_lo=sp.Rational("1.5705"),
                                       zero_side_hi=sp.Rational("1.5712")))
    assert cert.sign == "pos"


# --- rendering --------------------------------------------------------------

def _render(lo, hi):
    fam = weil_form_family(
        "T", GridSpec([("case", [0])]), lambda pt: "weil_form_t",
        spec=lambda pt: _data(lo, hi),
    )
    report = emit(certify(fam), LeanProfile(namespace=("T",)), [WeilFormEnclosureEmitter()],
                  ValidationReport(checks=(("weil_form_enclosure", True),)))
    return next(iter(report.files.values()))


def test_render_positive_branch():
    text = _render("1.57", "1.58")
    assert "theorem weil_form_t (W : ℝ)" in text
    assert "(0 : ℝ) < W ∧ W ≤" in text
    assert "conjecture1_proved = False" in text
    assert "RH-equivalent" in text


def test_render_negative_branch_is_the_refutation_shape():
    text = _render("-2", "-1")
    assert "W < (0 : ℝ)" in text


def test_render_is_byte_stable():
    assert _render("1.57", "1.58") == _render("1.57", "1.58")


def test_falsifiability_and_membership_faces_are_emitted_text():
    from telperion import weil_form_membership_face_lean, weil_form_neg_refutes_rh_lean
    neg = weil_form_neg_refutes_rh_lean()
    mem = weil_form_membership_face_lean()
    assert "¬ RiemannHypothesis" in neg
    assert "hcrit" in neg and "UNDISCHARGED" in neg
    assert "0 ≤ Wre g" in mem
    assert "conjecture1_proved = False" in neg and "conjecture1_proved = False" in mem


# --- the Arb backend (flint-gated) ------------------------------------------

def test_weil_gauss_anchor_and_enclosure():
    """The backend's anchor gate re-derives the closed forms from the DEFINING integrals; the
    certified enclosure at the first zeta ordinate must be positive, of order one, and must
    contain the independently computed zero-side sum (the E8 identity as a cross-check)."""
    pytest.importorskip("flint")
    pytest.importorskip("mpmath")
    from telperion.weil_gauss import WeilGaussParams, enclose_weil_gauss

    params = WeilGaussParams(a=Fraction(1, 2), omega=Fraction(-141347, 10000),
                             c=Fraction(1, 5), cutoff=500)
    enc = enclose_weil_gauss(params)
    assert enc.lo > 0
    assert enc.hi < 2
    # the independent zero-side reading (first 40 zero pairs) computed once, frozen here
    zero_side = Fraction("1.5708074408343442739")
    assert enc.lo <= zero_side <= enc.hi


def test_weil_gauss_refuses_small_cutoff():
    pytest.importorskip("flint")
    from telperion.weil_gauss import WeilGaussParams, enclose_weil_gauss

    with pytest.raises(ValueError, match="too small for the tail bound"):
        enclose_weil_gauss(WeilGaussParams(a=Fraction(3), omega=Fraction(0), cutoff=10))
