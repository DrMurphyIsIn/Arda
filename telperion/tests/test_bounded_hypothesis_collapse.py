"""BoundedHypothesisCollapse emitter (kind ``bounded_hypothesis_collapse``) --
the statement-SHAPE triviality certificate.

Audits the shape ``exists C >= 0, forall T >= T0, P T -> -(C log T / T^k) <= W``
and emits the collapse witness: the explicit constant ``max 0 (-W) * B^k / log T0``
closes it for every ``W``, every hypothesis family ``P`` and every finite height
``B`` above which ``P`` fails -- so the shape carries no content.  Built during the
MIRRORMERE D3 statement-authoring pass (node ``MM_weil_form_certified_height``);
the emitted Lean was compiled against Mathlib v4.32.0 and is axiom-clean
(``[propext, Classical.choice, Quot.sound]``).
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.certify import CertifiedInstance  # noqa: E402
from telperion.emit_bounded_hypothesis_collapse import (  # noqa: E402
    BoundedHypothesisCollapseEmitter,
    bounded_hypothesis_collapse_certificate,
    bounded_hypothesis_collapse_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402


# --------------------------------------------------------------------------- #
# certificate: acceptance                                                      #
# --------------------------------------------------------------------------- #

def test_certificate_accepts_the_d3_headline_shape():
    """(T0, k) = (2, 1) -- the shape proposed for the D3 node -- with three
    adversarial samples, including the ladder's real certified height 640000."""
    cert = bounded_hypothesis_collapse_certificate(
        2, 1, [(-3, 100, 50), (-1, 10, 2), (sp.Rational(-1, 7), 640000, 100)])
    assert cert.T0 == 2 and cert.k == 1
    assert len(cert.samples) == 3
    for W, B, T, C_star, margin in cert.samples:
        assert W < 0 and cert.T0 <= T <= B
        # the constant is max(0, -W) * B^k / log T0 = -W * B^k / log T0 for W < 0
        assert sp.simplify(C_star - (-W) * B ** cert.k / sp.log(cert.T0)) == 0
        # and it closes the shape at the probe height, with slack
        assert float(margin.evalf(40)) >= 0


def test_sharper_exponent_also_collapses():
    """The collapse is not an artifact of the weak exponent k = 1."""
    cert = bounded_hypothesis_collapse_certificate(2, 3, [(-3, 100, 50)])
    assert cert.k == 3
    assert float(cert.samples[0][4].evalf(40)) >= 0


# --------------------------------------------------------------------------- #
# certificate: the refusals (negative controls)                                #
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("args, needle", [
    ((2, 0, [(-1, 10, 2)]), "decaying error"),        # no decay: not this family
    ((2, -1, [(-1, 10, 2)]), "decaying error"),
    ((1, 1, [(-1, 10, 2)]), "T0 > 1"),                # log T0 = 0
    ((sp.Rational(1, 2), 1, [(-1, 10, 2)]), "T0 > 1"),
    ((2, 1, [(-1, 1, 1)]), "EMPTY"),                  # B < T0: vacuity, not collapse
    ((2, 1, [(1, 10, 2)]), "benign"),                 # W >= 0 collapses by C := 0
    ((2, 1, [(0, 10, 2)]), "benign"),
    ((2, 1, [(-1, 10, 50)]), "outside"),              # probe height out of range
    ((2, 1, []), "no samples"),
])
def test_refusals(args, needle):
    with pytest.raises(ValueError) as exc:
        bounded_hypothesis_collapse_certificate(*args)
    assert needle in str(exc.value)


# --------------------------------------------------------------------------- #
# emission                                                                     #
# --------------------------------------------------------------------------- #

def _emit(T0, k, samples, name="collapse_witness"):
    cert = bounded_hypothesis_collapse_certificate(T0, k, samples)
    inst = CertifiedInstance(point={}, lean_name=name, corners=(), payload=cert)

    class _Fam:
        instances = [inst]

    return BoundedHypothesisCollapseEmitter().emit_body(_Fam(), LeanProfile())


def test_emits_one_theorem_carrying_the_explicit_constant():
    body, n = _emit(2, 1, [(-3, 100, 50)])
    assert n == 1
    assert "theorem collapse_witness" in body
    # the collapsing constant is IN the statement: that is the corruptible certificate
    assert "max 0 (-W) * B ^ 1 / Real.log 2" in body
    # the audited shape is quantified over an ARBITRARY hypothesis family
    assert "(Pr : ℝ → Prop)" in body
    assert "hfail : ∀ T : ℝ, B < T → ¬ Pr T" in body
    # and the honesty line is present
    assert "conjecture1_proved = False" in body
    assert "Refutes a SHAPE, not a theorem" in body
    assert lint_lean_text(body) == []


def test_exponent_appears_in_every_power_slot():
    body, _ = _emit(2, 3, [(-3, 100, 50)])
    assert "B ^ 3 / Real.log 2" in body
    assert "T ^ 3" in body
    assert "B ^ 1" not in body


def test_family_dispatches_through_the_special_hook():
    fam = bounded_hypothesis_collapse_family(
        "ShapeAuditTest", GridSpec([("k", [1])]),
        lambda pt: "shape_audit_test",
        lambda pt: (2, 1, [(-1, 10, 2)]))
    assert fam.kind == "bounded_hypothesis_collapse"
    T0, k, samples = fam.special[1]({"k": 1})
    assert (T0, k) == (2, 1) and len(samples) == 1
