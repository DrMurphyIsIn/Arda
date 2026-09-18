"""Routes-roadmap D2 certificate tools: `weil_form_enclosure` + `interval_gram_inertia`.

These are the two emitters built for the MIRRORMERE node `MM_weil_gram_trace` (design memo
`telperion/docs/MM_mm-d2-weil-gram-trace_DESIGN_2026-09-18.md`).  The tests cover the exact
rational arithmetic, every documented REFUSAL (the honest-refusal contract is the emitters'
negative control at certify time), and the shape of the emitted Lean.

No RH content is exercised or claimed anywhere here.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion.emit_weil_form_enclosure import (  # noqa: E402
    PrimeTermInterval,
    WeilFormData,
    WeilFormEnclosureEmitter,
    _prime_powers_up_to,
    gram_entry_intervals,
    weil_form_enclosure_certificate,
)
from telperion.emit_interval_gram_inertia import (  # noqa: E402
    GramInertiaData,
    IntervalGramInertiaEmitter,
    IntervalHermitian,
    interval_gram_inertia_certificate,
)


class _Fam:
    """Minimal stand-in for a CertifiedFamily: the emitters read only `.instances`."""

    def __init__(self, instances):
        self.instances = instances


class _Inst:
    def __init__(self, name, payload):
        self.lean_name = name
        self.payload = payload


def _q(x):
    return sp.Rational(x)


# --------------------------------------------------------------------------- #
# weil_form_enclosure
# --------------------------------------------------------------------------- #

def test_prime_powers_up_to():
    assert _prime_powers_up_to(20) == [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19]
    assert _prime_powers_up_to(1) == []


def _data(**kw):
    """A support radius R = 3/2 family: exp(3/2) = 4.48..., so n in {2, 3, 4}."""
    base = dict(
        label="0,0",
        support_radius=_q("3/2"),
        arch_lo=_q("11/10"),
        arch_hi=_q("6/5"),
        terms=(
            PrimeTermInterval(2, _q("1/10"), _q("11/100")),
            PrimeTermInterval(3, _q("1/20"), _q("6/100")),
            PrimeTermInterval(4, _q("1/40"), _q("3/100")),
        ),
    )
    base.update(kw)
    return WeilFormData(**base)


def test_fold_is_exact_and_entry_interval_is_derived():
    cert = weil_form_enclosure_certificate(_data())
    assert cert.prime_lo == _q("1/10") + _q("1/20") + _q("1/40")
    assert cert.prime_hi == _q("11/100") + _q("6/100") + _q("3/100")
    # entry interval = [archLo - primeHi, archHi - primeLo]
    assert cert.lo == _q("11/10") - cert.prime_hi
    assert cert.hi == _q("6/5") - cert.prime_lo
    assert cert.lo <= cert.hi
    assert cert.width == cert.hi - cert.lo


def test_refuses_incomplete_prime_power_list():
    bad = _data(terms=(PrimeTermInterval(2, _q("1/10"), _q("11/100")),
                       PrimeTermInterval(4, _q("1/40"), _q("3/100"))))
    with pytest.raises(ValueError, match="complete set of prime powers"):
        weil_form_enclosure_certificate(bad)


def test_refuses_inverted_intervals_and_bad_radius():
    with pytest.raises(ValueError, match="inverted archimedean interval"):
        weil_form_enclosure_certificate(_data(arch_lo=_q(2), arch_hi=_q(1)))
    with pytest.raises(ValueError, match="support radius"):
        weil_form_enclosure_certificate(_data(support_radius=_q(0)))
    bad = _data(terms=(PrimeTermInterval(2, _q("11/100"), _q("1/10")),
                       PrimeTermInterval(3, _q("1/20"), _q("6/100")),
                       PrimeTermInterval(4, _q("1/40"), _q("3/100"))))
    with pytest.raises(ValueError, match="inverted term interval"):
        weil_form_enclosure_certificate(bad)


def test_emitted_lean_carries_fold_and_enclosure():
    cert = weil_form_enclosure_certificate(_data())
    body, n = WeilFormEnclosureEmitter().emit_body(_Fam([_Inst("wf_00", cert)]), profile=None)
    assert n == 2
    assert "theorem wf_00_fold" in body and "norm_num" in body
    assert "theorem wf_00 (arch prime : ℝ)" in body and "linarith" in body
    assert "conjecture1_proved = False" in body
    # the fold theorem must SPELL OUT the summands (that is what makes it corruptible)
    assert "(1 / 10) + (1 / 20) + (1 / 40)" in body


def test_gram_entry_intervals_handoff():
    cert = weil_form_enclosure_certificate(_data())
    got = gram_entry_intervals([cert])
    assert got["0,0"] == (cert.lo, cert.hi)


# --------------------------------------------------------------------------- #
# interval_gram_inertia
# --------------------------------------------------------------------------- #

def _herm2(d0=("1/10", "2/10"), d1=("1/10", "2/10"), re=("-1/10", "1/10"),
           im=("-1/10", "1/10")):
    return IntervalHermitian(
        k=2,
        diag=((_q(d0[0]), _q(d0[1])), (_q(d1[0]), _q(d1[1]))),
        off={(0, 1): ((_q(re[0]), _q(re[1])), (_q(im[0]), _q(im[1])))},
    )


def test_negative_direction_coefficients_and_box_max():
    # Diagonal in [-1, -1/2]; off-diagonal tiny.  Witness x = (1, 0) sees a00 only.
    m = _herm2(d0=("-1", "-1/2"), d1=("-1", "-1/2"), re=("-1/100", "1/100"),
               im=("-1/100", "1/100"))
    cert = interval_gram_inertia_certificate(
        GramInertiaData(label="neg", matrix=m, mode="negative",
                        witness=((_q(1), _q(0)), (_q(0), _q(0)))))
    assert cert.diag_coeff == (_q(1), _q(0))
    assert cert.box_max == _q("-1/2")
    assert cert.margin == _q("1/2")


def test_negative_direction_uses_the_off_diagonal_conjugation_convention():
    # x = (1, i): alpha_01 = 2 Re(conj 1 * i) = 0, beta_01 = -2 Im(conj 1 * i) = -2.
    m = _herm2(d0=("-1", "-1/2"), d1=("-1", "-1/2"), re=("-1/100", "1/100"),
               im=("-1/100", "1/100"))
    cert = interval_gram_inertia_certificate(
        GramInertiaData(label="neg2", matrix=m, mode="negative",
                        witness=((_q(1), _q(0)), (_q(0), _q(1)))))
    (i, j, alpha, beta) = cert.off_coeff[0]
    assert (i, j) == (0, 1)
    assert alpha == _q(0)
    assert beta == _q(-2)
    # box max: -1/2 - 1/2 + |beta| * 1/100 = -1 + 1/50
    assert cert.box_max == _q(-1) + _q("1/50")


def test_refuses_zero_witness_and_nonnegative_box_max():
    m = _herm2()
    with pytest.raises(ValueError, match="zero witness"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="z", matrix=m, mode="negative",
                            witness=((_q(0), _q(0)), (_q(0), _q(0)))))
    with pytest.raises(ValueError, match="does not force a negative direction"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="p", matrix=m, mode="negative",
                            witness=((_q(1), _q(0)), (_q(0), _q(0)))))


def test_dominance_moduli_and_row_slack():
    m = _herm2(d0=("3/10", "4/10"), d1=("3/10", "4/10"), re=("-1/10", "1/10"),
               im=("-1/10", "1/10"))
    cert = interval_gram_inertia_certificate(
        GramInertiaData(label="dom", matrix=m, mode="dominance"))
    (i, j, mij) = cert.moduli[0]
    assert (i, j) == (0, 1)
    # m_01^2 must dominate (1/10)^2 + (1/10)^2 = 1/50, exactly checked
    assert mij ** 2 >= _q("1/50")
    assert all(s > 0 for s in cert.row_slack)


def test_refuses_non_dominant_row_and_nonpositive_diagonal():
    thin = _herm2(d0=("1/100", "2/100"), d1=("3/10", "4/10"))
    with pytest.raises(ValueError, match="not strictly dominant"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="thin", matrix=thin, mode="dominance"))
    neg = _herm2(d0=("-1", "1"), d1=("3/10", "4/10"))
    with pytest.raises(ValueError, match="not positive"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="neg", matrix=neg, mode="dominance"))


def test_refuses_missing_off_diagonal_and_bad_mode():
    bare = IntervalHermitian(k=2, diag=((_q(1), _q(2)), (_q(1), _q(2))), off={})
    with pytest.raises(ValueError, match="missing off-diagonal enclosures"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="bare", matrix=bare, mode="dominance"))
    with pytest.raises(ValueError, match="unknown mode"):
        interval_gram_inertia_certificate(
            GramInertiaData(label="x", matrix=_herm2(), mode="posdef"))


def test_emitted_lean_shapes():
    m = _herm2(d0=("-1", "-1/2"), d1=("-1", "-1/2"), re=("-1/100", "1/100"),
               im=("-1/100", "1/100"))
    neg = interval_gram_inertia_certificate(
        GramInertiaData(label="neg", matrix=m, mode="negative",
                        witness=((_q(1), _q(0)), (_q(0), _q(0)))))
    body, n = IntervalGramInertiaEmitter().emit_body(_Fam([_Inst("gi_neg", neg)]), profile=None)
    assert n == 1
    assert "theorem gi_neg (a00 a11 a01 b01 : ℝ)" in body
    assert "linarith" in body and "≤ (-(1 / 2))" in body
    # no PosDef / posIndex / defect claim is ever emitted IN THE THEOREM (the comment block
    # explains what is deliberately NOT claimed, so only the declaration is checked)
    decl = body[body.index("theorem gi_neg"):]
    assert "PosDef" not in decl and "posIndex" not in decl and "defect" not in decl

    dom_m = _herm2(d0=("3/10", "4/10"), d1=("3/10", "4/10"))
    dom = interval_gram_inertia_certificate(
        GramInertiaData(label="dom", matrix=dom_m, mode="dominance"))
    body2, n2 = IntervalGramInertiaEmitter().emit_body(_Fam([_Inst("gi_dom", dom)]), profile=None)
    assert n2 == 1
    assert "nlinarith" in body2
    assert "a01 ^ 2 + b01 ^ 2 ≤" in body2
    decl2 = body2[body2.index("theorem gi_dom"):]
    assert "PosDef" not in decl2 and "posIndex" not in decl2 and "defect" not in decl2


def test_kind_round_trip_through_the_certify_registry():
    from telperion.certify import emitter_for
    assert emitter_for("weil_form_enclosure").kind == "weil_form_enclosure"
    assert emitter_for("interval_gram_inertia").kind == "interval_gram_inertia"
