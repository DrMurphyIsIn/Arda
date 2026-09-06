"""Tests for complex Arb enclosure of Lambda(s) = pi^(-s/2) * Gamma(s/2) * zeta(s).

Lambda zeros are exactly the nontrivial zeros of the Riemann zeta function.
Box membership is a documented NON-KERNEL input: Arb ball arithmetic is
internally certified; Lean does not independently verify the value.
conjecture1_proved = False.
"""
from fractions import Fraction
import mpmath
from telperion.arb_enclosure import enclose_acb, enclose_lambda


def _c(box, val):  # val real float, box=(lo,hi)
    return float(box[0]) <= val <= float(box[1])


def _lambda_oracle(sre, sim):
    mpmath.mp.dps = 60
    s = mpmath.mpf(str(sre)) + 1j*mpmath.mpf(str(sim))
    return mpmath.power(mpmath.pi, -s/2) * mpmath.gamma(s/2) * mpmath.zeta(s)


def test_lambda_on_line_is_real_and_encloses_oracle():
    # Lambda(1/2 + i*14) : known to be near a zero region; imag part must be ~0
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    o = _lambda_oracle(0.5, 14)
    assert _c((lo_re, hi_re), float(o.real))
    assert lo_im <= 0 <= hi_im   # imaginary part boxes zero on the line
    assert _c((lo_im, hi_im), float(o.imag))


def test_complex_point_encloses_oracle():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(3, 5), 20, prec_bits=300)
    o = _lambda_oracle(0.6, 20)
    assert _c((lo_re, hi_re), float(o.real)) and _c((lo_im, hi_im), float(o.imag))


def test_width_shrinks_with_precision():
    b1 = enclose_lambda(Fraction(1, 2), 14, prec_bits=120)
    b2 = enclose_lambda(Fraction(1, 2), 14, prec_bits=300)
    assert (b2[0][1] - b2[0][0]) < (b1[0][1] - b1[0][0])


def test_returns_fractions():
    (lo_re, hi_re), (lo_im, hi_im) = enclose_lambda(Fraction(1, 2), 21, prec_bits=200)
    assert all(isinstance(x, Fraction) for x in (lo_re, hi_re, lo_im, hi_im))
