# tests/rh_jensen/test_jensen.py
from fractions import Fraction
from telperion.rh_jensen.jensen import jensen_coeff_box, disc2_margin


def test_binomial_scaling():
    box = jensen_coeff_box(n=0, d=2, prec_bits=200)
    assert len(box) == 3  # c0, c1, c2 with weights C(2,0)=1, C(2,1)=2, C(2,2)=1


def test_d2_turan_margin_positive_small_n():
    # The Riemann xi Turan inequalities alpha(n+1)^2 >= alpha(n) alpha(n+2)
    # hold for all n (classical). Margin must certify positive at n = 0.
    box = jensen_coeff_box(n=0, d=2, prec_bits=300)
    m = disc2_margin(box)
    assert m > 0


def test_margin_is_lower_bound():
    # Margin must not exceed the midpoint discriminant (it is a guaranteed lower bound).
    box = jensen_coeff_box(n=1, d=2, prec_bits=300)
    m = disc2_margin(box)
    c0 = (box[0][0] + box[0][1]) / 2
    c1 = (box[1][0] + box[1][1]) / 2
    c2 = (box[2][0] + box[2][1]) / 2
    assert m <= c1 * c1 - c0 * c2
