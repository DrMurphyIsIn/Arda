"""Stage II exponent system of OpenAI's 7/8 half-plane (paper1 §§10, 12, 19, 20), as a symbolic model.

Part A (this file): exact-rational reproduction of every certificate in §20 at the paper's values,
using the closed forms the Lean file Endpoint.lean also uses. Part B (stage3_search.py) varies the
boundary and the geometry. conjecture1_proved = False.
"""
from fractions import Fraction as Fr
import sympy as sp

# ---- the paper's fixed data (eq. 12.1-12.4, 20.4) ----------------------------------------------
sigma0 = Fr(7, 8)
b, h, ell, lx, ly = Fr(1, 8), Fr(13, 16), Fr(1, 6), Fr(17, 48), Fr(23, 48)
z0 = Fr(17, 50)          # the Re z contour (eq. 20.4, 16.15)
alpha = Fr(5, 6)         # bin ceiling kappa <= 5/6 at Stage II (12.1-12.2)
assert h == 1 - lx + ell and ly == lx + b and lx + ly + ell == 1
C_at_sigma0 = sigma0 + lx / 2 - 1 + h / 6           # Lemma 10.4 proof: C(sigma0) = sigma0 + lx/2 - 1 + h/6
assert C_at_sigma0 == Fr(3, 16)                      # = C(7/8) with C(s) = s - 11/16

def E(d, a, q, R, *, sigma0=sigma0, h=h, ell=ell, ly=ly, z0=z0):
    """Eq. (20.4) / (10.15) with g = q*ell: scale exponent of a row bin relative to C(sigma0)."""
    delta = 2 * a - 1
    return a - sigma0 + h * (z0 - Fr(1, 6)) - a * ly - (1 - a) * ell - (delta / 2 - q) * ell + d * (R + delta / 2 - z0)

def E_second_form(d, a, q, R, h=h, z0=z0):
    delta = 2 * a - 1
    C0 = Fr(-1, 48)
    return C0 + Fr(2, 3) * delta + q / 6 - h * (1 - R) + (d - h) * (R + delta / 2 - z0)

# ---- Prop. 19.2 row counts (Lean Endpoint.lean closed forms) -----------------------------------
def Dx(x):  return 3 - Fr(17, 9) * x                       # = (37 + 34 y)/18, y = 1/2 - x
def Px(x):  y = Fr(1, 2) - x; return (7 + 18 * y + 8 * y ** 2) / 9
def J(delta, x, alpha=alpha):  return (alpha - delta) * Dx(x) + delta * Px(x)        # (20.8)
def t_bal(delta, x, alpha=alpha):  return 1 + delta * Px(x) / (2 * J(delta, x, alpha))
def R_short(t, delta, x):  return 1 - delta + delta * Px(x) / Dx(x) * (Fr(3, 2) - t)   # (19.3)
def L(t, delta, alpha=alpha):  return 1 - delta + (alpha - delta) * (t - 1)            # (19.4)
def R_star(delta, x, alpha=alpha):
    t = t_bal(delta, x, alpha)
    rs, l = R_short(t, delta, x), L(t, delta, alpha)
    assert rs == l, (rs, l)                                   # t balances the two counts (20.8)
    return l

# ---- reproduce the certificates -----------------------------------------------------------------
def check():
    # (20.4): the two displayed forms agree identically
    d, a, q, R = sp.symbols('d a q R')
    e1 = sp.nsimplify(E(d, a, q, R)); e2 = sp.nsimplify(E_second_form(d, a, q, R))
    assert sp.simplify(e1 - e2) == 0
    # (20.5): floor bin a = 51/100, R = 1, q <= delta0/2
    delta0 = Fr(1, 50); a0 = Fr(51, 100)
    assert E(h, a0, delta0 / 2, 1) == Fr(-7, 1200)
    # (20.7): live endpoint delta = alpha, R = 1 - delta, q <= delta/2 -> -1/48 - delta/16
    a1 = (1 + alpha) / 2
    assert E(h, a1, alpha / 2, 1 - alpha) == Fr(-1, 48) - alpha / 16
    # (20.6): d-independent small-row part
    assert h * (z0 - Fr(1, 6)) - ly / 2 == Fr(-79, 800)
    # Lemma 20.2: -E_* >= 49/440640 on 0 <= delta <= 5/6, 0 <= x <= 1/2, via the identity (20.9)
    dl, y = sp.symbols('delta y', real=True)
    x = sp.Rational(1, 2) - y
    DX = 3 - sp.Rational(17, 9) * x
    PX = (7 + 18 * y + 8 * y ** 2) / 9
    JJ = (sp.Rational(5, 6) - dl) * DX + dl * PX
    Rs = 1 - dl + (sp.Rational(5, 6) - dl) * dl * PX / (2 * JJ)      # R_* = L(t_bal)
    aa = (1 + dl) / 2
    Estar = sp.nsimplify(E(sp.Symbol('h_'), aa, x * dl, Rs)).subs(sp.Symbol('h_'), sp.Rational(13, 16))
    v = 51 + 41 * y
    lhs = 10368 * v * JJ * (-Estar)
    rhs = (3 + 5 * y) * ((4 * v * dl - 79) ** 2 + 49) + 4 * y * (4 * v * dl * ((1 + 3 * y) * (15 + 32 * y) * dl + 9 - 13 * y) + 265 + 3485 * y)
    assert sp.simplify(sp.together(lhs - rhs)) == 0, "identity (20.9) fails"
    # numeric margin check on a grid
    worst = min(-float(Estar.subs({dl: dd, y: yy})) for dd in [Fr(k, 60) for k in range(0, 51)] for yy in [Fr(k, 40) for k in range(0, 21)])
    assert worst >= 49 / 440640, worst
    # (20.11): d_min <= d <= 1/2, R = 76/75 - (2/3) delta, q = delta/2: E(1/2) <= -49/14400 for delta <= 5/6
    worst11 = max(E(Fr(1, 2), (1 + dd) / 2, dd / 2, Fr(76, 75) - Fr(2, 3) * dd) for dd in [Fr(k, 60) for k in range(1, 51)])
    assert worst11 <= Fr(-49, 14400), worst11
    assert E(Fr(1, 2), (1 + Fr(5, 6)) / 2, Fr(5, 12), Fr(76, 75) - Fr(2, 3) * Fr(5, 6)) == Fr(-529, 2400) + Fr(25, 96) * Fr(5, 6)
    print("all Stage II certificates reproduced at the paper's values:")
    print("  C(7/8) = 3/16; (20.5) = -7/1200; (20.7) = -1/48 - delta/16; (20.6) = -79/800;")
    print("  Lemma 20.2 identity (20.9) holds symbolically, grid min of -E_* =", worst, ">= 49/440640 =", 49/440640)
    print("  (20.11) worst =", worst11, "<= -49/14400 =", float(Fr(-49, 14400)))

if __name__ == "__main__":
    check()
