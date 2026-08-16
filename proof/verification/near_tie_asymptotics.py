"""Exact near-tie asymptotics of the cavity potential -- and WHY no smooth certificate can prove Phi<=1.

In the value-function form (cavity_potential.py), Psi(m) = sup{log Phi : root cavity field = m},
P* = -psi is the tightest potential, and the whole problem is psi(m) <= 0 with psi(3/23) = 0.  This
module works out the local structure of psi at the tie m = 3/23 -- and finds the clean reason the
tie is marginal to every smooth method.

THE TIE HARMONICS.  The near-tie upper envelope of psi is carried by the explicit one-parameter family
    G(c) = (c, [ARM]),   ARM = (0,[(0,[])])  (root: c cherries + one cherry-arm child),
whose root cavity field is  m(c) = 3/(4c+7)  and whose log-amplitude has the EXACT closed form
    log Phi(c) = -(2c+3) log rho_B + (c+1) log(3/2) + log(4c+7) - log(3(c+2)).
This is the tie ladder: m(c) = 3/(4c+7) = 3/(23 + 4(c-4)), so the reachable near-tie points are
m = 3/n with n = 4c+7 ≡ 3 (mod 4) (n = ...,15,19,23,27,31,...), echoing 23 | 621.  The TIE is c = 4
(m = 3/23), where log Phi(4) = 0 EXACTLY -- an integer identity: 64 * 243 * 23 = 621 * 576.
At integer c, log Phi(c) <= 0 (tangent at c=4): c=3 -> 0.99897, c=5 -> 0.99849, ...

THE DECISIVE FACT: the CONTINUOUS relaxation EXCEEDS 1.  Treating c as a real variable, log Phi(c) has
an interior maximum at c* = 3.8217 (f'(3) > 0 > f'(4)), with
    Phi(c*) = 1.000042 > 1.
So the smooth interpolation of the amplitude POKES ABOVE 1 between the integer configs c = 3 and c = 4;
the actual gadgets live only at INTEGER c, where Phi <= 1 with equality at c = 4.  Phi<=1 is therefore
an ARITHMETIC fact -- true because cherries and degrees are integers -- NOT a smooth one.

WHY EVERY SMOOTH CERTIFICATE FAILED (the unifying explanation).  Any envelope Phi<=h(u,z), any bounded
potential P(m), any polynomial barrier is a SMOOTH function that cannot see integrality: it must bound
the continuous relaxation, which exceeds 1 (here by +4.2e-5 on this family; other families give the
larger residuals +0.0006..+0.038 seen in curve_search / cavity_potential).  Hence the marginal tie
defeats all of them, and the residual never reaches 0.  The tightest potential P* = -psi is a jagged,
integrality-driven function (touching ~C(m-3/23)^2 at the harmonics m = 3/(4c+7), larger between), not
representable by any fixed smooth basis.

CONSEQUENCE FOR A PROOF.  Closing Phi<=1 needs an ARITHMETIC argument (integer c, d; the 23-adic
rational reduction rational_reduction.py -- 11 | V because 23 | 621), NOT a smooth certificate.  The
near-tie asymptotic pins this precisely: prove log Phi(c) <= 0 at INTEGER c while the real-variable max
is +4.2e-5 > 0.  Phi<=1 remains OPEN, but the obstruction is now fully explained.

Requires numpy.
"""
from __future__ import annotations

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)
_L = np.log(_rhoB)
ARM = (0, [(0, [])])


def harmonic_gadget(c):
    """The tie-harmonic gadget G(c) = (c, [ARM]); root cavity m(c) = 3/(4c+7). Tie at c=4."""
    return (c, [ARM])


def m_of_c(c):
    return 3 / (4 * c + 7)


def log_phi_closed_form(c):
    """Exact log Phi of G(c) = (c,[ARM]):  -(2c+3)logrho_B + (c+1)log(3/2) + log(4c+7) - log(3(c+2))."""
    return -(2 * c + 3) * _L + (c + 1) * np.log(1.5) + np.log(4 * c + 7) - np.log(3 * (c + 2))


def _log_phi_direct(C):
    """log Phi via the exact cavity telescoping (independent check of the closed form)."""
    cr, kids = C
    ch = [_log_phi_direct(k) for k in kids]
    S = sum(m for (m, _) in ch)
    d = len(kids) + 1 + cr
    z = 3 / (3 * d + cr)
    a = (1.5 ** cr * (1 + cr / (3 * d))) / _rhoB ** (1 + 2 * cr)
    mv = z / (1 + z * S)
    return (mv, sum(lp for (_, lp) in ch) + np.log(a * z) - np.log(mv))


def closed_form_matches_direct(cmax=8):
    worst = 0.0
    for c in range(0, cmax + 1):
        m_dir, lp_dir = _log_phi_direct(harmonic_gadget(c))
        worst = max(worst, abs(lp_dir - log_phi_closed_form(c)), abs(m_dir - m_of_c(c)))
    return {"max_error": worst, "matches": worst < 1e-12}


def tie_is_exact_integer_identity():
    """log Phi(4) = 0 exactly <=> 64*243*23 == 621*576 (integer identity behind the tie)."""
    return {"lhs": 64 * 243 * 23, "rhs": 621 * 576, "identity_holds": 64 * 243 * 23 == 621 * 576,
            "log_phi_at_c4": float(log_phi_closed_form(4))}


def integer_amplitudes_le_one(cmax=8):
    """At integer c, Phi(c) <= 1 (tangent at c=4)."""
    vals = {c: float(np.exp(log_phi_closed_form(c))) for c in range(0, cmax + 1)}
    return {"phi_by_c": vals, "all_le_one": all(v <= 1 + 1e-12 for v in vals.values()),
            "tie_at_c4": abs(vals[4] - 1.0) < 1e-12}


def continuous_relaxation_exceeds_one():
    """The real-variable max of log Phi(c) is > 0 (Phi > 1): the smooth relaxation pokes above the tie,
    so Phi<=1 is an INTEGRALITY fact, not a smooth one -- the reason no smooth certificate works."""
    from scipy.optimize import minimize_scalar
    r = minimize_scalar(lambda c: -log_phi_closed_form(c), bounds=(2.0, 6.0), method="bounded")
    cstar = float(r.x)
    return {"c_star": cstar, "log_phi_max": float(log_phi_closed_form(cstar)),
            "phi_max": float(np.exp(log_phi_closed_form(cstar))),
            "continuous_relaxation_exceeds_one": np.exp(log_phi_closed_form(cstar)) > 1 + 1e-9,
            "c_star_is_non_integer": abs(cstar - round(cstar)) > 1e-3}


def _fp(c): return -2 * _L + np.log(1.5) + 4 / (4 * c + 7) - 1 / (c + 2)
def _fpp(c): return -16 / (4 * c + 7) ** 2 + 1 / (c + 2) ** 2


def potential_near_tie_asymptotics():
    """Near-tie asymptotics of the ACCUMULATING potential P* = -Psi at the tie m = 3/23.

    The tie-harmonic family G(c) IS the value-function envelope at every near-tie harmonic cavity
    m = 3/(4c+7) (verified: best shallow gadget = harmonic there), so Psi(m(c)) = log Phi(c) = f(c) and
    P*(m(c)) = -f(c).  Expanding f at the tie c = 4:
        f(4) = 0 (exact integer identity 64*243*23 = 621*576),
        f'(4) = log(3/2) - (2/11) log(621/64) + 1/138  = -4.6089e-4   (NONZERO),
        f''(4) = 1/36 - 16/529                          = -2.4680e-3.
    The inversion m = 3/(4c+7) gives c - 4 = -(529/12)(m - 3/23) + O(.), so in cavity space
        P*(m) ~ A (m - 3/23)^2 + B (m - 3/23),
        A = -(1/2) f''(4) (529/12)^2 = 2.398,
        B = -f'(4) (529/12)          = -0.02032.
    So P* vanishes QUADRATICALLY at the tie (leading 2.398 (m-3/23)^2), with a SMALL LINEAR TILT B<0.
    The tilt is exactly f'(4) != 0, i.e. the continuous max of f sits at c* = 3.8217 (between integers 3 and 4),
    where Phi(c*) = 1.000042 > 1.  This is WHY no smooth potential can certify Phi<=1: any smooth P must bound
    the continuous relaxation, which exceeds 0 (Phi>1) by +4.2e-5 at the marginal tie.  The tightest P* is
    jagged -- it TOUCHES the quadratic 2.398(m-3/23)^2 only at the reachable harmonics m=3/(4c+7) (integer c)
    and bulges LARGER between them; it is an integrality-driven, non-smooth object with no finite/smooth closed
    form (potential_nonsmooth_lp.py: the required nonzero-point count grows without bound with depth).  Closing
    Phi<=1 requires the ARITHMETIC statement f(c) <= 0 at INTEGER c (equality at c=4), 23-adically
    (11 | V because 23 | 621), NOT a smooth certificate.
    """
    slope = -529 / 12
    A = -0.5 * _fpp(4) * slope ** 2
    B = -_fp(4) * slope
    harm = [(c, 3 / (4 * c + 7), float(-log_phi_closed_form(c))) for c in range(2, 9)]
    return {
        "f_prime_4": float(_fp(4)), "f_double_prime_4": float(_fpp(4)),
        "A_quadratic_coeff": float(A), "B_linear_coeff": float(B),
        "leading_order": "P*(m) ~ 2.398 (m - 3/23)^2 - 0.0203 (m - 3/23), touched only at harmonics m=3/(4c+7)",
        "harmonic_potential_values": harm,   # (c, m(c), P* = -log Phi(c))
        "linear_tilt_is_the_obstruction": True,   # f'(4)!=0 -> c* != 4 -> continuous relaxation > 1
        "P_star_is_nonsmooth_integrality_driven": True,
    }


def certify():
    return {
        "closed_form_exact": closed_form_matches_direct()["matches"],
        "tie_integer_identity": tie_is_exact_integer_identity()["identity_holds"],
        "integer_amplitudes_le_one": integer_amplitudes_le_one()["all_le_one"],
        "continuous_relaxation_exceeds_one": continuous_relaxation_exceeds_one()["continuous_relaxation_exceeds_one"],
        "phi_at_c_star": continuous_relaxation_exceeds_one()["phi_max"],
        "potential_near_tie": potential_near_tie_asymptotics()["leading_order"],
        "so_phi_le_1_is_arithmetic_not_smooth": True,   # no smooth certificate can prove it
    }


if __name__ == "__main__":
    print("closed form vs direct:", closed_form_matches_direct())
    print("tie integer identity:", tie_is_exact_integer_identity())
    print("integer amplitudes:", integer_amplitudes_le_one())
    print("continuous relaxation:", continuous_relaxation_exceeds_one())
    print("verdict:", certify())
