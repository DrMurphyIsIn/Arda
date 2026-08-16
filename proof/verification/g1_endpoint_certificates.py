"""G1 HARDENING part 2: the heavy-top endpoint and the FULL mixed-profile hub layer,
certified in exact rational arithmetic -- completing the G1 program for the arc.

Builds on g1_floor_certificates' kernel (rational exp brackets, verified constants,
anchored log bounds).  Two results:

(1) HEAVY-TOP ENDPOINT (interpolation_lemma), rational.  The old certificate was an
    interval-float scan.  Here: A_top * C1 * (1 + z_t sigma_top) collects into
    F(dt,cT) * FD^j * (26/23) * rho^{-(2+2cT+j vD)} * (1 + z_t sigma_top) with rho
    bracketed rationally; per-dt EXACT evaluation on dt < 400 plus a monotone tail
    (F decreasing in dt; z_t sigma_top fractional-linear, sup at an endpoint), compared
    against the rational bound e^{-3/200} >= 1/exp_upper(3/200).  Worst sup/target
    0.9044 -- a 9.6% certified margin.

(2) THE MIXED-PROFILE HUB LAYER, ALL m, rational -- superseding both the m >= 11
    payment-dominance argument and the m <= 10 sweeps.  Per-child cost
    c(y) = (11/50)(y-T0)_+ + tau * [y in window] admits the CONVEX MINORANT
        chat(y) = 0                       for y <= T_HI - EPS,
                  (11/100)(y - T_HI+EPS)  for y in (T_HI-EPS, T_HI+EPS],
                  (11/50)(y - T_HI)       for y >  T_HI+EPS,
    (breakpoints at the CERTAIN window boundaries -- the T0-bracket-safe choice; the
    naive T_LO-EPS start is INVALID in a 1e-7 sliver where membership is ambiguous).
    Validity is a finite list of rational piece-comparisons (certified in-code).
    By Jensen, sum_i c(y_i) >= m * chat(S/m), so the hub charge is bounded by a
    1-VARIABLE function of the total mass S:
        H(S, m) = L - log(1 + S/(m+1)) + m*chat(S/m) - (11/50)(cav - T0)_+ .
    * m in {2..7}: adaptive bisection over S in (0, m/2] certifies H >= 47/2000.
    * m >= 8 UNIFORM LEMMA: cav <= 1/9 < T0 kills the penalty; with sigma = S/m,
      H >= L - log(1+sigma) + 8*(11/100)*(sigma - b)_+  (b = T_HI - EPS), which at
      sigma <= b is >= L - log(1+b) >= 0.0238, and for sigma > b has derivative
      >= 22/25 - 1/(1+sigma) > 0 -- increasing.  One rational check each.
    CONSEQUENCE: charge >= 47/2000 = DELTA_AMORT for EVERY pure hub at EVERY m and
    EVERY child profile -- the amortized hub bound's mixed layer is now a theorem at
    rational rigor, no sweeps.

conjecture1_proved=False.  Self-verifying run_all(); zero floats in certificate paths.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(100000)

from verification.g1_floor_certificates import (
    exp_upper,
    L_LO,
    T_LO,
    T_HI,
    log1p_upper,
    ELEVEN50,
)

EPS = Fr(29, 1000)
TAU = Fr(99, 10000)                 # certified tax floor / 2
B = T_HI - EPS                      # certain-window start (T0-bracket-safe)
FLOOR = Fr(47, 2000)                # DELTA_AMORT


# --------------------------------------------------------- (1) heavy-top endpoint
def certify_heavy_top_rational(D0: int = 400) -> dict:
    r_lo = Fr(12294736, 10 ** 7)
    assert r_lo ** 11 <= Fr(621, 64)
    target = 1 / exp_upper(Fr(3, 200))

    def F_rat(d, c):
        if c == 0:
            return Fr(1)
        return Fr(3, 2) ** c + Fr(c, 2 * (d + c)) * Fr(3, 2) ** (c - 1)

    DEFS = {"none": (0, Fr(0), Fr(1), [0, 0]), "leaf": (1, Fr(1), Fr(1), [1, 2]),
            "arm1": (3, Fr(3, 7), Fr(7, 4), [1, 9]),
            "arm2": (5, Fr(3, 11), Fr(11, 4), [1, 13])}
    worst = Fr(0)
    for cT in range(6):
        for name, (vD, zD, FD, jr) in DEFS.items():
            for j in range(jr[0], jr[1] + 1):
                S = 2
                dt_min = max(j + S, -(-(23 - 4 * cT) // 3))
                k = 2 + 2 * cT + j * vD
                const = FD ** j * Fr(26, 23) / (r_lo ** k)

                def G(dt):
                    zsig = (Fr(9, 23) * (dt - j - S) + 3 * j * zD) / (3 * dt + 4 * cT)
                    return F_rat(dt, cT) * (1 + zsig) * const

                sup = max(G(dt) for dt in range(dt_min, D0))
                zs_tail = max((Fr(9, 23) * (D0 - j - S) + 3 * j * zD) / (3 * D0 + 4 * cT),
                              Fr(3, 23))
                sup = max(sup, F_rat(D0, cT) * (1 + zs_tail) * const)
                assert sup < target, (cT, name, j)
                worst = max(worst, sup / target)
    return {"heavy_top": "rationally certified", "worst_sup_over_target": float(worst)}


# ------------------------------------------- (2) the mixed layer: minorant + Jensen
def chat(y: Fr) -> Fr:
    if y <= B:
        return Fr(0)
    if y <= T_HI + EPS:
        return (ELEVEN50 / 2) * (y - B)
    return ELEVEN50 * (y - T_HI)


def certify_minorant_validity() -> dict:
    """chat <= true cost for every y, rationally, by piece analysis (T0 in [T_LO,T_HI]):
    (i)   y <= B = T_HI-EPS: chat = 0 <= cost.                                    [trivial]
    (ii)  y in (B, T_HI+EPS]: y >= T_HI-EPS >= T0-EPS, so IF y <= T0+EPS the child
          is certainly in the window and cost >= TAU >= chat's max on the piece
          (11/100)(2 EPS); IF y > T0+EPS (only possible for y > T_LO+EPS) then
          cost >= (11/50)(y - T0) >= (11/50)(y - T_HI) and chat = (11/100)(y-B)
          <= (11/50)(y - T_HI) whenever y >= T_HI + ... -- covered by the max-check
          (11/100)(y-B) <= (11/50)(EPS) <= (11/50)(y-T0) since y - T0 > EPS.       [rational]
    (iii) y > T_HI+EPS: chat = (11/50)(y-T_HI) <= (11/50)(y-T0).                  [T0<=T_HI]
    Also convexity (slopes 0 <= 11/100 <= 11/50) and continuity at both breakpoints."""
    assert (ELEVEN50 / 2) * (2 * EPS) <= TAU                        # piece (ii), window case
    assert (ELEVEN50 / 2) * (2 * EPS) <= ELEVEN50 * EPS             # piece (ii), above case
    # continuity at T_HI+EPS:
    assert (ELEVEN50 / 2) * (T_HI + EPS - B) == ELEVEN50 * ((T_HI + EPS) - T_HI)
    return {"minorant": "valid (rational piece analysis), convex, continuous"}


def H_lower(m: int, S0: Fr, S1: Fr) -> Fr:
    u1 = S1 / (m + 1)
    cav_hi = Fr(1) / (m + 1 + S0)
    pen = ELEVEN50 * max(Fr(0), cav_hi - T_LO)
    return L_LO - log1p_upper(u1) + m * chat(S0 / m) - pen


def _bisect(m, floor, S0, S1, depth=0):
    if H_lower(m, S0, S1) >= floor:
        return True
    if depth >= 24:
        return False
    mid = (S0 + S1) / 2
    return _bisect(m, floor, S0, mid, depth + 1) and _bisect(m, floor, mid, S1, depth + 1)


def certify_mixed_layer_all_m() -> dict:
    """charge >= FLOOR for every pure hub, every m >= 2, every profile."""
    for m in range(2, 8):
        # S0 = 0 (review amendment: the earlier 1e-6 start left a formally uncovered
        # sliver S in (0, 1e-6); H_lower handles S0 = 0 directly and the bound is
        # slack there -- H_lower(m, 0, 1e-6) >= 0.18 -- so the claim is now literal)
        assert _bisect(m, FLOOR, Fr(0), Fr(m, 2)), m
    # m >= 8 uniform: cav <= 1/9 < T_LO kills the penalty
    assert Fr(1, 9) < T_LO
    # sigma <= b branch:  L - log(1+b) >= FLOOR
    assert L_LO - log1p_upper(B) >= FLOOR
    # sigma > b branch: derivative >= 8*(11/100) - 1/(1+sigma) >= 22/25 - 1 ... rational:
    # 8*(11/100) = 22/25 = 0.88 > 1 >= 1/(1+sigma)?  1/(1+sigma) <= 1 <= ... need 22/25 > 1? NO:
    # 22/25 = 0.88 < 1: at sigma = b the derivative could be negative?  1/(1+b) = 0.813 < 0.88 OK:
    assert Fr(22, 25) > Fr(1) / (1 + B)          # increasing on sigma > b
    return {"mixed_layer": "charge >= 47/2000 for ALL m >= 2, ALL profiles "
                           "(m in 2..7 bisection; m >= 8 uniform lemma)"}


def run_all():
    out = {}
    out["heavy_top"] = certify_heavy_top_rational()
    out["minorant"] = certify_minorant_validity()
    out["mixed_all_m"] = certify_mixed_layer_all_m()
    out["status"] = {
        "G1": "COMPLETE for the arc: floors (g1_floor_certificates) + heavy-top endpoint "
              "+ the FULL mixed-profile hub layer (all m, all profiles) at rational rigor. "
              "The amortized hub bound and the interpolation lemma no longer contain any "
              "sweep- or float-rigor step.",
        "supersedes": "amortized_hub_bound (2b) payment-dominance and (2c) sweeps; "
                      "interpolation_lemma's interval-float endpoints",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
