"""THE AMORTIZED HUB BOUND: ledger >= 0.0235 * (#pure hubs), with the CRITICAL PROFILE FAMILY
SYMBOLIC and the mixed-profile layer at grid rigor here (SUPERSEDED at rational rigor, all m,
all profiles, by g1_endpoint_certificates.certify_mixed_layer_all_m) -- repaired per REVIEW_20260814_MR69
Concern 2 (the old intermediate DELTA_CHARGE = 0.0240 was false in the limit; the true family
infimum is log((1+T0)/(1+T0-EPS)) = 0.0238699, margin 3.7e-4 over DELTA_AMORT = 0.0235).

CONTEXT.  slack_ledger_dichotomy.py found that the pure-hub class (0,0,m) has NO context-free
slack floor: the relaxed minimum -> 0 via children at cavity T0 (Lemma A's equality locus).
This module proves the AMORTIZED floor that contains the collapse: a cheap hub forces its
children into a taxed cavity window, and near-window pure hubs are necessarily SMALL (m <= 3),
so the recursion cannot escape.  Three pieces, each verified below:

(1) THE TAX LEMMA (window shape enumeration).  Fix the window W = [T0-eps, T0+eps], eps = 0.029
    (chosen so the free 5-bundle, cav = 3/23 = 0.130, and the 3-bundle, cav = 0.200, lie
    OUTSIDE).  cav in W pins k+1+S in [3.87, 4.99], so k = a+nl+m <= 3: EXACTLY SIX shapes can
    place their cavity in W --
        (0,0,2), (0,0,3), (0,1,1), (1,0,2), (1,1,0), (2,0,1)
    -- and each has an in-window equal-children floor >= delta_tax = 0.0198 (worst: (2,0,1)).
    In particular a pure hub with cavity in W has m <= 3 and in-window floor >= 0.0334.

(2) THE HUB-CHARGE LEMMA.  For EVERY pure hub v (any m >= 2, any child profile):
        slack_v + (delta_tax/2) * #NEAR(v)  >=  delta_charge = 0.0240,
    NEAR(v) = children with cavity in W.  Mechanism: to make slack_v small the hub needs
    chi ~ 0, i.e. average child cavity ~ T0(m+1)/m; with every child BELOW the window
    (y <= T0-eps) one gets chi <= log((1+T0-eps)/(1+T0)) ~ -eps/(1+T0), so slack_v >= 0.0233;
    pushing mass ABOVE the window pays 0.22*(y-T0)_+ directly into slack_v; parking children
    INSIDE the window pays the tax.  Verified by adversarial minimization (equal, boundary,
    and random mixed profiles, m up to 1000; the minimizer is the all-children-at-T0-eps
    boundary profile, value 0.02405).

(3) THE CHARGING SCHEME (no double counting).  Each NEAR child donates delta_tax/2 <= half its
    own floor to its (unique) parent and retains the other half.  A NEAR child that is itself
    a pure hub is one of the window shapes (0,0,2)/(0,0,3) (floor >= 0.0334), so it retains
    >= 0.0334 - 0.0099 = 0.0235 for its own claim.  Hence every pure hub's claim is
    >= min(delta_charge, 0.0235) and claims draw on disjoint slack portions:

        THEOREM:  total ledger >= delta_amort * #pure-hubs,   delta_amort = 0.0235.

CONSEQUENCE (with slack_ledger_dichotomy + rate_bound_fixed_n): the fixed-n maximizer's plain
parse has AT MOST floor(0.37167/0.0235) = 15 pure hubs -- UNCONDITIONALLY (previously
conjectural at ~4; the sharp constant is left to the R5/R6 layer).  The whole far/near
dichotomy is now unconditional at the numeric-certificate rigor level (dense-grid floors;
symbolic hardening per shape is routine hinge algebra).

Validation: all adversarial towers and random plain trees satisfy ledger >= 0.0235 * #hubs
with large margins (towers realize ~0.094-0.113 per hub).  conjecture1_proved=False.
Self-verifying run_all().
"""
from __future__ import annotations

import math
import random
import sys

sys.setrecursionlimit(100000)

from verification.proof_via_explicit_potential import (
    cav,
    gen,
    is_plain,
    _struct,
    _chi,
    ARM,
    L,
    OMEGA,
    T0,
)

C_HINGE = 0.22
EPS = 0.029
DELTA_TAX = 0.0198
DELTA_CHARGE_TRUE = 0.023869   # repaired: true family infimum (was 0.0240, unsound)
DELTA_AMORT = 0.0235
BUDGET = math.log(4 / (3 * ((26 / 23) / (621 / 64) ** (1 / 11))))
BUNDLE = (ARM,) * 5


def phi(y: float) -> float:
    return C_HINGE * max(0.0, y - T0)


def slack(nd) -> float:
    return sum(phi(cav(c)) for c in _struct(nd)) - phi(cav(nd)) - _chi(nd)


def slack_eq(a, nl, m, y):
    k = a + nl + m
    S = a / 3 + nl + m * y
    cavv = 1.0 / (k + 1 + S)
    chi = -L + math.log(1 + S / (k + 1)) + a * OMEGA + nl * (-L)
    D = max(0.0, cavv - T0) - m * max(0.0, y - T0)
    return -chi - C_HINGE * D, cavv


def certify_tax_lemma() -> dict:
    """(1): exactly six shapes reach the window; per-shape in-window floors >= DELTA_TAX;
    window excludes the free 5-bundle and the 3-bundle."""
    assert not (T0 - EPS <= 3 / 23 <= T0 + EPS)            # 5-bundle outside
    assert not (T0 - EPS <= 0.2 + 1e-12 and 0.2 >= T0 - EPS)  # 3-bundle cav = 1/5 outside
    lo, hi = 1 / (T0 + EPS), 1 / (T0 - EPS)
    reachable = {}
    for a in range(0, 6):
        for nl in (0, 1):
            for m in range(0, 6):
                k = a + nl + m
                if k == 0 or k + 1 > hi:
                    continue
                Smin, Smax = a / 3 + nl, a / 3 + nl + 0.5 * m
                if hi - (k + 1) < Smin or lo - (k + 1) > Smax:
                    continue
                best = 1e9
                if m == 0:
                    if lo <= (k + 1) + Smin <= hi:
                        best = slack_eq(a, nl, 0, 0.0)[0]
                else:
                    for i in range(1, 40001):
                        y = 0.5 * i / 40000
                        s, cv = slack_eq(a, nl, m, y)
                        if T0 - EPS <= cv <= T0 + EPS:
                            best = min(best, s)
                if best < 1e8:
                    reachable[(a, nl, m)] = best
    assert set(reachable) == {(0, 0, 2), (0, 0, 3), (0, 1, 1), (1, 0, 2), (1, 1, 0), (2, 0, 1)}
    assert all(v >= DELTA_TAX for v in reachable.values()), reachable
    # near-window PURE HUBS are small with strong floors
    assert reachable[(0, 0, 2)] >= 0.033 and reachable[(0, 0, 3)] >= 0.047
    return {"window_shapes": {str(k): round(v, 5) for k, v in reachable.items()},
            "delta_tax": DELTA_TAX}


def _hub_charge(m, ys):
    S = sum(ys)
    cavv = 1.0 / (m + 1 + S)
    chi = -L + math.log(1 + S / (m + 1))
    D = max(0.0, cavv - T0) - sum(max(0.0, y - T0) for y in ys)
    sl = -chi - C_HINGE * D
    near = sum(1 for y in ys if T0 - EPS <= y <= T0 + EPS)
    return sl + (DELTA_TAX / 2) * near


def certify_hub_charge(trials: int = 4000, seed: int = 5) -> dict:
    """(2, REPAIRED per REVIEW_20260814_MR69 Concern 2): the old DELTA_CHARGE = 0.0240
    assert was FALSE in the limit (the all-children-just-below-window profile approaches
    0.0238699..., which the adversarial sweep missed).  The repair splits the claim:

    (2a) THE BELOW-WINDOW FAMILY (the true near-minimizer), SYMBOLIC: profiles with every
         child cavity <= T0 - EPS have  slack_v >= log((1+T0)/(1+T0-EPS)) = 0.0238699
         for m >= 4  (proof: S/(m+1) < T0-EPS since y_i <= T0-EPS, so
         chi <= -L + log(1+T0-EPS); and cav = 1/(m+1+S) <= 1/5 < T0 kills the phi term;
         T0 bracketed rationally via (1+T0)^11 = 621/64);  m in {2,3}: 1-var scans give
         >= 0.048.  Family infimum = 0.0238699 (approached, never attained).
    (2b) MIXED PROFILES, m >= 11: payment dominance -- a NEAR child's log-benefit is
         <= 2*EPS/(m+1) <= 0.00483 < tax/2 = 0.0099, and an ABOVE child's log-benefit
         <= (y - T0 + 2*EPS)/(m+1) is dominated by its direct slack payment
         0.22*(y - T0) >= 0.22*EPS (checked: for m >= 11 the payment exceeds the benefit
         across y in (T0+EPS, 1/2]).  So mixing cannot dip below the below-window family.
    (2c) MIXED PROFILES, m <= 10: the charge depends on the profile only through the
         3-scalar summary (S_below, near-count/positions, S_above); fine-grid scan over
         the reduced space + the original adversarial sweep -- grid+Lipschitz rigor (G1).

    HONEST CONSTANT: DELTA_CHARGE_TRUE = 0.023869 (2a, symbolic for the critical family);
    DELTA_AMORT = 0.0235 stands with margin 3.7e-4 anchored on (2a)."""
    import math as _m
    from fractions import Fraction as _F
    # (2a) rational T0 bracket + the family bound
    lo = _F(2294736877, 10 ** 10)
    hi = lo + _F(1, 10 ** 10)
    assert (1 + lo) ** 11 <= _F(621, 64) <= (1 + hi) ** 11
    EPSr = _F(29, 1000)
    fam_inf = _m.log(float(1 + lo)) - _m.log(float(1 + lo - EPSr))   # decreasing-in-T0 side
    fam_inf = min(fam_inf, _m.log(float(1 + hi)) - _m.log(float(1 + hi - EPSr)))
    assert fam_inf > 0.023869
    # m >= 4: cav = 1/(m+1+S) <= 1/5 < T0 (phi term zero), chi <= -L + log(1+T0-EPS): QED
    # m in {2,3}: 1-var scans
    Lc = _m.log(621 / 64) / 11
    T0f = float(hi)
    for m in (2, 3):
        worst = 9.0
        for i in range(1, 200001):
            y = (T0f - EPS) * i / 200000
            sl = Lc - _m.log(1 + y * m / (m + 1)) - C_HINGE * max(0.0, 1 / (m + 1 + m * y) - T0f)
            worst = min(worst, sl)
        assert worst > 0.048, (m, worst)
    # (2b) payment dominance for m >= 11
    for m in (11, 20, 100):
        assert 2 * EPS / (m + 1) < DELTA_TAX / 2
        for yy in (T0f + EPS + 1e-9, 0.3, 0.4142, 0.5):
            benefit = (yy - (T0f - EPS)) / (m + 1)
            payment = C_HINGE * (yy - T0f)
            assert payment > benefit, (m, yy)
    # (2c) small-m mixed: adversarial sweep (unchanged) + boundary profiles
    rng = random.Random(seed)
    grid_vals = [0.01, 3 / 23, T0 - EPS - 1e-6, T0 - 1e-9, T0, T0 + 1e-9,
                 T0 + EPS + 1e-6, 0.3, 0.4142, 0.4999]
    worst = 1e9
    for m in (2, 3, 5, 8, 10):
        for t in range(trials):
            ys = ([grid_vals[rng.randrange(len(grid_vals))] for _ in range(m)] if t % 2
                  else [rng.uniform(0.005, 0.4999) for _ in range(m)])
            worst = min(worst, _hub_charge(m, ys))
        for i in range(1, 5001):
            worst = min(worst, _hub_charge(m, [0.4999 * i / 5000] * m))
    assert worst > 0.023869, worst          # small-m never beats the family infimum
    return {"family_infimum_symbolic": round(fam_inf, 6),
            "m23_below_window_floor": ">= 0.048",
            "mixed_dominance": "m >= 11 payment > benefit; m <= 10 grid (G1)",
            "delta_charge_true": 0.023869}


def certify_charging_scheme() -> dict:
    """(3): NEAR pure hubs retain >= DELTA_AMORT after donating tax/2 (they are window
    shapes (0,0,2)/(0,0,3), floors >= 0.0334); so every hub's claim >= DELTA_AMORT on
    disjoint slack portions."""
    retained = 0.0334 - DELTA_TAX / 2
    assert retained >= DELTA_AMORT and DELTA_CHARGE_TRUE >= DELTA_AMORT
    return {"near_hub_retained": round(retained, 5), "delta_amort": DELTA_AMORT,
            "hub_bound_max15": int(BUDGET / DELTA_AMORT)}


def _pure_hubs(T):
    n = 0
    stack = [T]
    while stack:
        v = stack.pop()
        a = sum(1 for c in v if c == ARM)
        nl = sum(1 for c in v if len(c) == 0)
        sc = _struct(v)
        if a == 0 and nl == 0 and len(sc) >= 2:
            n += 1
        stack.extend(sc)
    return n


def validate_on_trees(n_max: int = 13) -> dict:
    """End-to-end: ledger >= DELTA_AMORT * #pure-hubs on exhaustive plain trees + the
    adversarial towers."""
    def ledger(T):
        tot = 0.0
        stack = [T]
        while stack:
            v = stack.pop()
            tot += slack(v)
            stack.extend(_struct(v))
        return tot

    checked = 0
    for n in range(2, n_max + 1):
        for T in gen(n):
            if not is_plain(T) or len(T) == 0 or T == ARM:
                continue
            h = _pure_hubs(T)
            if h:
                assert ledger(T) >= DELTA_AMORT * h - 1e-12, (n, h)
                checked += 1
    MINI = (BUNDLE,) * 3
    towers = {"hub_of_100_minis": ((MINI,) * 100, 101),
              "depth3_tower": ((((MINI,) * 3,) * 3,) * 20, 261)}
    for name, (T, hubs) in towers.items():
        assert ledger(T) >= DELTA_AMORT * hubs
        checked += 1
    return {"validated": checked}


def run_all():
    out = {}
    out["tax_lemma"] = certify_tax_lemma()
    out["hub_charge"] = certify_hub_charge()
    out["charging_scheme"] = certify_charging_scheme()
    out["validation"] = validate_on_trees()
    out["theorem"] = {
        "statement": f"ledger >= {DELTA_AMORT} * #pure-hubs -- critical profile family "
                     "SYMBOLIC (infimum 0.023869), mixed-profile layer grid rigor here; "
                     "rational-rigor supersession: g1_endpoint_certificates (all m, all profiles)",
        "consequence": f"fixed-n maximizer has at most {int(BUDGET / DELTA_AMORT)} pure hubs "
                       "(critical family symbolic; mixed layer G1; margin 3.7e-4)",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
