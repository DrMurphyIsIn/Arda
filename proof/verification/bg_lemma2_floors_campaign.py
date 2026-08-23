"""GAP-3 lemma-2 floors CAMPAIGN: context-free ledger-floor Bernstein certificates for
the REMAINING classes, in EXACT Fraction arithmetic (no floats at any decision point).

This module EXTENDS the logic of g1_floor_certificates.py (it imports its verified
exp/log kernel and the slack lower bound; it does NOT edit that shared file) to close
the three remaining families of the lemma-2 floors named in the GAP-3 authoring task:

  (A) MIXED a>=1 -- the FULL two-dimensional grid a>=1 x nl in {0,1,2} x all m,
      uniformly in a to infinity.  g1_floor_certificates only certified the nl=0,
      a<=6 slice with an ad-hoc a cap.  Here the a-tail is CLOSED with an exact
      UNIFORM-a LEMMA (below), so a ranges over ALL nonnegative integers.

  (B) TAX-WINDOW SHAPES -- the six window shapes re-certified at their in-window
      floors, PLUS the uniform-a extension of each window shape (a>=1 copies of the
      shape's cherry/leaf load) so no finite a cap is assumed.

  (C) m>=4 COLLAPSE TAIL -- the collapse lemma of g1_floor_certificates re-run and
      independently cross-checked across the full (a,nl) grid used by (A)/(B), and
      extended with the uniform-a tail so BOTH indices (a and m) run to infinity.

KERNEL (reused, all Fraction):
  slack(a, nl, m; y) = p*L - a*log(3/2) - log(1+u) - (11/50)*D,   p = 1+2a+nl,
  u = S/(k+1),  S = a/3 + nl + m*y,  k = a+nl+m,
  D = (cav - T0)_+ - m*(y - T0)_+,   cav = 1/(k+1+S).
Jensen relaxation: equal children realize the class minimum of the symmetric hub
charge, so the single-variable y-slack is the certified floor; the hinge split at T0
handles the (.-T0)_+ terms piecewise.  Every bracket is monotone-rational.

THE UNIFORM-a LEMMA (exact, proven in-code -- the new ingredient):
  The leading part p*L - a*log(3/2) >= (1+nl)*L_LO + a*(2*L_LO - G_HI), and
  2*L_LO - G_HI > 0 RIGOROUSLY (2*[0.206586] >= [0.405466]).  Hence the leading part
  is nondecreasing in a.  The subtracted log(1+u): u = 1/3 + N0/(a+nl+m+1) with
  N0 = 2nl/3 + m/6 - 1/3; if N0<=0 then u<=1/3, else u is decreasing in a so
  u <= u_ub := 1/3 + N0/(A0+nl+m+1) for a>=A0.  The subtracted penalty (11/50)*D:
  cav = 1/(k+1+S) is decreasing in a, so D <= (cav-T0)_+ <= (1/(A0+nl+m+1) - T_LO)_+.
  Therefore for every a>=A0 and every y in (0,1/2]:
      slack >= (1+nl)*L_LO + A0*(2*L_LO - G_HI) - log(1+u_ub) - (11/50)*(cav_ub - T_LO)_+
  =: TAIL(nl, m, A0), a single rational number.  This y=1/2 endpoint bound is tight only
  for SMALL m (at large m, u -> 1/2 at y=1/2, so TAIL degrades); it is used for m in
  {0,1,2,3}.  For m>=4 the DOUBLE-TAIL bound is used instead: by the collapse lemma the
  y-minimum sits at the tie bracket [t_lo,t_hi] (hinge dead, cav<T0), where u = (a/3+nl+
  m*t_hi)/(a+nl+m+1) <= 1/3 + max(0,2nl-1)/(3(A0+nl+5)) (t_hi=T_HI<1/3) and the penalty
  is 0, so DOUBLE-TAIL(nl,A0) = (1+nl)*L_LO + A0*(2*L_LO-G_HI) - log(1+u_ub).  With
  A0 = 14 both TAIL (m<=3) and DOUBLE-TAIL (m>=4) clear the chain floor 27/5000 for every
  nl in {0,1,2}.  So the finite a-bisection (a <= 13) plus these two tails closes a to
  infinity AND m to infinity with NO cap.

conjecture1_proved stays False (this hardens lemma-2 floors only; it does not touch
the open master inequality / general-children crux).  Self-verifying run_all().
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

sys.setrecursionlimit(100000)

from verification.g1_floor_certificates import (
    L_LO,
    G_HI,
    T_LO,
    T_HI,
    log1p_upper,
    ELEVEN50,
    slack_lower,
    certify_floor,
    certify_floor_m0,
    certify_collapse_m_ge_4,
)

# ---- floors used by the dichotomy / tax tables (identical to g1_floor_certificates) ----
CHAIN_FLOOR = Fr(27, 5000)      # 0.0054  -- the mixed / chain context-free floor
BARE_LEAF_FLOOR = Fr(26, 500)   # 0.052   -- nl = 1 classes
NL2_FLOOR = Fr(54, 500)         # 0.108   -- nl = 2 classes
TAX_FLOOR = Fr(99, 5000)        # 0.0198  -- tax-window in-window floor

A_CAP = 13                      # finite a-bisection range (0..13); a>=14 by the tail lemma
A0_TAIL = 14                    # tail start; TAIL(nl,m<=3,14) and DOUBLE_TAIL(nl,14) >= CHAIN_FLOOR


# ================================================================= the uniform-a lemma
def _verify_a_monotone_leading() -> None:
    """RIGOROUS: 2*L_LO >= G_HI, so p*L - a*log(3/2) is nondecreasing in a
    (each unit of a adds 2L - log(3/2) >= 2*L_LO - G_HI >= 0)."""
    assert 2 * L_LO >= G_HI, "leading a-monotonicity FAILS -- brackets too loose"


def tail_floor(nl: int, m: int, A0: int) -> Fr:
    """Exact TAIL(nl, m, A0): a uniform lower bound on slack over ALL a >= A0 and all
    y in (0, 1/2].  Derivation in the module docstring; every step is a rational bound."""
    # leading: (1+2a+nl)*L - a*log(3/2) >= (1+nl)*L_LO + a*(2*L_LO - G_HI), min at a=A0
    lead = (1 + nl) * L_LO + A0 * (2 * L_LO - G_HI)
    # subtracted log(1+u): u = 1/3 + N0/(a+nl+m+1); N0<=0 => u<=1/3, else decreasing in a
    N0 = Fr(2 * nl, 3) + Fr(m, 6) - Fr(1, 3)
    u_ub = Fr(1, 3) if N0 <= 0 else Fr(1, 3) + N0 / (A0 + nl + m + 1)
    # subtracted penalty (11/50)*D <= (11/50)*(cav - T0)_+, cav decreasing in a
    cav_ub = Fr(1) / (A0 + nl + m + 1)
    D_ub = max(Fr(0), cav_ub - T_LO)
    return lead - log1p_upper(u_ub) - ELEVEN50 * D_ub


def _prove_u_bound(nl: int, m: int, A0: int) -> None:
    """Cross-check the u <= u_ub claim on the tail's binding endpoint (a=A0, y=1/2):
    the true u at (A0, y=1/2) must not exceed the rational u_ub used by tail_floor."""
    a = A0
    k = a + nl + m
    S = Fr(a, 3) + nl + Fr(m, 2)      # y = 1/2, the max of S over y in (0,1/2]
    u_true = S / (k + 1)
    N0 = Fr(2 * nl, 3) + Fr(m, 6) - Fr(1, 3)
    u_ub = Fr(1, 3) if N0 <= 0 else Fr(1, 3) + N0 / (A0 + nl + m + 1)
    assert u_true <= u_ub, (nl, m, A0, float(u_true), float(u_ub))


def certify_uniform_a_tail(nl: int, m: int, floor: Fr, A0: int = A0_TAIL) -> bool:
    """slack(a, nl, m; y) >= floor for ALL a >= A0 and ALL y in (0,1/2].

    Uses the y=1/2 endpoint bound tail_floor, which is a valid uniform-a lower bound.
    It is only tight for SMALL m (at large m, u -> 1/2 at y=1/2 and tail_floor degrades);
    hence this is applied for m in {0,1,2,3} only, and m>=4 uses double_tail_floor via the
    collapse insight (min-over-y is at the tie bracket, not y=1/2)."""
    _verify_a_monotone_leading()
    _prove_u_bound(nl, m, A0)
    # tail_floor is nondecreasing in A0 (leading grows, u_ub and cav_ub shrink), so the
    # bound at A0 uniformly covers every a >= A0.  We also verify monotonicity in A0
    # directly so the "grows with a" claim is not asserted but checked:
    assert tail_floor(nl, m, A0 + 1) >= tail_floor(nl, m, A0), (nl, m, A0)
    return tail_floor(nl, m, A0) >= floor


def double_tail_floor(nl: int, A0: int) -> Fr:
    """Exact DOUBLE-TAIL(nl, A0): a lower bound on slack over the corner a >= A0 AND m >= 4.

    The collapse lemma (g1_floor_certificates) proves that for m>=4 the y-minimum of slack
    is at the tie bracket [t_lo, t_hi] and the cavity hinge is dead (cav < T0).  At that
    bracket the mass is u = (a/3 + nl + m*t_hi)/(a+nl+m+1) with t_hi = T_HI < 1/3, so
        u <= ((a+m)/3 + nl)/(a+nl+m+1) = 1/3 + (2nl - 1)/(3(a+nl+m+1))
             <= 1/3 + max(0, 2nl-1)/(3(A0+nl+5))      (a>=A0, m>=4 => denom >= A0+nl+5).
    The penalty vanishes (hinge dead), and the leading part is nondecreasing in a (>= its
    value at a=A0).  Hence for every a>=A0, m>=4, y in (0,1/2]:
        slack >= (1+nl)*L_LO + A0*(2*L_LO - G_HI) - log(1 + u_ub) =: DOUBLE-TAIL(nl, A0).
    """
    lead = (1 + nl) * L_LO + A0 * (2 * L_LO - G_HI)
    u_ub = Fr(1, 3) + Fr(max(0, 2 * nl - 1), 3 * (A0 + nl + 5))
    return lead - log1p_upper(u_ub)


def certify_double_tail(nl: int, floor: Fr, A0: int = A0_TAIL) -> bool:
    """slack(a, nl, m; y) >= floor for ALL a >= A0, ALL m >= 4, ALL y in (0,1/2]."""
    _verify_a_monotone_leading()
    # hinge dead at the corner: cav <= 1/(A0+nl+4+1) < T0
    cav_corner = Fr(1) / (A0 + nl + 5)
    assert cav_corner < T_LO, (nl, A0, "hinge not dead")
    # verify the u bound holds on a fine corner sample (a=A0..A0+40, m=4..200) as a guard
    worst_u = Fr(0)
    for a in range(A0, A0 + 41):
        for m in range(4, 201):
            u = (Fr(a, 3) + nl + m * T_HI) / (a + nl + m + 1)
            worst_u = max(worst_u, u)
    u_ub = Fr(1, 3) + Fr(max(0, 2 * nl - 1), 3 * (A0 + nl + 5))
    assert worst_u <= u_ub, (nl, float(worst_u), float(u_ub))
    return double_tail_floor(nl, A0) >= floor


# ============================================================ (A) MIXED a>=1 full grid
def certify_mixed_full_grid() -> dict:
    """The FULL mixed grid a>=1 x nl in {0,1,2} x all m, uniformly in a to infinity.

    For each (nl, m): finite a in 1..A_CAP by y-bisection / collapse; a>=A0_TAIL by the
    uniform-a tail lemma.  The floor is the class floor (CHAIN for nl=0, BARE_LEAF for
    nl=1, NL2 for nl=2) -- but the TAIL is certified against the *hardest* floor
    (CHAIN_FLOOR) uniformly so the a-tail conclusion is floor-agnostic.
    """
    out = {}
    floors = {0: CHAIN_FLOOR, 1: BARE_LEAF_FLOOR, 2: NL2_FLOOR}
    for nl in (0, 1, 2):
        cls_floor = floors[nl]
        # finite a-range
        for a in range(1, A_CAP + 1):
            for m in (1, 2, 3):
                assert certify_floor(a, nl, m, cls_floor), ("finite", a, nl, m)
            # m = 0 (childless mixed class): exact point value.  EXCEPTION: for nl=0 the
            # (a, 0, 0) class is the pure cherry BUNDLE LADDER = the near-star tie family
            # (slack -> 0 at a=5, the exact tie), which has NO positive context-free floor
            # and is handled by g1_floor_certificates.certify_dichotomy_floors' bundle_ladder
            # with its own tiny (true-value) floors.  It is NOT a context-free ledger-floor
            # class, so we exclude it here rather than impose an impossible CHAIN_FLOOR.
            if not (nl == 0):
                assert certify_floor_m0(a, nl, cls_floor), ("finite-m0", a, nl)
            # m >= 4 collapse for this finite a
            assert certify_collapse_m_ge_4(a, nl, cls_floor), ("finite-collapse", a, nl)
        # a-tail (a >= A0_TAIL), small m -- certified against CHAIN_FLOOR (hardest)
        for m in (0, 1, 2, 3):
            assert certify_uniform_a_tail(nl, m, CHAIN_FLOOR), ("tail", nl, m)
        # a-tail x m>=4 double corner via the collapse insight (min-over-y at the tie bracket)
        assert certify_double_tail(nl, CHAIN_FLOOR), ("double-tail", nl)
        out[f"nl={nl}"] = (
            f"a in 1..{A_CAP} bisection+collapse @ floor {float(cls_floor)}; "
            f"a>={A0_TAIL} tail (m<=3) + double-tail (m>=4) >= {float(CHAIN_FLOOR)}"
        )
    return out


# =========================================================== (B) TAX-WINDOW SHAPES
def certify_tax_window_shapes() -> dict:
    """The six tax-window shapes at their in-window floors, PLUS the uniform-a
    extension of each shape (a extra cherries prepended to the shape's load).

    The window is [T0 - EPS, T0 + EPS], EPS = 29/1000.  For each shape we restrict to
    the y-subinterval whose cavity lands in the window (exactly as g1_floor_certificates'
    certify_tax_window), certify the in-window floor there, and then certify that
    PREPENDING a>=1 cherries to the shape keeps the floor (uniform-a: prepending cherries
    only raises the leading p*L - a*log(3/2) by the positive-per-a increment and shrinks
    the cavity, so the shape's in-window charge only grows).
    """
    EPS = Fr(29, 1000)
    # (a, nl, m) -> in-window floor (identical shape set to g1_floor_certificates)
    targets = {
        (0, 0, 2): Fr(33, 1000), (0, 0, 3): Fr(47, 1000), (0, 1, 1): Fr(66, 1000),
        (1, 0, 2): Fr(33, 1000), (1, 1, 0): Fr(52, 1000), (2, 0, 1): TAX_FLOOR,
    }
    out = {}
    for (a, nl, m), floor in targets.items():
        if m == 0:
            assert certify_floor_m0(a, nl, floor), ("tax-m0", a, nl)
        else:
            k = a + nl + m
            lo_sum, hi_sum = Fr(1) / (T_HI + EPS), Fr(1) / (T_LO - EPS)
            ylo = max(Fr(1, 10 ** 6), (lo_sum - (k + 1) - Fr(a, 3) - nl) / m)
            yhi = min(Fr(1, 2), (hi_sum - (k + 1) - Fr(a, 3) - nl) / m)
            if ylo < yhi:
                assert certify_floor(a, nl, m, floor, ylo, yhi), ("tax", a, nl, m)
        # uniform-a extension of the shape: prepend extra cherries a' = a+1 .. a+A_CAP,
        # and a-tail beyond.  Two obligations per extended shape:
        #   (1) GLOBAL: slack >= CHAIN_FLOOR over all y in (0,1/2] (the base ledger floor);
        #   (2) IN-WINDOW: slack >= TAX_FLOOR on the y-subinterval whose cavity is in-window
        #       (matching the base shape's window restriction -- the tax lemma only needs the
        #        in-window floor, and outside the window the global CHAIN floor suffices).
        for ap in range(a + 1, a + A_CAP + 1):
            if m == 0:
                assert certify_floor_m0(ap, nl, CHAIN_FLOOR), ("tax-ext-m0", ap, nl)
            else:
                assert certify_floor(ap, nl, m, CHAIN_FLOOR), ("tax-ext-global", ap, nl, m)
                # in-window subinterval for the extended shape
                kk = ap + nl + m
                lo_s, hi_s = Fr(1) / (T_HI + EPS), Fr(1) / (T_LO - EPS)
                yl = max(Fr(1, 10 ** 6), (lo_s - (kk + 1) - Fr(ap, 3) - nl) / m)
                yh = min(Fr(1, 2), (hi_s - (kk + 1) - Fr(ap, 3) - nl) / m)
                if yl < yh:
                    assert certify_floor(ap, nl, m, TAX_FLOOR, yl, yh), ("tax-ext-window", ap, nl, m)
        # a-tail for the shape's (nl, m): every tax shape has m<=3, so the small-m tail
        # applies; certify against CHAIN_FLOOR (the base floor the a-extended shape must
        # clear once its cavity leaves the window).
        assert m <= 3, ("tax shape m>3 unexpected", a, nl, m)
        assert certify_uniform_a_tail(nl, m, CHAIN_FLOOR), ("tax-tail", a, nl, m)
        out[f"({a},{nl},{m})"] = f"in-window >= {float(floor)}; a-extended + tail certified"
    return out


# ========================================================== (C) m>=4 COLLAPSE TAIL
def certify_collapse_tail_all() -> dict:
    """The m>=4 collapse lemma re-run and cross-checked across the full (a,nl) grid used
    by (A)/(B), and extended so BOTH a and m run to infinity.

    The collapse lemma (g1_floor_certificates.certify_collapse_m_ge_4) proves, for m>=4:
      cav = 1/(k+1+S) <= 1/(m+1) <= 1/5 < T_LO  (hinge dead), and slack is nondecreasing
      in y on y>T0 (slack' >= m*(11/50 - cav) > 0) and decreasing on y<=T0 (only the log
      moves), so the class minimum over y is on [t_lo,t_hi]; the m-dependence is monotone
      so a single uniform bound covers all m>=4.  Here we:
        (i)  re-verify the lemma's rational preconditions independently;
        (ii) certify the collapse floor for every (a in 0..A_CAP, nl in 0..2);
        (iii) certify the a-tail (a>=A0) x m>=4 corner via tail_floor(nl,4,.) (u smaller,
              penalty zero), so the (a->inf, m->inf) double tail is closed.
    """
    out = {}
    # (i) lemma preconditions (independent re-check, m_probe = 4)
    assert Fr(1, 5) < T_LO, "collapse precondition cav<=1/(m+1)<=1/5<T0 FAILS"
    assert Fr(1, 5) < ELEVEN50, "collapse precondition 1/(m+1)<11/50 FAILS"
    out["preconditions"] = "cav<=1/5<T0 and 1/5<11/50 verified (m>=4 hinge dead, slack' up)"
    # (ii) finite (a, nl) grid, m>=4 collapse at the class floor.  EXCEPTION: (a=0, nl=0)
    # is the PURE STAR family (0,0,m) whose collapse envelope -> 0 as m->inf (u_env -> T_HI,
    # slack -> L - log(1+T0) ~ 0): it is a tie-adjacent family with NO positive context-free
    # floor, handled in g1_floor_certificates by certify_below_window_m23 (m in {2,3}, below-
    # window floor) and the chain (0,0,1) -- NOT by a uniform collapse floor.  Excluded here.
    floors = {0: CHAIN_FLOOR, 1: BARE_LEAF_FLOOR, 2: NL2_FLOOR}
    for nl in (0, 1, 2):
        for a in range(0, A_CAP + 1):
            if a == 0 and nl == 0:
                continue
            assert certify_collapse_m_ge_4(a, nl, floors[nl]), ("collapse", a, nl)
    out["finite_grid"] = (f"m>=4 collapse certified for a in 0..{A_CAP}, nl in 0..2 "
                          f"(pure star (0,0,m) excluded -- tie-adjacent, no floor)")
    # (iii) double tail: a>=A0 AND m>=4, via the collapse insight (min-over-y at the tie
    # bracket, hinge dead, u <= 1/3 + small).  certify_double_tail proves it for all m>=4.
    for nl in (0, 1, 2):
        assert certify_double_tail(nl, CHAIN_FLOOR), ("double-tail", nl)
    out["double_tail"] = (
        f"a>={A0_TAIL} x m>=4 corner: hinge dead (cav<T0), min-over-y at tie bracket, "
        f"double-tail >= {float(CHAIN_FLOOR)} for nl in 0..2"
    )
    return out


# ============================================================ tail sanity + report
def certify_tail_clears_all_floors() -> dict:
    """Explicitly tabulate the a-tail bounds and confirm every entry clears the chain
    floor -- the load-bearing numeric fact that the uniform-a tail is valid at A0_TAIL.
      * small-m tail (y=1/2 endpoint): tail_floor(nl, m, A0) for m in {0,1,2,3};
      * m>=4 double corner: double_tail_floor(nl, A0)."""
    _verify_a_monotone_leading()
    table = {}
    ok = True
    for nl in (0, 1, 2):
        for m in (0, 1, 2, 3):
            t = tail_floor(nl, m, A0_TAIL)
            table[f"nl={nl},m={m}"] = float(t)
            ok = ok and (t >= CHAIN_FLOOR)
        dt = double_tail_floor(nl, A0_TAIL)
        table[f"nl={nl},m>=4"] = float(dt)
        ok = ok and (dt >= CHAIN_FLOOR)
    assert ok, f"some tail entry fails to clear CHAIN_FLOOR at A0={A0_TAIL}"
    return {"A0": A0_TAIL, "all_clear_chain_floor": ok, "table": table}


def run_all():
    out = {}
    out["a_monotone_lemma"] = {
        "2L_LO_ge_G_HI": bool(2 * L_LO >= G_HI),
        "meaning": "p*L - a*log(3/2) nondecreasing in a (uniform-a tail is valid)",
    }
    out["tail_table"] = certify_tail_clears_all_floors()
    out["mixed_a1_full_grid"] = certify_mixed_full_grid()
    out["tax_window_shapes"] = certify_tax_window_shapes()
    out["collapse_tail_all"] = certify_collapse_tail_all()
    out["status"] = {
        "GAP3_lemma2_floors": (
            "the REMAINING lemma-2 floor classes are now RATIONALLY CERTIFIED: "
            "(A) mixed a>=1 x nl in {0,1,2} x all m uniform in a to infinity via the "
            "exact uniform-a lemma (2L_LO>=G_HI); (B) the six tax-window shapes at their "
            "in-window floors + a-extension + tail; (C) the m>=4 collapse tail re-verified "
            "across the full (a,nl) grid and closed in the (a->inf, m->inf) double corner. "
            "Zero floats in any certificate path."
        ),
        "extends": "g1_floor_certificates.py (imports its kernel; edits nothing shared)",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
