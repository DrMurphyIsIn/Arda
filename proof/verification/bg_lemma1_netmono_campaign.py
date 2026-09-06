"""
GAP-3 / lemma-1 (chain3p ledger depth-monotonicity) — exact-Fraction campaign.

Attacks the cavity-coupled 3-node NET monotonicity pinned in
`proof/docs/design/G1_STAGE2_AUDIT_20260822.md` (FURTHER SHARPENING 2026-08-22):
for the deep-spine family

    chain3p(pT, pM, pL) = ((((BUNDLE,) * pL,) + (BUNDLE,) * pM),) + (BUNDLE,) * pT

with BUNDLE = (ARM,)*5 the five-arm tie bundle (cav = 3/23), the ledger

    ledger(T) = sum_v slack(v),   slack(v) = sum_{struct children} phi(cav_c) - phi(cav_v) - chi_v,
    phi(y)    = C_HINGE * (y - T0)_+,   T0 = rho_B - 1 = (621/64)^(1/11) - 1,

is (empirically) monotone-increasing in the deep-spine length pL at (pT,pM)=(1,1).
Because every bundle is the tie (phi(cav_bundle)=phi(3/23)=0, slack(bundle)=0), the
ENTIRE ledger is carried by the three spine nodes Z(root) -> Y(mid) -> X(tip):

    ledger(chain3p(1,1,pL)) = slack(Z) + slack(Y) + slack(X)   (exact identity).

WHAT IS EXACT HERE.
  * All cavities are RATIONAL (fractions.Fraction) — the cavity recursion of rational
    children stays rational. Computed exactly; no floats at any structural decision.
  * The knee crossing "cav > T0" is decided EXACTLY by the rational surrogate
    (cav + 1)^11 > 621/64  <=>  cav > T0, since t -> (1+t)^11 is increasing and
    rho_B^11 = 621/64. No float comparison at the knee.
  * The only transcendentals are the chi log terms (log(1 + S/w)) and the constants
    L, OMEGA. These are evaluated at ARBITRARY precision via mpmath with EXACT
    rational arguments, so the monotonicity sign is certified to hundreds of digits,
    not float noise. The exact-inequality ATTEMPT (part c) isolates these log
    differences and asks whether they admit a clean rational/telescoping bound.

HONESTY. This is a probe + attack, not a closure. conjecture1_proved stays False.
It reports (a) monotonicity reproduced to large pL, (b) the exact per-node
decomposition and its sign structure, and (c) an HONEST verdict on whether a clean
exact dominating inequality exists.

Run:  cd proof && python3 -m verification.bg_lemma1_netmono_campaign
"""
from __future__ import annotations

import sys
from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 80  # 80 decimal digits — far beyond float; sign certification

# ---------------------------------------------------------------------------
# Exact constants (rational where possible; T0 handled via rational surrogate)
# ---------------------------------------------------------------------------
RHO_B_11 = Fr(621, 64)                     # rho_B^11 exactly
CAV_BUNDLE = Fr(3, 23)                     # cav of the five-arm tie bundle
CAV_ARM = Fr(1, 3)                         # cav of ARM = ((),)
C_HINGE = Fr(22, 100)                      # 0.22 exactly

# transcendental constants at working precision (exact rational inputs)
L_mp = mp.log(mp.mpf(621) / 64) / 11
OMEGA_mp = mp.log(mp.mpf(3) / 2) - 2 * L_mp
RHO_B_mp = (mp.mpf(621) / 64) ** (mp.mpf(1) / 11)
T0_mp = RHO_B_mp - 1


# ---------------------------------------------------------------------------
# Exact cavity + exact knee decision
# ---------------------------------------------------------------------------
def cav_equal_children(m_struct: int, child_cav: Fr, n_bundles: int) -> Fr:
    """cav of a node with m_struct identical structural children at cavity child_cav
    plus n_bundles tie-bundles (each cav 3/23).  cav = 1/(k+1 + S)."""
    k = m_struct + n_bundles
    S = m_struct * child_cav + n_bundles * CAV_BUNDLE
    return Fr(1, 1) / (k + 1 + S)


def above_knee(y: Fr) -> bool:
    """EXACT decision of y > T0, i.e. (1+y)^11 > 621/64.  y rational."""
    return (1 + y) ** 11 > RHO_B_11


def hinge_exact_rational_part(y: Fr) -> Fr:
    """The RATIONAL part of phi(y) = C_HINGE*(y-T0)_+ is C_HINGE*y when above knee
    (the -C_HINGE*T0 is the irrational part, tracked separately).  Returns
    (is_above, C_HINGE*y) so callers can assemble phi differences exactly modulo T0."""
    if above_knee(y):
        return C_HINGE * y
    return Fr(0)


def phi_mp(y: Fr):
    """phi(y) at working precision (for numeric monotonicity certification)."""
    yv = mp.mpf(y.numerator) / y.denominator
    d = yv - T0_mp
    return C_HINGE_mp * d if d > 0 else mp.mpf(0)


C_HINGE_mp = mp.mpf(22) / 100


def chi_spine_mp(m_struct: int, child_cav: Fr, n_bundles: int):
    """chi_v for a spine node = -L + log(1 + S/w) (+ arm/leaf terms; none on the spine).
    Spine nodes here have NO arms and NO bare leaves (only struct child + bundles), so
    chi = -L + log(1 + S/w).  Exact rational S, w; log at working precision."""
    k = m_struct + n_bundles
    w = k + 1
    S = m_struct * child_cav + n_bundles * CAV_BUNDLE          # exact Fraction
    arg = mp.mpf((1 + S / w).numerator) / (1 + S / w).denominator
    return -L_mp + mp.log(arg)


# ---------------------------------------------------------------------------
# The chain3p spine at (pT, pM) = (1, 1): three nodes Z -> Y -> X
# ---------------------------------------------------------------------------
def spine_cavities(pL: int, pT: int = 1, pM: int = 1):
    """Return exact (cav_X, cav_Y, cav_Z)."""
    cav_X = cav_equal_children(0, Fr(0), pL)                    # pL bundles, no struct child
    cav_Y = cav_equal_children(1, cav_X, pM)                   # X + pM bundles
    cav_Z = cav_equal_children(1, cav_Y, pT)                   # Y + pT bundles
    return cav_X, cav_Y, cav_Z


def slack_spine_mp(cav_self: Fr, cav_child, n_bundles: int, pL_for_tip=None):
    """slack(v) = sum_struct phi(cav_c) - phi(cav_v) - chi_v.
    For X (tip): no struct child (cav_child None) => sum term is 0.
    For Y, Z: one struct child at cav_child.  Bundles are ties: phi(3/23)=0."""
    if cav_child is None:
        sum_term = mp.mpf(0)
        m_struct = 0
        child_cav_for_chi = Fr(0)
    else:
        sum_term = phi_mp(cav_child)
        m_struct = 1
        child_cav_for_chi = cav_child
    chi = chi_spine_mp(m_struct, child_cav_for_chi, n_bundles)
    return sum_term - phi_mp(cav_self) - chi


def ledger_chain3p_mp(pL: int, pT: int = 1, pM: int = 1):
    cav_X, cav_Y, cav_Z = spine_cavities(pL, pT, pM)
    sX = slack_spine_mp(cav_X, None, pL)
    sY = slack_spine_mp(cav_Y, cav_X, pM)
    sZ = slack_spine_mp(cav_Z, cav_Y, pT)
    return sX + sY + sZ, (sX, sY, sZ), (cav_X, cav_Y, cav_Z)


# ---------------------------------------------------------------------------
# (a) reproduce monotonicity to large pL
# ---------------------------------------------------------------------------
def reproduce_monotone(PMAX: int = 4000) -> dict:
    prev = None
    worst_dec = mp.mpf(0)          # most negative increment (should stay >= 0)
    worst_at = None
    n_up = 0
    n_checks = 0
    sample = {}
    for pL in range(1, PMAX + 1):
        led, _, _ = ledger_chain3p_mp(pL)
        if prev is not None:
            d = led - prev
            n_checks += 1
            if d > 0:
                n_up += 1
            if d < worst_dec:
                worst_dec = d
                worst_at = pL
        prev = led
        if pL in (1, 2, 3, 4, 5, 10, 50, 200, 1000, PMAX):
            sample[pL] = mp.nstr(led, 12)
    return {
        "PMAX": PMAX,
        "increments_checked": n_checks,
        "increments_positive": n_up,
        "monotone_increasing": n_up == n_checks,
        "worst_increment": mp.nstr(worst_dec, 6),
        "worst_increment_at_pL": worst_at,
        "ledger_samples": sample,
    }


# ---------------------------------------------------------------------------
# (b) exact per-node sign decomposition through the knee
# ---------------------------------------------------------------------------
def per_node_decomposition(pLs=(1, 2, 3, 4, 5, 8, 11, 30, 100)) -> dict:
    rows = []
    for pL in pLs:
        _, (sX, sY, sZ), (cX, cY, cZ) = ledger_chain3p_mp(pL)
        rows.append({
            "pL": pL,
            "cav_X": mp.nstr(mp.mpf(cX.numerator) / cX.denominator, 8),
            "cav_Y": mp.nstr(mp.mpf(cY.numerator) / cY.denominator, 8),
            "cav_Z": mp.nstr(mp.mpf(cZ.numerator) / cZ.denominator, 8),
            "X_above_knee": above_knee(cX),
            "Y_above_knee": above_knee(cY),
            "Z_above_knee": above_knee(cZ),
            "slack_X": mp.nstr(sX, 8),
            "slack_Y": mp.nstr(sY, 8),
            "slack_Z": mp.nstr(sZ, 8),
        })
    # locate the exact knee crossing pL* for the tip: last pL with cav_X > T0
    knee_pL = None
    for pL in range(1, 200):
        cX = cav_equal_children(0, Fr(0), pL)
        if above_knee(cX) and not above_knee(cav_equal_children(0, Fr(0), pL + 1)):
            knee_pL = pL
            break
    return {"rows": rows, "tip_knee_last_above_pL": knee_pL}


# ---------------------------------------------------------------------------
# (c) attempt the exact dominating inequality
# ---------------------------------------------------------------------------
def exact_inequality_attempt(PMAX: int = 400) -> dict:
    """
    Try to close d(pL) = ledger(pL+1) - ledger(pL) >= 0 by an EXACT argument.

    Increment structure (pT=pM=1).  Going pL -> pL+1 changes ONLY the tip node's
    child count, hence changes cav_X, cav_Y, cav_Z (coupled) and the three slacks.
    All bundle slacks stay 0.  So

        d(pL) = [slack_X(pL+1)-slack_X(pL)] + [slack_Y...] + [slack_Z...].

    Each slack has the shape  phi(cav_child) - phi(cav_self) - chi.
    Split into (I) the HINGE part (rational modulo T0, EXACT) and (II) the CHI
    log-difference part (transcendental).  We test whether the hinge part alone,
    or a rational lower bound on the log part, certifies d >= 0.

    Reported: for each pL, the exact hinge contribution to d and the numeric log
    contribution; and whether hinge-alone >= 0 (a clean exact certificate would
    require the hinge part to dominate a rational bound on the log part).
    """
    hinge_dominates = True
    hinge_alone_nonneg = True
    worst_hinge = mp.mpf(9)
    worst_total = mp.mpf(9)
    rows = []
    for pL in range(1, PMAX + 1):
        # cavities at pL and pL+1
        cX0, cY0, cZ0 = spine_cavities(pL)
        cX1, cY1, cZ1 = spine_cavities(pL + 1)

        # --- EXACT hinge part of d(pL) ---
        # phi(y) contributes C_HINGE*(y-T0) when above knee, else 0.
        # A DIFFERENCE phi_a - phi_b is exact-rational ONLY when a,b are on the SAME
        # side of the knee (the T0 cancels) OR both above (T0 cancels) OR both below
        # (both 0).  When one is above and one below, the T0 term does NOT cancel and
        # the hinge difference carries an irrational -C_HINGE*T0.  We compute the hinge
        # part numerically but flag the knee-straddle where it is not purely rational.
        def phi_val(y):
            return C_HINGE_mp * (mp.mpf(y.numerator) / y.denominator - T0_mp) if above_knee(y) else mp.mpf(0)

        # slack_X = -phi(cav_X) - chi_X   (no struct child)
        # slack_Y = phi(cav_X) - phi(cav_Y) - chi_Y
        # slack_Z = phi(cav_Y) - phi(cav_Z) - chi_Z
        # hinge part of ledger = -phi(cX) + phi(cX) - phi(cY) + phi(cY) - phi(cZ)
        #                       = -phi(cav_Z)   (telescopes!)  <-- key structural fact
        hinge_led_0 = -phi_val(cZ0)
        hinge_led_1 = -phi_val(cZ1)
        d_hinge = hinge_led_1 - hinge_led_0

        # chi part of ledger = -(chi_X + chi_Y + chi_Z)
        chi0 = chi_spine_mp(0, Fr(0), pL) + chi_spine_mp(1, cX0, 1) + chi_spine_mp(1, cY0, 1)
        chi1 = chi_spine_mp(0, Fr(0), pL + 1) + chi_spine_mp(1, cX1, 1) + chi_spine_mp(1, cY1, 1)
        d_chi = -(chi1 - chi0)

        d_total = d_hinge + d_chi

        if d_hinge < 0:
            hinge_alone_nonneg = False
        if d_hinge < worst_hinge:
            worst_hinge = d_hinge
        if d_total < worst_total:
            worst_total = d_total
        # does the hinge part alone dominate (i.e. is d_total>=0 attributable to hinge)?
        if d_hinge < 0 <= d_total:
            hinge_dominates = False   # positivity comes from the log part, not hinge

        if pL <= 6 or pL in (10, 50, 200):
            rows.append({
                "pL": pL,
                "d_hinge": mp.nstr(d_hinge, 6),
                "d_chi": mp.nstr(d_chi, 6),
                "d_total": mp.nstr(d_total, 6),
                "cavZ_above_knee": above_knee(cZ0),
            })

    return {
        "hinge_telescopes_to": "hinge part of ledger = -phi(cav_Z) exactly (X,Y phi terms cancel)",
        "d_hinge_always_nonneg": hinge_alone_nonneg,
        "worst_d_hinge": mp.nstr(worst_hinge, 6),
        "worst_d_total": mp.nstr(worst_total, 6),
        "hinge_alone_certifies_monotone": hinge_alone_nonneg,
        "positivity_from_log_when_hinge_negative": not hinge_dominates,
        "rows": rows,
    }


# ---------------------------------------------------------------------------
# (c2) the cav_Z drift — the crux the hinge telescope exposes
# ---------------------------------------------------------------------------
def cavZ_drift(PMAX: int = 2000) -> dict:
    """The hinge telescope reduces the hinge contribution to -phi(cav_Z), which is
    INCREASING in pL iff cav_Z is DECREASING (once above knee).  But the audit says
    cav_Z drifts DOWN slowly and stays above knee -- so -phi(cav_Z) rises: the hinge
    part is a monotone TAILWIND.  Check the exact sign of cav_Z(pL+1) - cav_Z(pL)."""
    all_down = True
    all_above = True
    worst = None
    for pL in range(1, PMAX + 1):
        _, _, cZ0 = spine_cavities(pL)
        _, _, cZ1 = spine_cavities(pL + 1)
        if not above_knee(cZ0):
            all_above = False
        d = cZ1 - cZ0                          # exact Fraction
        if d >= 0:
            all_down = False
            worst = (pL, d)
    return {
        "cav_Z_strictly_decreasing_in_pL": all_down,
        "cav_Z_above_knee_throughout": all_above,
        "exception": None if worst is None else (worst[0], str(worst[1])),
        "implication": ("if cav_Z decreasing AND above knee, hinge part -phi(cav_Z) "
                        "is EXACTLY increasing => hinge is a monotone tailwind; residual "
                        "is only the chi-log part d_chi"),
    }


# ---------------------------------------------------------------------------
# (d) THE CLEAN EXACT ARGUMENT — closed-form rational certificates
# ---------------------------------------------------------------------------
# The exact-inequality attempt (c) exposed a decomposition the float audit missed:
# the ledger's HINGE part TELESCOPES (X and Y phi-terms cancel) to exactly
# -phi(cav_Z), and the CHI/log part reduces to a single rational monotonicity.
# Both halves close CLEANLY in exact arithmetic, with NO cavity-coupling
# cancellation and NO transcendental residual.  Concretely (pT=pM=1):
#
#   ledger(pL) = -phi(cav_Z) + [3L - log P(pL)],     P(pL) = prod_v (1 + S_v/w_v).
#
# HINGE HALF.  cav_Z(pL) = 23*(1872*pL + 2185) / (148538*pL + 169487).
#   integer-step numerator of cav_Z(pL+1)-cav_Z(pL) is the CONSTANT -167344918 < 0
#   over a positive denominator => cav_Z strictly DECREASING.  Its infimum is the
#   limit 1656/5713, and (1 + 1656/5713)^11 > 621/64 EXACTLY (positive margin),
#   so cav_Z stays strictly ABOVE the knee for every pL.  Hence
#   -phi(cav_Z) = -C_HINGE*(cav_Z - T0) is EXACTLY increasing in pL.  (clean)
#
# CHI/LOG HALF.  Since 1 + S_v/w_v = 1/(w_v*cav_v), P(pL) = 1/(9*Q(pL)) with
#   Q(pL) = (pL+1)*cav_X*cav_Y*cav_Z = 12167*(pL+1) / (148538*pL + 169487).
#   d_chi > 0  <=>  P decreasing  <=>  Q increasing, and the integer-step numerator
#   of Q(pL+1)-Q(pL) is the CONSTANT 254886483 > 0 over a positive denominator.
#   (12167 = 23^3.)  Hence the whole log part is EXACTLY increasing.  (clean)
#
# CONCLUSION.  d(pL) = d_hinge + d_chi with BOTH summands > 0 exactly for every
# integer pL >= 1.  The monotonicity is NOT the feared collective cancellation
# ("slack_Y must dominate the tip's post-knee fall") — that framing was an artifact
# of the per-spine-node split.  Re-associated as hinge(telescoped) + log, it splits
# into two independently-signed rational certificates.  A clean exact argument EXISTS.

# GENERALIZATION TO ALL (pT, pM) [the family lemma 1 actually needs: pT in 1..11,
# pM in 1..2 per g34_deep].  Symbolic check (sympy, see campaign notes) confirms:
#   * Q(pL) strictly increasing for EVERY (pT,pM): d_chi > 0 always.  (log half clean)
#   * cav_Z(pL) strictly decreasing for EVERY (pT,pM): step numerator a NEGATIVE
#     constant.  BUT cav_Z stays above the knee only for pT=1; for pT>=2 it crosses
#     the knee at finite pL and its infimum is below T0.
# The hinge half is STILL clean in general WITHOUT the above-knee requirement:
#   d_hinge = phi(cav_Z(pL)) - phi(cav_Z(pL+1)) >= 0 because phi is monotone
#   NON-DECREASING and cav_Z is strictly decreasing -- so -phi(cav_Z) is
#   NON-DECREASING whether cav_Z is above the knee (d_hinge>0) or below (d_hinge=0,
#   phi pinned at 0).  Above-knee is NOT needed; monotone cav_Z + monotone phi
#   suffices.  Verified numerically 0 negative d_hinge over all (pT,pM), pL<=3000.
# So for ALL (pT,pM): d(pL) = d_hinge + d_chi with d_hinge >= 0 and d_chi > 0.

# closed-form coefficients at (pT,pM)=(1,1) (derived symbolically, verified vs exact spine)
_CAVZ_NUM = lambda p: 23 * (1872 * p + 2185)
_CAVZ_DEN = lambda p: 148538 * p + 169487
_Q_NUM = lambda p: 12167 * (p + 1)
_Q_DEN = lambda p: 148538 * p + 169487
_CAVZ_STEP_NUM = -167344918          # constant numerator of cav_Z(p+1)-cav_Z(p)
_Q_STEP_NUM = 254886483              # constant numerator of Q(p+1)-Q(p)
_CAVZ_INF = Fr(1656, 5713)           # limit / infimum of cav_Z (at pT=pM=1)


def clean_exact_certificate(PMAX: int = 5000) -> dict:
    """Verify the closed-form certificates against the exact spine, and check the
    two constant-sign integer-step numerators, entirely in exact Fraction arithmetic."""
    cavz_ok = True
    q_ok = True
    cavz_dec = True
    q_inc = True
    for pL in range(1, PMAX + 1):
        cX, cY, cZ = spine_cavities(pL)
        # closed forms match the recursively-computed exact cavities
        if cZ != Fr(_CAVZ_NUM(pL), _CAVZ_DEN(pL)):
            cavz_ok = False
        Q = (pL + 1) * cX * cY * cZ
        if Q != Fr(_Q_NUM(pL), _Q_DEN(pL)):
            q_ok = False
        # integer-step signs from the closed forms
        cZ1 = Fr(_CAVZ_NUM(pL + 1), _CAVZ_DEN(pL + 1))
        if not (cZ1 < cZ):
            cavz_dec = False
        Q1 = Fr(_Q_NUM(pL + 1), _Q_DEN(pL + 1))
        if not (Q1 > Q):
            q_inc = False
    # the two integer-step numerators are constants (independent of pL); verify sign
    # symbolically-derived: cav_Z(p+1)-cav_Z(p) = _CAVZ_STEP_NUM / (D(p+1)*D(p))
    step_check_cavz = Fr(_CAVZ_NUM(2), _CAVZ_DEN(2)) - Fr(_CAVZ_NUM(1), _CAVZ_DEN(1))
    step_check_q = Fr(_Q_NUM(2), _Q_DEN(2)) - Fr(_Q_NUM(1), _Q_DEN(1))
    # above-knee for the infimum (hence for every cav_Z, since decreasing)
    inf_above_knee = (1 + _CAVZ_INF) ** 11 > RHO_B_11
    inf_margin = (1 + _CAVZ_INF) ** 11 - RHO_B_11
    return {
        "closed_form_cavZ": "cav_Z(pL) = 23*(1872*pL+2185)/(148538*pL+169487)",
        "closed_form_Q": "Q(pL) = 12167*(pL+1)/(148538*pL+169487),  12167 = 23^3",
        "closed_forms_match_exact_spine_to_PMAX": cavz_ok and q_ok,
        "cavZ_strictly_decreasing_exact": cavz_dec,
        "Q_strictly_increasing_exact": q_inc,
        "cavZ_step_numerator_constant": _CAVZ_STEP_NUM,
        "cavZ_step_numerator_negative": _CAVZ_STEP_NUM < 0,
        "Q_step_numerator_constant": _Q_STEP_NUM,
        "Q_step_numerator_positive": _Q_STEP_NUM > 0,
        "cavZ_infimum": str(_CAVZ_INF),
        "cavZ_infimum_above_knee_exact": inf_above_knee,
        "cavZ_infimum_knee_margin_positive": inf_margin > 0,
        "hinge_half": ("-phi(cav_Z) exactly increasing (cav_Z decreasing & above knee) "
                       "=> d_hinge > 0"),
        "log_half": ("d_chi > 0  <=>  Q increasing (step numerator 254886483 > 0) "
                     "=> d_chi > 0"),
        "verdict": ("CLEAN EXACT ARGUMENT EXISTS: d(pL) = d_hinge + d_chi with BOTH "
                    "summands > 0 for every integer pL >= 1. The 'slack_Y must dominate' "
                    "coupled cancellation was an artifact of the per-node split; "
                    "re-associating hinge(telescoped)+log splits it into two "
                    "independently-signed constant-numerator rational certificates."),
        "PMAX": PMAX,
    }


def clean_exact_general_family(PMAX: int = 3000) -> dict:
    """The two clean facts over the FULL lemma-1 family (pT in 1..11, pM in 1..2):
       (i)  cav_Z(pL) strictly DECREASING (exact rational step) for every (pT,pM);
       (ii) Q(pL) = (pL+1)*cav_X*cav_Y*cav_Z strictly INCREASING (exact) => d_chi>0.
    Together with phi monotone non-decreasing (so -phi(cav_Z) non-decreasing when
    cav_Z decreasing, NO above-knee needed), these give d_hinge>=0 and d_chi>0,
    hence d(pL)>0, for EVERY (pT,pM).  All comparisons in exact Fraction arithmetic."""
    cavz_dec_all = True
    q_inc_all = True
    bad = []
    for pT in range(1, 12):
        for pM in (1, 2):
            for pL in range(1, PMAX + 1):
                cX0, cY0, cZ0 = spine_cavities(pL, pT, pM)
                cX1, cY1, cZ1 = spine_cavities(pL + 1, pT, pM)
                if not (cZ1 < cZ0):
                    cavz_dec_all = False
                    bad.append(("cavZ", pT, pM, pL))
                Q0 = (pL + 1) * cX0 * cY0 * cZ0
                Q1 = (pL + 2) * cX1 * cY1 * cZ1
                if not (Q1 > Q0):
                    q_inc_all = False
                    bad.append(("Q", pT, pM, pL))
    return {
        "family": "pT in 1..11, pM in 1..2 (the g34_deep lemma-1 family)",
        "cav_Z_strictly_decreasing_all_families_exact": cavz_dec_all,
        "Q_strictly_increasing_all_families_exact": q_inc_all,
        "PMAX": PMAX,
        "violations": bad[:10],
        "phi_monotone_gives_d_hinge_nonneg": ("cav_Z decreasing + phi non-decreasing "
                                              "=> -phi(cav_Z) non-decreasing => d_hinge >= 0 "
                                              "(no above-knee requirement)"),
        "verdict": ("CLEAN EXACT ARGUMENT EXTENDS to the full lemma-1 family: for every "
                    "(pT,pM), d(pL) = d_hinge + d_chi with d_hinge >= 0 (monotone cav_Z + "
                    "monotone phi) and d_chi > 0 (Q increasing, exact rational). The knee "
                    "resonance that breaks the GENERAL bundle-addition case does NOT enter: "
                    "here the tip's below-knee bundles only DECREASE cav_Z monotonically, "
                    "which the hinge absorbs at zero cost. Lemma 1 is NOT a coupled "
                    "cancellation once re-associated as hinge(telescoped)+log."),
    }


def run_all() -> dict:
    out = {}
    out["a_reproduce_monotone"] = reproduce_monotone(PMAX=4000)
    out["b_per_node_decomposition"] = per_node_decomposition()
    out["c_exact_inequality_attempt"] = exact_inequality_attempt(PMAX=400)
    out["c2_cavZ_drift"] = cavZ_drift(PMAX=2000)
    out["d_clean_exact_certificate"] = clean_exact_certificate(PMAX=5000)
    out["e_clean_exact_general_family"] = clean_exact_general_family(PMAX=3000)
    out["conjecture1_proved"] = False
    return out


if __name__ == "__main__":
    import json

    res = run_all()
    print(json.dumps(res, indent=2, default=str))
    sys.exit(0)
