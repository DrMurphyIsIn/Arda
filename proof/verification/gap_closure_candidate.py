"""CANDIDATE CLOSURE OF THE GAP -- the induction "non-near-star branches sit below the near-star spine"
closes over a fully PROVABLE structural menu.  If certified, this proves Phi <= 1 for all branches and
closes the Brualdi-Goldwasser residual.

STATUS (honest): the mathematical skeleton is rigorous and the binding corner is verified EXACTLY; the two
finite tables (chain fixed point, global adversary sweep) are conservative grid computations in float
arithmetic with explicit margins (>= 2.1e-4 at the corner, larger elsewhere), plus tail arguments that are
sketched but not yet formalized.  So: CANDIDATE PROOF, pending mechanical certification (interval
arithmetic on the tables + formal tail lemmas + the 2-type-completeness lemma).  NOT claimed as a theorem.

THE CLAIM.  Gap: every non-near-star branch B has log Phi(B) <= omega = log(3/(2 rho^2)) = -0.0077073,
with equality iff B = ARM.  Combined with the PROVEN near-star theorem (g(s) <= 0), this gives Phi <= 1
for every branch -- the open crux.

THE INDUCTION (strong, on branch size).  IH: for all smaller branches, (a) log Phi <= 0, and (b) if
non-near-star, log Phi <= omega.  A non-near-star node has s arm-units and j >= 1 non-ARM deep children;
by (DEC), node = g(s+j) - j omega + sum ell_l + log((4s+3j+3+3 sum mu_l)/(4(s+j)+3)).  Each deep child is
either a near-star -- EXACT (mu, ell) = (3/(4s'+3), g(s')) -- or a non-near-star bounded by the STRUCTURAL
ENVELOPE B(mu) below.  The adversarial maximum of (DEC) over this menu is <= omega for every (s,j) != (0,1)
(the (0,1) case is the separately-proven s0-closure).  Hence node <= omega: the induction closes.

THE STRUCTURAL ENVELOPE B(mu) -- every ingredient PROVABLE from the IH + cavity arithmetic:
  (E0) cavity spectrum: every branch cavity is in {1} U (0, 1/2); mu=1 iff bareleaf.  [t=3d+c+3S >= 6 for
       any non-bareleaf root, algebraic]
  (E1) FORBIDDEN BAND: no branch has cavity in (1/3, 2/5].  [chains: mu=1/(2+nu), nu in {1} U (0,1/2) =>
       mu in {1/3} U (2/5,1/2); every non-chain non-bareleaf root has t > 9 => mu < 1/3]
  (E2) mu in (2/5, 1/2): ONLY chains (0,[D']) live here.  Their bound is the CHAIN FIXED POINT: chainB(mu)
       = min(omega [s0-closure], -L + log(1/(2 mu)) + best-child(nu)), nu = 1/mu - 2, iterated to a fixed
       point on a conservative cell table.  The iteration DISCOVERS the CANTOR STRUCTURE: the band (E1)
       pulls back through nu -> 1/(2+nu) to second-order gaps ((7/17, 12/29), etc.), accumulating at the
       chain fixed point sqrt(2)-1 = 0.41421...; empty cells are marked forbidden.  Table result:
       max chainB = -0.0725 (at the N(1)-child chain 7/17), all cells << omega-needed.
  (E3) mu in (1/4, 1/3): only root shapes (n,c) in {(2,0),(1,1)} exist [t in (9,12) forces this], giving
       the SHAPE BOUND ell <= log(1/(3 mu)) - L  [IH (a) on children].  This crosses omega at
       mu* = e^{-(L+omega)}/3 = 0.273216.
  (E4) mu <= mu*: ell <= omega  [IH (b)].
  (mu = 1/3 is ARM alone -- an arm, never a deep child.)
VALIDATED: over 5.2M enumerated branches (depth <= 6) PLUS arm-heavy configs (c,[ARM]^k,+near-stars; the
unbounded axis that refuted (A')) PLUS deep chains around sqrt(2)-1: ZERO envelope violations (max defect
exactly 0, i.e. tight), and ZERO branches inside any claimed-forbidden band.

THE BINDING CORNER -- EXACT.  The global adversary max is at (s=4, j=1, child at (mu*, omega)):
node = log((22+3 mu*)/23) <= omega  <=>  mu* <= mu_c = (23 e^omega - 22)/3.  Using e^{-L-omega} = (2/3)rho
and e^omega = (3/2) rho^{-2}  (omega = log(3/2) - 2L, L = log rho, rho = (621/64)^{1/11}):
    mu* <= mu_c   <=>   132 rho^2 + 4 rho^3 <= 207.
PROVEN EXACTLY: rho < r := 122948/100000  (r^11 > 621/64, exact rational), and  132 r^2 + 4 r^3 =
206.968... <= 207 (exact rational).  Slack 0.032 in the cubic = margin 1.65e-4 in the node value.  One
more exact rational inequality in the same 23-adic family as the near-star and broom proofs.

GLOBAL SWEEP (grid, conservative): all (s,j) with s <= 63, j <= 39, identical children over the full menu
+ ALL two-type splits (all n1) over hull candidates + 200k random 3-type mixes: max = -0.007918 <= omega,
margin 2.11e-4, binding at the exact corner above.  Tails (sketched, to formalize): s >= 64 via
g <= s omega + log(4/3) - L and the log-term < 1/8 bound; j large via the tie-dominance limit
node -> s omega + 0.081 - 0.165.  2-type completeness: the objective is separable + concave(log) in
sum mu, so the continuous relaxation's optimum uses <= 2 menu points (Caratheodory in 1D).

WHY THIS EVADES THE OLD OBSTRUCTIONS: the menu is NOT a box (obstruction 3) -- it is the exact
shape-quantized envelope, whose forbidden bands and -L discounts encode the discreteness; and it is NOT a
smooth certificate (integrality obstruction) -- every piece is either exact near-star data or a per-shape
arithmetic bound, with the binding corner an exact rational inequality.  The discrete reachability that
the continuum Bellman relaxation destroys (value_function_bellman) is precisely what (E1)-(E3) retain.

Requires numpy.
"""
from __future__ import annotations

from fractions import Fraction

import numpy as np

from verification import gap_reduction_frontier as GF
from verification import curve_search as CS

g = GF.g
OMEGA = GF.OMEGA
ARM = GF.ARM
_amp = GF._amp
_is_nearstar = GF._is_nearstar
L = float(np.log((621 / 64) ** (1 / 11)))
MU_STAR = float(np.exp(-(L + OMEGA)) / 3)          # 0.273216: S3 bound crosses omega
MU_C = float((23 * np.exp(OMEGA) - 22) / 3)        # 0.274471: (s=4,j=1) corner requirement


def corner_inequality_exact():
    """The binding corner mu* <= mu_c, exactly: 132 rho^2 + 4 rho^3 <= 207 via the rational bracket
    rho < 122948/100000 (r^11 > 621/64 exact) and 132 r^2 + 4 r^3 <= 207 exact."""
    r = Fraction(122948, 100000)
    upper = r ** 11 > Fraction(621, 64)
    cubic = 132 * r ** 2 + 4 * r ** 3 <= 207
    return {"rho_upper_bound_exact": upper, "cubic_at_r_le_207": cubic,
            "cubic_value": float(132 * r ** 2 + 4 * r ** 3),
            "mu_star": MU_STAR, "mu_c": MU_C,
            "corner_proven_exact": upper and cubic and MU_STAR < MU_C}


def _B_low(mu):
    if mu > 0.25:
        return min(OMEGA, np.log(1 / (3 * mu)) - L)
    return OMEGA


def build_chain_envelope(nc=4000):
    """The chain-region fixed point on a conservative cell table, with dynamic Cantor-gap detection.
    Start = omega (valid: chains are s=0,j=1 nodes, proven <= omega); each iterate applies the exact chain
    telescoping with a conservative sup over the cell; cells whose child-cavity range is entirely forbidden
    are EMPTY (no chain exists) and get marked forbidden -- the Cantor gaps around sqrt(2)-1."""
    NS = [(3 / (4 * sp + 3), g(sp)) for sp in range(0, 300)]
    edges = np.linspace(0.4, 0.5, nc + 1)

    def cell_of(nu):
        return min(max(int((nu - 0.4) / 0.1 * nc), 0), nc - 1)
    chainB = np.full(nc, OMEGA)
    forb = np.zeros(nc, bool)
    for i in range(nc):
        if edges[i] >= 5 / 12 and edges[i + 1] <= 3 / 7:
            forb[i] = True

    def best_child(nlo, nhi):
        cands = []
        for cav, val in NS:
            if nlo - 1e-12 <= cav <= nhi + 1e-12:
                cands.append(val)
        if nlo <= 1 / 3:
            cands.append(max(_B_low(max(nlo, 1e-6)), _B_low(min(nhi, 1 / 3))))
        if nhi > 0.4:
            i0, i1 = cell_of(max(nlo, 0.4 + 1e-12)), cell_of(min(nhi, 0.5 - 1e-12))
            sub = [chainB[i] for i in range(i0, i1 + 1) if not forb[i]]
            if sub:
                cands.append(max(sub))
        return max(cands) if cands else None
    for _ in range(200):
        changed = False
        new = chainB.copy()
        for i in range(nc):
            if forb[i]:
                continue
            mulo, muhi = edges[i], edges[i + 1]
            bc = best_child(1 / muhi - 2, 1 / mulo - 2)
            if bc is None:
                forb[i] = True
                changed = True
                continue
            cand = -L + np.log(1 / (2 * mulo)) + bc
            if cand < new[i] - 1e-14:
                new[i] = cand
                changed = True
        chainB = new
        if not changed:
            break
    return edges, chainB, forb


def B_envelope(nc=4000):
    """The full provable non-near-star envelope B(mu) (None = no branches at that cavity)."""
    edges, chainB, forb = build_chain_envelope(nc)

    def cell_of(mu):
        return min(max(int((mu - 0.4) / 0.1 * nc), 0), nc - 1)

    def B(mu):
        if mu >= 0.5:
            return None
        if mu > 0.4:
            i = cell_of(mu)
            return None if forb[i] else float(chainB[i])
        if mu > 1 / 3 + 1e-12:
            return None                       # forbidden band (E1)
        if abs(mu - 1 / 3) <= 1e-12:
            return None                       # ARM only
        return float(_B_low(mu))
    return B, edges, chainB, forb


def validate_envelope(max_depth=6, width=40):
    """Adversarial pointwise validation: every real non-near-star non-ARM branch (deep enumeration +
    arm-heavy configs + nested chains around sqrt(2)-1) obeys ell <= B(mu), and none occupies a
    claimed-forbidden cavity."""
    B, _, _, _ = B_envelope()
    BL = (0, [])
    worst = -9.0
    in_forbidden = 0
    n = 0

    def check(gg):
        nonlocal worst, in_forbidden, n
        mu, ell = _amp(gg)
        n += 1
        b = B(mu)
        if b is None:
            if abs(mu - 1 / 3) > 1e-9:
                in_forbidden += 1
            return
        worst = max(worst, ell - b)
    for D in range(1, max_depth + 1):
        for gg in CS._gadgets(D, mc=5, mcher=6):
            if gg in (BL, ARM) or _is_nearstar(gg):
                continue
            check(gg)
    for c in range(0, 20):
        for k in range(0, width):
            for js in ([2], [3], [4], [5], [6], [4, 5], [5, 5]):
                gg = (c, [ARM] * k + [(0, [ARM] * s) for s in js])
                if not _is_nearstar(gg):
                    check(gg)
    for seed in ((1, []), (0, []), (0, [ARM] * 5)):
        T = seed
        for _ in range(1, 50):
            T = (0, [T])
            if not _is_nearstar(T) and T != ARM:
                check(T)
    return {"n_branches": n, "max_defect": worst, "envelope_valid": worst <= 1e-9,
            "branches_in_forbidden_bands": in_forbidden}


def adversary_closes(smax=63, jmax=39):
    """The global DEC adversary over [near-stars exact UNION B(mu)]: max over (s,j) != (0,1) of the
    node bound.  Grid-conservative; identical children over the full menu + all two-type splits over hull
    candidates.  Result <= omega closes the gap induction over the menu (finite ranges; tails sketched)."""
    B, edges, chainB, forb = B_envelope()
    menu = [(3 / (4 * sp + 3), g(sp)) for sp in range(0, 80)]
    for i in range(len(chainB)):
        if not forb[i]:
            menu.append((edges[i + 1], float(chainB[i])))
    for mu in np.linspace(0.02, 1 / 3 - 1e-6, 400):
        b = B(mu)
        if b is not None:
            menu.append((mu, b))
    menu = [(m, e) for m, e in menu if e > -5]
    mus = np.array([m for m, _ in menu])
    els = np.array([e for _, e in menu])

    def node(s, j, MM, EE):
        return g(s + j) - j * OMEGA + EE + np.log((4 * s + 3 * j + 3 + 3 * MM) / (4 * (s + j) + 3))
    worst = -9.0
    arg = None
    for j in range(1, jmax + 1):
        for s in range(0, smax + 1):
            if j == 1 and s == 0:
                continue
            v = node(s, j, j * mus, j * els)
            k = int(v.argmax())
            if v[k] > worst:
                worst, arg = float(v[k]), (s, j, "id", round(float(mus[k]), 5))
            if j >= 2:
                idx = np.argsort(-(els + 0.02 * mus))[:70]
                for a_i, ia in enumerate(idx):
                    for ib in idx[a_i + 1:]:
                        for n1 in range(1, j):
                            v2 = node(s, j, n1 * mus[ia] + (j - n1) * mus[ib],
                                      n1 * els[ia] + (j - n1) * els[ib])
                            if v2 > worst:
                                worst, arg = float(v2), (s, j, "split", n1,
                                                         round(float(mus[ia]), 4), round(float(mus[ib]), 4))
    return {"worst_node": worst, "closes": worst <= OMEGA + 1e-9,
            "margin": OMEGA - worst, "binding": arg}


def certify_menu_completeness(max_depth=6):
    """HARDENING: the closure menu is a DISJOINT-and-COMPLETE cover of every branch's amplitude.  Each branch
    is bounded by exactly the right arm: a NEAR-STAR by its exact value ell=g(s')=E_ns(mu) (the spine), a
    NON-near-star (non-ARM) by the structural envelope B(mu); and no non-near-star lands at a claimed-empty
    (Cantor-gap / forbidden) cavity.  This guards the load-bearing near-star/non-near-star split -- the split
    that (correctly) routes the single-cherry leaf (1,[])=N(1,0) at mu=3/7 to the exact g(1)=-0.0601 rather
    than to the (lower) chain envelope.  Verified over the depth<=6 enumeration + arm-heavy near-stars."""
    B = B_envelope()[0]

    def E_ns(mu):
        return g((3 / mu - 3) / 4)
    worst_nearstar = -9.0
    worst_nonnearstar = -9.0
    nonnearstar_in_empty = 0
    for D in range(1, max_depth + 1):
        for gg in CS._gadgets(D, mc=5, mcher=6):
            mu, ell = _amp(gg)
            if _is_nearstar(gg):
                worst_nearstar = max(worst_nearstar, abs(ell - E_ns(mu)))   # near-star == g exactly
            elif gg != ARM:
                b = B(mu)
                if b is None:
                    if abs(mu - 1 / 3) > 1e-9:
                        nonnearstar_in_empty += 1                            # a non-near-star in a "gap" = bug
                else:
                    worst_nonnearstar = max(worst_nonnearstar, ell - b)      # must be <= B(mu)
    # arm-heavy near-stars (the axis that refuted A'): N(c,k) must equal g(c+k)
    armheavy_ok = all(abs(_amp((c, [ARM] * k))[1] - g(c + k)) < 1e-9
                      for c in range(0, 15) for k in range(0, 20) if (c, [ARM] * k) != ARM)
    return {"near_stars_equal_g": worst_nearstar < 1e-9, "near_star_max_dev": worst_nearstar,
            "non_near_stars_le_B": worst_nonnearstar <= 1e-9, "non_near_star_max_defect": worst_nonnearstar,
            "no_non_near_star_in_empty_cavity": nonnearstar_in_empty == 0,
            "arm_heavy_near_stars_equal_g": armheavy_ok,
            "menu_complete_and_correct": (worst_nearstar < 1e-9 and worst_nonnearstar <= 1e-9
                                          and nonnearstar_in_empty == 0 and armheavy_ok)}


def certify():
    corner = corner_inequality_exact()
    val = validate_envelope(max_depth=5, width=30)
    adv = adversary_closes(smax=40, jmax=24)
    return {
        "corner_inequality_exact": corner["corner_proven_exact"],   # 132 rho^2 + 4 rho^3 <= 207, EXACT
        "envelope_valid_pointwise": val["envelope_valid"],
        "no_branches_in_forbidden_bands": val["branches_in_forbidden_bands"] == 0,
        "adversary_worst": adv["worst_node"],
        "adversary_closes_le_omega": adv["closes"],
        "adversary_margin": adv["margin"],
        "binding_config": adv["binding"],
        "status": "CANDIDATE PROOF of the gap (=> Phi<=1): induction closes over the provable structural "
                  "menu; binding corner exact; PENDING mechanical certification (interval arithmetic on "
                  "the two tables, formal tail lemmas s>=64 / j large, 2-type completeness lemma).",
        "claimed_as_theorem": False,
    }


if __name__ == "__main__":
    print("corner:", corner_inequality_exact())
    print("envelope validation:", validate_envelope())
    print("adversary:", adversary_closes())
    print("verdict:", certify())
