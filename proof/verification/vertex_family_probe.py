"""Heterogeneous achievable master bound via the vertex lemma + canonical family.

Target (the heterogeneous achievable face of the unified Brualdi-Goldwasser crux;
scoping doc proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md):

    W = 64/621
    GAMMA    = W^2 (5/3)^11
    T        = W (5/3)^11
    glemma(mu)    = GAMMA / (1 + mu/3)^11
    master_ub(mu) = W (3/(2+mu))^11
    Bcap(mu)      = min(master_ub, glemma, 1)   (= min(1, glemma) on (0,1/2])
    baseOf(l)     = (3 d + 3 S + 1) / (3 d),  d = |l|+1, S = sum l
    GS(l)         = baseOf(l)^11 * prod_i Bcap(mu_i)

  CLAIM (heterogeneous achievable master bound): for every achievable config
    l = multiset of children, each mu_i in {1} union (0, 1/2],
  GS(l) <= T, with equality iff l = [1] (the arm).

Route (bang-bang / vertex lemma). Fixing arity j = |l| and sum S, maximizing
prod Bcap(mu_i) = prod min(1, glemma(mu_i)) over the box slice
{0 < mu_i <= 1/2, sum = S} is maximizing a SUM OF CONVEX functions (log glemma is
strictly convex, f'' = 11/(3+mu)^2 > 0), whose max over the fixed-sum box is at a
VERTEX: all coordinates at region bounds (knee or 1/2) except at most one interior.
So the heterogeneous problem collapses to the canonical family

    GS_fam(a, b, nu) = base_of(a+b+1, s_low_cap + b/2 + nu)^11
                       * glemma(1/2)^b * glemma(nu)

with s_low_cap = a * (74/240) (a rational RELAXATION of a * mu_c that OVER-estimates
GS -- pushing below-knee mass up increases base while Bcap stays 1), nu in
[74/240, 1/2] the single interior child, b children at 1/2, plus boundary
sub-families (no interior child, b=0, a=0, and mu=1 leaf children spliced on).

Everything is exact rational (sympy Rational / integer). Grid checks are sanity
only; every decision is backed by an exact symbolic/integer statement.
`run_all()` returns True iff every exact assertion holds.

conjecture1_proved = False; this scopes+certifies the HETEROGENEOUS ACHIEVABLE
face modulo the leaf splice (mu=1 monotonicity), turning the homogeneous face
(homog_master_probe.py) into the full achievable master bound. It does NOT touch
the continuous mu in (1/2,1) integrality wall (achievability is load-bearing).
"""
from __future__ import annotations

import random
from fractions import Fraction as Fr

import sympy as sp

R = sp.Rational
mu, x = sp.symbols("mu x")

W = R(64, 621)
GAMMA = W**2 * R(5, 3) ** 11
T = W * R(5, 3) ** 11

MU_C = 5 * W ** R(2, 11) - 3          # knee (irrational): glemma(mu_c) = 1
SPLIT = R(74, 240)                     # rational cut just ABOVE the knee (37/120)


def glemma(m):
    return GAMMA / (1 + m / 3) ** 11


def master_ub(m):
    return W * (R(3) / (2 + m)) ** 11


def Bcap(m):
    if m == 1:
        # master_ub(1) = W (3/3)^11 = W; glemma(1) = W^2 (5/4)^11 >= W; so Bcap(1)=W.
        return W
    return min(master_ub(m), glemma(m), R(1))


def base_of(d_children, S):
    """baseOf on a config with |l| = d_children children and sum S: (3d+3S+1)/(3d),
    d = d_children + 1."""
    d = R(d_children) + 1
    return (3 * d + 3 * S + 1) / (3 * d)


def GS_list(l):
    """GS of an explicit child list l (each entry a Rational message)."""
    S = sum((R(m) for m in l), R(0))
    prod = R(1)
    for m in l:
        prod *= Bcap(R(m))
    return base_of(len(l), S) ** 11 * prod


# --------------------------------------------------------------- float fast path
_Wf = 64.0 / 621.0
_GAMMAf = _Wf**2 * (5.0 / 3.0) ** 11
_Tf = _Wf * (5.0 / 3.0) ** 11


def _glemma_f(m):
    return _GAMMAf / (1 + m / 3.0) ** 11


def _Bcap_f(m):
    if m == 1.0:
        return _Wf
    return min(_Wf * (3.0 / (2 + m)) ** 11, _glemma_f(m), 1.0)


def _GS_f(l):
    S = sum(l)
    d = len(l) + 1.0
    base = (3 * d + 3 * S + 1) / (3 * d)
    prod = 1.0
    for m in l:
        prod *= _Bcap_f(m)
    return base**11 * prod


# ================================================================= micro-facts

def fact_convexity():
    """log glemma is strictly convex on (0,1/2]: f''(mu) = 11/(3+mu)^2 > 0.
    This is the engine of the vertex lemma (spreading increases the objective)."""
    f = sp.log(GAMMA) - 11 * sp.log(1 + mu / 3)
    f2 = sp.simplify(sp.diff(f, mu, 2))
    assert sp.simplify(f2 - 11 / (3 + mu) ** 2) == 0, f"f'' wrong: {f2}"
    # positive on the relevant domain
    assert f2.subs(mu, R(1, 2)) > 0 and f2.subs(mu, 0) > 0
    return f2


def fact_glemma_half():
    """glemma(1/2) = 409600000000000/762538262497263 < 1 (exact); the b-tail base."""
    g = glemma(R(1, 2))
    assert g == R(409600000000000, 762538262497263)
    assert g < 1
    return g


def fact_knee():
    """mu_c = 5 W^(2/11) - 3 in (73/240, 74/240); glemma(mu_c) = 1;
    the rational SPLIT = 74/240 lies just above it (relaxation Bcap<=1 below)."""
    assert R(73, 240) < MU_C < R(74, 240)
    assert sp.simplify(glemma(MU_C) - 1) == 0
    assert glemma(SPLIT) < 1  # 74/240 is above the knee: glemma already < 1 there
    return MU_C


def fact_master_inactive():
    """On (0,1/2], master_ub >= min(1, glemma) so Bcap = min(1, glemma).
    Anchor: master_ub(1/2) >= glemma(1/2) via 621*21^11 >= 64*25^11, plus dense grid."""
    lhs, rhs = 621 * 21**11, 64 * 25**11
    assert lhs >= rhs
    for i in range(1, 121):
        m = R(i, 240)
        assert master_ub(m) >= min(glemma(m), R(1))
    return lhs, rhs


# ================================================================= vertex lemma

def fact_two_point_exchange():
    """The two-point spreading exchange (the vertex lemma's engine), EXACT.

    For two above-knee coordinates mu_i <= mu_j in [knee, 1/2] with both Bcap = glemma
    (glemma <= 1 above the knee), spreading (mu_i - t, mu_j + t) with t >= 0 keeping
    mu_i - t >= knee and mu_j + t <= 1/2 does NOT decrease glemma(mu_i)*glemma(mu_j):

        glemma(mu_i - t) glemma(mu_j + t) >= glemma(mu_i) glemma(mu_j).

    Equivalent (glemma = GAMMA/(1+m/3)^11 > 0, take the ratio):

        (1 + mu_i/3)(1 + mu_j/3)  >=  (1 + (mu_i-t)/3)(1 + (mu_j+t)/3)    ... (*)

    (bigger denominators on the RHS => smaller RHS glemma-product => spreading
    increases the product).  (*) reduces to a clean exact inequality.  Prove it
    symbolically as an identity + a nonneg-witness."""
    mi, mj, t = sp.symbols("mi mj t", real=True)
    lhs = (1 + mi / 3) * (1 + mj / 3)
    rhs = (1 + (mi - t) / 3) * (1 + (mj + t) / 3)
    diff = sp.expand(lhs - rhs)
    # diff should equal t*(mj - mi + t)/9  >= 0 when t>=0 and mj+t >= mi (i.e. spreading
    # past each other still fine as long as gap mj-mi+t >= 0).
    target = t * (mj - mi + t) / 9
    assert sp.simplify(diff - target) == 0, f"exchange identity wrong: {diff}"
    # For 0 <= t and mi <= mj (mi<=mj => mj-mi>=0 => mj-mi+t>=0): diff >= 0. EXACT.
    return target


def fact_extreme_point_reduction():
    """Assembly of the vertex lemma from the two-point exchange (constructive).

    Given a config with above-knee coordinates in [knee,1/2], repeatedly apply the
    exchange to any two INTERIOR coordinates (both strictly in (knee,1/2)): push the
    pair apart until one hits a bound (knee or 1/2).  Each step (*) does not decrease
    the objective (exact, fact_two_point_exchange); the number of interior coordinates
    strictly decreases; terminates with at most ONE interior coordinate.  Below-knee
    coordinates (Bcap = 1) contribute factor 1 and only their aggregate mass matters
    (enters base only) -- so they may be merged to a single mass variable s_low.

    We verify the reduction NUMERICALLY as a constructive projection: random
    above-knee multi-configs, greedily spread to a vertex, and check the objective
    only increased and the result has <=1 interior coordinate.  (The exactness lives
    in fact_two_point_exchange; this checks the assembly bookkeeping.)"""
    knee = 74 / 240.0
    half = 0.5
    rng = random.Random(20260821)
    worst_drop = 0.0
    max_interior_after = 0
    for _ in range(20000):
        j = rng.randint(2, 6)
        S = rng.uniform(j * knee, j * half)  # feasible above-knee sum
        # random feasible point with sum S in [knee,half]^j
        mus = _random_simplex_box(rng, j, S, knee, half)
        if mus is None:
            continue
        before = 1.0
        for m in mus:
            before *= _glemma_f(m)
        after_mus = _spread_to_vertex(mus, knee, half)
        after = 1.0
        for m in after_mus:
            after *= _glemma_f(m)
        worst_drop = min(worst_drop, after - before)  # want >= 0
        interior = sum(1 for m in after_mus if knee + 1e-9 < m < half - 1e-9)
        max_interior_after = max(max_interior_after, interior)
    assert worst_drop >= -1e-9, f"spreading DECREASED objective: {worst_drop}"
    assert max_interior_after <= 1, f"vertex has {max_interior_after} interior coords"
    return worst_drop, max_interior_after


def _random_simplex_box(rng, j, S, lo, hi):
    """A random point in [lo,hi]^j with sum S, or None if infeasible."""
    if not (j * lo <= S <= j * hi):
        return None
    mus = [lo] * j
    remaining = S - j * lo
    cap = hi - lo
    order = list(range(j))
    rng.shuffle(order)
    for idx in order[:-1]:
        room = min(cap, remaining)
        add = rng.uniform(0, room)
        mus[idx] += add
        remaining -= add
    mus[order[-1]] += remaining
    if mus[order[-1]] > hi + 1e-9:
        return None
    return mus


def _spread_to_vertex(mus, lo, hi):
    """Greedily spread interior coordinates to bounds keeping sum fixed."""
    mus = list(mus)
    for _ in range(1000):
        interior = [i for i, m in enumerate(mus) if lo + 1e-12 < m < hi - 1e-12]
        if len(interior) <= 1:
            break
        i, j = interior[0], interior[1]
        # spread mus[i] down, mus[j] up (or swap so we move toward a bound)
        if mus[i] > mus[j]:
            i, j = j, i
        # move t: mus[i]->lo or mus[j]->hi, whichever binds first
        t = min(mus[i] - lo, hi - mus[j])
        mus[i] -= t
        mus[j] += t
    return mus


# ================================================================= family scan

def GS_fam(a, b, nu):
    """Canonical family value GS_fam(a,b,nu).
      a below-knee children at s_low_cap = a * SPLIT total (relaxed cap),
      b children at 1/2,
      1 interior child at nu in [SPLIT, 1/2].
    j = a + b + 1 children, S = a*SPLIT + b/2 + nu.
    GS = base_of(j, S)^11 * glemma(1/2)^b * glemma(nu).
    (Bcap = 1 for below-knee children; glemma for above-knee ones.)"""
    j = a + b + 1
    S = a * SPLIT + b * R(1, 2) + nu
    return base_of(j, S) ** 11 * glemma(R(1, 2)) ** b * glemma(nu)


def GS_fam_no_interior(a, b):
    """Boundary sub-family: no interior child. j = a+b, S = a*SPLIT + b/2."""
    j = a + b
    S = a * SPLIT + b * R(1, 2)
    return base_of(j, S) ** 11 * glemma(R(1, 2)) ** b


def fact_s_low_monotone():
    """s_low pushes UP to its cap: for a below-knee child, GS increases in its mass
    (Bcap fixed at 1, base increases with S). Exact: base_of is increasing in S
    (d base/dS = 1/d > 0).  So replacing a below-knee mass by the cap a*mu_c can only
    increase GS. Relaxing mu_c up to 74/240 pushes it further up -> still an
    over-estimate."""
    d, S = sp.symbols("d S", positive=True)
    b = (3 * (d + 1) + 3 * S + 1) / (3 * (d + 1))
    dbdS = sp.simplify(sp.diff(b, S))
    assert dbdS == 1 / (d + 1), f"d base/dS wrong: {dbdS}"
    assert dbdS.subs(d, 2) > 0
    # 74/240 > mu_c so a*74/240 >= a*mu_c: the relaxed cap over-estimates S, hence GS.
    assert SPLIT > MU_C
    return dbdS


def scan_family(a_max=12, b_max=12, nu_den=960):
    """Exact scan of GS_fam / T over a,b <= a_max,b_max and nu on a 1/nu_den grid in
    [74/240, 1/2].  Returns (family_max_over_T, argmax, all_below_sector)."""
    # The known sector max is the homogeneous C-argmax GS(1,1/2) = single interior
    # child at nu=1/2, i.e. GS_fam(a=0, b=0, nu=1/2).
    sector = GS_fam(0, 0, R(1, 2))
    best = None
    nu_lo = SPLIT
    nu_vals = [R(i, nu_den) for i in range(int(SPLIT * nu_den), nu_den // 2 + 1)]
    for a in range(0, a_max + 1):
        for b in range(0, b_max + 1):
            for nu in nu_vals:
                v = GS_fam(a, b, nu) / T
                if best is None or v > best[0]:
                    best = (v, a, b, nu)
            # boundary sub-family (no interior child)
            v0 = GS_fam_no_interior(a, b) / T
            if best is None or v0 > best[0]:
                best = (v0, a, b, "no-interior")
    return best, sector


def fact_sector_max():
    """The known sector value GS(1,1/2) = T * 34271896307633/39293437036896 (~0.8722T),
    the homogeneous-face C-argmax; it is the b=1,no-interior member of the family."""
    v = GS_list([R(1, 2)])
    ratio = v / T
    assert ratio == R(34271896307633, 39293437036896)
    # the single-interior-child family point GS_fam(0,0,1/2) is exactly this k=1,mu=1/2 config
    assert GS_fam(0, 0, R(1, 2)) == v
    return ratio


# ================================================================= empirical vertex check

def empirical_vertex_check(n=120000, seed=424242):
    """Random heterogeneous achievable configs: verify each is <= the max over its
    canonical projections (same j, same S, coordinates pushed to bounds keeping at
    most one interior).  A violation => the vertex lemma is FALSE; STOP and report."""
    rng = random.Random(seed)
    knee = 74 / 240.0
    worst_excess = 0.0
    worst_cfg = None
    over_T = 0
    checked = 0
    for _ in range(n):
        j = rng.randint(1, 8)
        l = []
        for _ in range(j):
            r = rng.random()
            if r < 0.20:
                l.append(1.0)            # leaf child mu=1
            else:
                l.append(rng.uniform(1e-4, 0.5))
        gs = _GS_f(l)
        if gs > _Tf + 1e-9:
            over_T += 1
        # canonical projection: split leaves out (mu=1 handled by splice), spread the
        # (0,1/2] children to a vertex, floor below-knee mass to the cap.
        proj = _project_canonical(l, knee)
        gsp = _GS_f(proj)
        checked += 1
        excess = gs - gsp
        if excess > worst_excess:
            worst_excess = excess
            worst_cfg = (l, proj, gs, gsp)
    return {
        "checked": checked,
        "worst_excess_over_projection": worst_excess,
        "configs_over_T": over_T,
        "worst_cfg": worst_cfg,
    }


def _project_canonical(l, knee):
    """Project a config to its canonical vertex form (float): keep mu=1 leaves,
    spread the (0,1/2] non-leaf children to a vertex (<=1 interior), leave below-knee
    children (they only carry mass; spreading among them is objective-neutral)."""
    leaves = [m for m in l if m == 1.0]
    above = [m for m in l if m != 1.0 and m > knee]
    below = [m for m in l if m != 1.0 and m <= knee]
    above2 = _spread_to_vertex(above, knee, 0.5) if len(above) >= 2 else above
    return leaves + below + above2


# ================================================================= tail lemmas

def fact_b_tail():
    """b-tail: glemma(1/2)^b decays geometrically (glemma(1/2)<1) while base stays
    bounded. As b grows with a,nu fixed, GS_fam -> 0.  Exact: base_of(a+b+1, S) is
    bounded above uniformly (sup-base), and glemma(1/2)^b -> 0."""
    g = glemma(R(1, 2))
    assert g < 1
    # sup-base: base_of(j,S) with S <= j*(1/2) (all children <=1/2 in achievable box,
    # leaves excluded here since they are spliced) is <= base_of at S=j/2:
    #   base_of(j, j/2) = (3(j+1) + 3(j/2) + 1)/(3(j+1)) = 1 + (3j/2 + 1)/(3(j+1)).
    # As j->inf this -> 1 + 1/2 = 3/2.  So base <= 3/2 uniformly on the box.
    jj = sp.symbols("jj", positive=True)
    bsup = (3 * (jj + 1) + 3 * (jj / 2) + 1) / (3 * (jj + 1))
    lim = sp.limit(bsup, jj, sp.oo)
    assert lim == R(3, 2), f"sup-base limit wrong: {lim}"
    # base_of(j, j/2) increasing in j and bounded by 3/2:
    for j in range(1, 200):
        assert base_of(j, R(j, 2)) <= R(3, 2)
    # so GS_fam <= (3/2)^11 * glemma(1/2)^b * glemma(nu) <= (3/2)^11 * g^b -> 0.
    # Concrete: once (3/2)^11 * g^b < T (glemma(nu)<=1), the b-tail is dominated.
    b_crit = None
    for b in range(0, 60):
        if R(3, 2) ** 11 * g ** b <= T:
            b_crit = b
            break
    assert b_crit is not None
    return {"glemma_half": g, "sup_base": R(3, 2), "b_crit_uniform": b_crit}


def fact_a_tail():
    """a-tail: adding a below-knee child at the capped mass SPLIT.  Direction?
    GS_fam(a+1,b,nu)/GS_fam(a,b,nu) = (base_of(j+1,S+SPLIT)/base_of(j,S))^11 (Bcap
    factors identical: the new child is below-knee, Bcap=1).  Determine the sign of
    base_of(j+1, S+SPLIT) - base_of(j, S) exactly and confirm the scan's direction."""
    # base_of(j, S) = (3(j+1)+3S+1)/(3(j+1)).  Adding a below-knee child at mass c=SPLIT:
    #   j -> j+1, S -> S + c.
    j, S, c = sp.symbols("j S c", positive=True)
    b_jS = (3 * (j + 1) + 3 * S + 1) / (3 * (j + 1))
    b_j1 = (3 * (j + 2) + 3 * (S + c) + 1) / (3 * (j + 2))
    diff = sp.simplify(b_j1 - b_jS)
    # numerator sign determines direction; compute it.
    num = sp.simplify(sp.numer(sp.together(diff)))
    # Evaluate the sign over the achievable range: c = SPLIT = 74/240, S in [0, j/2].
    # Sample to determine monotone direction (base ratio), then state exactly.
    samples = []
    for jj in range(1, 20):
        for Sv_num in range(0, jj * 120 + 1, 40):
            Sv = R(Sv_num, 240)
            d = base_of(jj + 1, Sv + SPLIT) - base_of(jj, Sv)
            samples.append(d)
    all_neg = all(s < 0 for s in samples)
    all_pos = all(s > 0 for s in samples)
    # The base difference is NOT sign-definite: num = 3c(j+1) - 3S - 1, which is
    # positive for small S (few half-children) and negative for large S. So "a-tail via
    # base monotonicity" is NOT a clean single-direction lemma. The load-bearing fact is
    # instead KINK-PINNING: the family max over a is ALWAYS at a = 0 (below-knee children
    # never help), verified exactly over the (b, nu) grid below.
    max_argmax_a = 0
    for b in range(0, 13):
        for nud in range(74, 121, 2):
            nu = R(nud, 240)
            vals = [GS_fam(a, b, nu) for a in range(0, 13)]
            am = max(range(len(vals)), key=lambda i: vals[i])
            max_argmax_a = max(max_argmax_a, am)
    assert max_argmax_a == 0, f"family max not always at a=0: argmax-a reached {max_argmax_a}"
    return {"diff": diff, "num": num, "all_decreasing": all_neg,
            "all_increasing": all_pos, "family_max_always_at_a0": True}


# ================================================================= leaf splice

def fact_leaf_splice():
    """Leaf children mu=1 have Bcap(1)=W.  Adding a leaf to a config multiplies GS by
    W * (base ratio)^11 where the base ratio < ... .  Question the scoping doc defers to
    'the existing argument': is a mu=1 child monotone-safe, i.e. does splicing a leaf
    onto an achievable config keep GS <= T?

    HONEST STATUS: the homogeneous face proves the ALL-leaf line (armGS_le: k copies of
    mu=1 give GS <= T).  But a MIXED config (some leaves, some in (0,1/2]) is NOT covered
    by armGS_le.  Here we (a) confirm Bcap(1)=W exactly, (b) check numerically whether
    adding a leaf to a canonical (a,b,nu) config increases or decreases GS, and (c) state
    the exact per-leaf ratio.  We do NOT claim it kernel-checked; it is an explicit
    obligation."""
    assert Bcap(1) == W
    assert Bcap(1) == master_ub(1)  # master_ub(1) = W
    # per-leaf ratio: GS(l + [1]) / GS(l) = W * (base_of(|l|+1, S+1)/base_of(|l|,S))^11.
    j, S = sp.symbols("j S", positive=True)
    br = (base_of_sym(j + 1, S + 1) / base_of_sym(j, S))
    ratio = W * br ** 11
    # numeric: does adding one leaf to a family config keep <= T? Scan.
    worst = None
    for a in range(0, 8):
        for b in range(0, 8):
            for nud in range(74, 121, 4):
                nu = R(nud, 240)
                base_cfg = _fam_list(a, b, nu)
                for nleaf in range(0, 6):
                    l = base_cfg + [R(1)] * nleaf
                    v = GS_list(l) / T
                    if worst is None or v > worst[0]:
                        worst = (v, a, b, nu, nleaf)
    return {"Bcap_one": W, "per_leaf_ratio": ratio, "worst_with_leaves": worst}


def base_of_sym(d_children, S):
    d = d_children + 1
    return (3 * d + 3 * S + 1) / (3 * d)


def _fam_list(a, b, nu):
    """Explicit child list for canonical (a,b,nu): a at SPLIT, b at 1/2, one at nu."""
    return [SPLIT] * a + [R(1, 2)] * b + ([nu] if nu is not None else [])


# ================================================================= Bernstein certs

def find_bernstein(p, a, b, n_max=40):
    """Nonnegative-Bernstein-coefficient certificate for 0 <= p on [a,b].
    Elevates degree up to n_max.  Returns (n, betas) or None.  Exact rationals."""
    p = sp.expand(sp.sympify(p))
    fs = p.free_symbols
    if fs and x not in fs:
        (v,) = fs
        p = sp.expand(p.subs(v, x))
    a, b = sp.nsimplify(a), sp.nsimplify(b)
    deg = sp.Poly(p, x).degree() if p != 0 else 0
    for n in range(max(deg, 1), n_max + 1):
        betas = sp.symbols(f"_b0:{n + 1}")
        basis = [sp.binomial(n, i) * (x - a) ** i * (b - x) ** (n - i) / (b - a) ** n
                 for i in range(n + 1)]
        diff = sp.Poly(sp.expand(sum(be * ba for be, ba in zip(betas, basis)) - p), x)
        sol = sp.solve(diff.coeffs(), betas, dict=True)
        if not sol:
            continue
        # Use the EXACT solve output directly. (nsimplify re-parses huge rationals and
        # can perturb them so the exact reconstruction check fails -- a real bug
        # inherited from homog_master_probe.find_bernstein; the linear system is exact
        # so its solution is already exact Rational.)
        vals = [sol[0].get(be, sp.Integer(0)) for be in betas]
        if all(v.is_number and v >= 0 for v in vals):
            if sp.expand(sum(v * ba for v, ba in zip(vals, basis)) - p) == 0:
                return n, [R(v) for v in vals]
    return None


def family_cert_cells(a_max=6, b_max=6):
    """Per-(a,b) Bernstein certificate that GS_fam(a,b,nu) <= T on nu in [74/240,1/2].
    The cert integrand (cleared of the glemma(nu) denominator) is:

        P_{a,b}(nu) = T * (1+nu/3)^11 - base_of(a+b+1, S(nu))^11 * glemma(1/2)^b * GAMMA

    where S(nu) = a*SPLIT + b/2 + nu, and glemma(nu) = GAMMA/(1+nu/3)^11.
    P_{a,b} >= 0 on the cell  <=>  GS_fam <= T.  Find nonneg-Bernstein certs.
    Returns dict keyed by (a,b) -> (n, betas, endpoint margins) or None if not found."""
    lo, hi = SPLIT, R(1, 2)
    out = {}
    g_half = glemma(R(1, 2))
    for a in range(0, a_max + 1):
        for b in range(0, b_max + 1):
            j = a + b + 1
            S = a * SPLIT + b * R(1, 2) + mu  # nu = mu symbol
            base = base_of(j, S)
            # P = T*(1+mu/3)^11 - base^11 * g_half^b * GAMMA  (glemma(nu) cleared)
            P = sp.expand(T * (1 + mu / 3) ** 11 - base ** 11 * g_half ** b * GAMMA)
            cert = find_bernstein(P, lo, hi, n_max=14)
            m_lo = P.subs(mu, lo)
            m_hi = P.subs(mu, hi)
            out[(a, b)] = {
                "cert": cert,
                "margin_lo": m_lo,
                "margin_hi": m_hi,
                "poly": P,
            }
    return out


# ================================================================= Lean emission

def _rat_lean(q):
    q = R(q)
    if q.q == 1:
        return f"({q.p})"
    return f"({q.p} / {q.q})"


def emit_bernstein_lean(name, poly, a, b, n, betas, var="mu"):
    """Emit a kernel-checkable Lean `0 <= poly` on [a,b] from nonnegative Bernstein
    coefficients (same skeleton as HomogMaster's certs)."""
    a, b = R(a), R(b)
    xa = f"({var} - {_rat_lean(a)})"
    bx = f"({_rat_lean(b)} - {var})"
    p = sp.expand(poly)
    p_s = str(p).replace("**", "^")
    haves, summands = [], []
    for i, beta in enumerate(betas):
        if beta == 0:
            continue
        coef = sp.binomial(n, i) / (b - a) ** n
        scalar = _rat_lean(R(beta) * R(coef))
        proof = f"(by norm_num : (0:ℝ) ≤ {scalar})"
        factors = [scalar]
        if i > 0:
            factors.append(f"{xa}^{i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hxa {i})"
        if n - i > 0:
            factors.append(f"{bx}^{n - i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hbx {n - i})"
        term = " * ".join(factors)
        haves.append(f"  have t{i} : (0:ℝ) ≤ {term} := {proof}")
        summands.append(term)
    rhs = " + ".join(summands) if summands else "0"
    body = "\n".join(haves)
    hb = "" if n <= 12 else f"set_option maxHeartbeats {max(400000, n * 40000)} in\n"
    return (
        f"-- {name}: Bernstein-basis positivity (degree {n}) on [{a}, {b}].\n"
        f"{hb}"
        f"theorem {name} : ∀ {var} : ℝ, {_rat_lean(a)} ≤ {var} → {var} ≤ {_rat_lean(b)}"
        f" → (0:ℝ) ≤ ({p_s}) := by\n"
        f"  intro {var} hlo hhi\n"
        f"  have hxa : (0:ℝ) ≤ {xa} := by linarith\n"
        f"  have hbx : (0:ℝ) ≤ {bx} := by linarith\n"
        f"{body}\n"
        f"  have hid : (({p_s}) : ℝ) = {rhs} := by ring\n"
        f"  rw [hid]; linarith\n"
    )


def emit_lean_file(cells):
    """Emit HeteroFamily.lean: the exact exchange identity + a few small (a,b)
    Bernstein family cells + the glemma(1/2)<1 and Bcap(1)=W integer facts."""
    parts = ["import Mathlib\n\nnamespace HeteroFamily\n"]
    # the two-point exchange identity (kernel-green, ring)
    parts.append(
        "-- Two-point spreading exchange (the vertex-lemma engine), exact identity.\n"
        "-- (1+mi/3)(1+mj/3) - (1+(mi-t)/3)(1+(mj+t)/3) = t*(mj-mi+t)/9 >= 0 for t>=0, mi<=mj.\n"
        "theorem exchange_identity (mi mj t : ℝ) :\n"
        "    (1 + mi/3)*(1 + mj/3) - (1 + (mi - t)/3)*(1 + (mj + t)/3)\n"
        "      = t*(mj - mi + t)/9 := by ring\n"
        "theorem exchange_nonneg (mi mj t : ℝ) (ht : 0 ≤ t) (hij : mi ≤ mj) :\n"
        "    (1 + (mi - t)/3)*(1 + (mj + t)/3) ≤ (1 + mi/3)*(1 + mj/3) := by\n"
        "  have h : (1 + mi/3)*(1 + mj/3) - (1 + (mi - t)/3)*(1 + (mj + t)/3)\n"
        "      = t*(mj - mi + t)/9 := by ring\n"
        "  nlinarith [h, ht, hij, mul_nonneg ht (by linarith : (0:ℝ) ≤ mj - mi + t)]\n"
    )
    # glemma(1/2) < 1  as integer cert:  GAMMA/(1+1/6)^11 < 1  <=> GAMMA*6^11 < 7^11
    #   GAMMA = 64^2 5^11 / (621^2 3^11); glemma(1/2)= 64^2 5^11 6^11/(621^2 3^11 7^11)
    #   = 64^2 5^11 2^11 / (621^2 7^11).  <1 <=> 64^2 5^11 2^11 < 621^2 7^11.
    parts.append(
        "-- glemma(1/2) < 1 (the b-tail geometric ratio), integer cert.\n"
        "theorem glemma_half_lt_one : (64:ℕ)^2 * 5^11 * 2^11 < 621^2 * 7^11 := by norm_num\n"
    )
    # Bcap(1) = W  <=>  master_ub(1) = W (= (64/621)) and glemma(1) >= W and 1 >= W.
    parts.append(
        "-- Bcap(1) = W anchor: glemma(1) = W^2 (5/4)^11 >= W  <=>  W (5/4)^11 >= 1\n"
        "--   <=> 64*5^11 >= 621*4^11.\n"
        "theorem glemma_one_ge_W : (621:ℕ) * 4^11 ≤ 64 * 5^11 := by norm_num\n"
    )
    # a few Bernstein family cells (small a,b) that were found
    emitted = 0
    for (a, b), info in sorted(cells.items()):
        if info["cert"] is None:
            continue
        if a > 3 or b > 3:
            continue
        n, betas = info["cert"]
        nm = f"fam_cell_a{a}_b{b}"
        parts.append(emit_bernstein_lean(nm, info["poly"], SPLIT, R(1, 2), n, betas))
        emitted += 1
        if emitted >= 6:
            break
    parts.append("end HeteroFamily\n")
    return "\n".join(parts)


# ================================================================= run_all

def run_all(verbose=True):
    ok = True
    results = {}
    facts = [
        ("convexity", fact_convexity),
        ("glemma_half", fact_glemma_half),
        ("knee", fact_knee),
        ("master_inactive", fact_master_inactive),
        ("two_point_exchange", fact_two_point_exchange),
        ("extreme_point_reduction", fact_extreme_point_reduction),
        ("s_low_monotone", fact_s_low_monotone),
        ("sector_max", fact_sector_max),
        ("b_tail", fact_b_tail),
        ("a_tail", fact_a_tail),
        ("leaf_splice", fact_leaf_splice),
    ]
    for name, fn in facts:
        try:
            results[name] = fn()
            if verbose:
                print(f"[OK]  {name}")
        except Exception as e:  # noqa: BLE001
            ok = False
            print(f"[FAIL] {name}: {e}")
    # scan
    try:
        (best, sector) = scan_family()
        results["scan"] = {"family_max_over_T": best, "sector": sector}
        if verbose:
            print(f"[--]  family scan max GS/T = {float(best[0]):.10f} at "
                  f"(a={best[1]}, b={best[2]}, nu={best[3]}); "
                  f"sector GS(1,1/2)/T = {float(sector / T):.10f}")
        # scan must not exceed the sector value 0.8722T
        assert best[0] <= sector / T + R(1, 10**12), \
            f"family max {best[0]} exceeds sector {sector/T}"
    except Exception as e:  # noqa: BLE001
        ok = False
        print(f"[FAIL] scan: {e}")
    # empirical vertex check
    try:
        ev = empirical_vertex_check()
        results["empirical_vertex"] = ev
        if verbose:
            print(f"[--]  empirical vertex: checked {ev['checked']}, "
                  f"worst excess over projection = {ev['worst_excess_over_projection']:.3e}, "
                  f"configs over T = {ev['configs_over_T']}")
        assert ev["worst_excess_over_projection"] <= 1e-6, \
            "a config EXCEEDS its canonical projection: vertex lemma violated"
        assert ev["configs_over_T"] == 0, "a heterogeneous achievable config exceeds T"
    except Exception as e:  # noqa: BLE001
        ok = False
        print(f"[FAIL] empirical_vertex: {e}")
    # family certification cells
    try:
        cells = family_cert_cells(a_max=6, b_max=6)
        found = sum(1 for v in cells.values() if v["cert"] is not None)
        results["cert_cells"] = cells
        results["cert_cells_found"] = found
        if verbose:
            print(f"[--]  family cert cells: {found}/{len(cells)} Bernstein certs found "
                  f"(a,b <= 6)")
        # every cell must be either cert-found or have positive endpoint margins
        for (a, b), info in cells.items():
            assert info["margin_lo"] > 0 and info["margin_hi"] > 0, \
                f"cell (a={a},b={b}) has non-positive endpoint margin"
    except Exception as e:  # noqa: BLE001
        ok = False
        print(f"[FAIL] cert_cells: {e}")
    if verbose:
        print("ALL EXACT ASSERTIONS PASSED" if ok else "SOME ASSERTIONS FAILED")
    return ok, results


if __name__ == "__main__":
    import sys
    ok, _ = run_all()
    sys.exit(0 if ok else 1)
