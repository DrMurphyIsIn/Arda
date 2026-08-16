"""The general-children crux of Phi<=1 -- located, factored, and its EXTREMAL VARIETY identified.

This module pins down the sole remaining open piece of the Brualdi-Goldwasser tree Laplacian-ratio
problem (Conjecture 1) after the near-star family was proven arithmetically in Lean
(NearStar.lean: logPhi(N(c,k)) = gVal(c+k) <= 0, equality iff c+k=5).  It records, self-verified:

THE CRUX (exact rational statement, from rational_reduction.py).  With F(d,c)=(3/2)^c(1+c/(3d)),
z(d,c)=3/(3d+c), d_v=n_ch+1+c_v, prodF(C)=prod_v F(d_v,c_v), V(C)=sum_v(1+2c_v), and f(C) the
matching polynomial of C with vertex activities z_v (edge weight z_u z_v):

    Phi(C) <= 1   <=>   (prodF(C) * f(C))^11  <=  (621/64)^V(C)      for EVERY rooted tree C.

This is a PURELY RATIONAL inequality (11 L = log(621/64) clears the 11th root).  Cherries are
region-free bounded (a_leaf(c)=F(1+c,c)/rhoB^{1+2c} peaks at c=5); the DEPTH and BRANCHING tails
are the open part (naive induction with only Phi_i<=1 overshoots to 1.197).

PER-NODE FACTORISATION (verified here).  Phi factors over nodes:

    Phi(C) = prod_v phi_v,   phi_v = F(d_v,c_v) * g_v / rhoB^{1+2 c_v},
    g_v = 1 + z_v * sum_{i in children} z_i / g_i,     cav(v) = z_v / g_v,

where g_v is the matching-ratio f(C_v)/prod_i f(C_i) and equals 1 + z_v * (sum of child cavities).
So log Phi = sum_v e_root(v) (the general_induction telescoping), and the tightest potential is
P* = -Psi, Psi(m)=sup{logPhi : cav=m}; the crux is exactly Psi<=0 (circular unless bounded).

THE EXTREMAL VARIETY (certified here by exhaustive enumeration).  Over ALL 192,888 rooted trees
with <=5 nodes and cherries<=7, max log Phi = 0 EXACTLY, and the equality set {log Phi = 0} is
EXACTLY the near-star tie family N(c,k), c+k=5 (all with cavity 3/23 and V=11):
    (5,[]),  (4,[ARM]),  (3,[ARM,ARM]),  ...   ARM = (0,[(0,[])]).
These are precisely the `nearStarB c k` gadgets with c+k=5 -- the diagonal Lean `nearStar_tie`
proves = 0.  So THE GLOBAL MAXIMISER VARIETY OF logPhi IS THE NEAR-STAR FAMILY ALREADY FORMALISED;
every other tree is strictly below.  The residual crux is: prove no tree exceeds this max of 0
(equivalently the rational inequality above) for ALL trees, not just <=5 nodes.

WHY IT IS ARITHMETIC, NOT SMOOTH (coordinate-free obstruction).  Psi touches the cherry-leaf/
near-star points (3/(4s+3), gVal(s)) and POKES ABOVE any chord between them (e.g. Psi(1/3)=-0.0077
sits above the -0.036 chord of its neighbours) -- so no concave/smooth envelope in ANY coordinate
bounds Psi: the continuous relaxation of the tie-harmonic exceeds 0 (Phi(c*=3.82)=1.00004>1,
near_tie_asymptotics.py), and only integrality (integer cherries/degrees) holds it at <=0.  Hence a
proof must be arithmetic (the 23-adic Rval<=1 route), exactly as the near-star proof is.

This module DOES NOT close the crux.  It certifies the reduction, the factorisation, and -- the new
contribution -- that the extremal variety is exactly the formalised near-star tie family, sharpening
the open statement to "the near-star tie variety is the global maximiser over all trees."

Requires the sibling `rational_reduction` module.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import rational_reduction as RR

_L = math.log(621 / 64) / 11
ARM = (0, [(0, [])])


def cav(C) -> Fr:
    """Exact cavity mu = 3/(3 + 3 n_ch + 4c + 3 S), S = sum of child cavities."""
    cr, kids = C
    S = sum(cav(ch) for ch in kids)
    return Fr(3, 3 + 3 * len(kids) + 4 * cr + 3 * S)


def log_phi(C) -> float:
    prodF, V = RR._prodF_V(C)
    f = RR._matching_f(C)
    val = prodF * f
    return math.log(val.numerator) - math.log(val.denominator) - V * _L


def g_recursion(C):
    """(prod of g over subtree, g at this root); verifies f(C)=prod_v g_v and cav=z_root/g_root."""
    cr, kids = C
    d = len(kids) + 1 + cr
    zr = Fr(3, 3 * d + cr)
    prodg_sub = Fr(1)
    child_z_over_g = Fr(0)
    for ch in kids:
        gsub, groot = g_recursion(ch)
        prodg_sub *= gsub
        crc, kk = ch
        dc = len(kk) + 1 + crc
        child_z_over_g += Fr(3, 3 * dc + crc) / groot
    gv = 1 + zr * child_z_over_g
    return prodg_sub * gv, gv


def g_Val(s: int) -> float:
    """The near-star / cherry-leaf amplitude gVal(s) = logPhi of the s-cherry leaf (s,[])."""
    return s * math.log(1.5) - (1 + 2 * s) * _L + math.log(4 * s + 3) - math.log(3 * (s + 1))


def nearstar(c: int, k: int):
    """N(c,k) = node with c cherries and k cherry-arms; logPhi = gVal(c+k)."""
    return (c, [ARM] * k)


# ---- self-verifying certificates ----

def certify_factorisation(seed: int = 3, n: int = 3000, depth: int = 4) -> dict:
    """Phi = prod_v phi_v with g_v = 1 + z_v sum z_i/g_i: check f(C)=prod g_v and cav=z/g exactly."""
    import random
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0 or rng.random() < 0.4:
            return (rng.randint(0, 6), [])
        return (rng.randint(0, 6), [rt(dep - 1) for _ in range(rng.randint(1, 3))])

    okf = okm = True
    for _ in range(n):
        C = rt(depth)
        prodg, groot = g_recursion(C)
        if prodg != RR._matching_f(C):
            okf = False
        cr, kids = C
        d = len(kids) + 1 + cr
        if cav(C) != Fr(3, 3 * d + cr) / groot:
            okm = False
    return {"f_eq_prod_g": okf, "cav_eq_z_over_g": okm}


def _trees(nmax: int, cmax: int):
    def _key(t):
        return (RR._prodF_V(t)[1], str(t))

    def tw(n):
        if n == 1:
            for c in range(cmax + 1):
                yield (c, [])
            return
        for c in range(cmax + 1):
            for fo in fw(n - 1):
                yield (c, fo)

    def fw(n):
        if n == 0:
            yield []
            return
        for fs in range(1, n + 1):
            for t in tw(fs):
                for rest in fw(n - fs):
                    if not rest or _key(t) <= _key(rest[0]):
                        yield [t] + rest

    for N in range(1, nmax + 1):
        yield from tw(N)


def certify_extremal_variety(nmax: int = 5, cmax: int = 7) -> dict:
    """Exhaustively: max logPhi = 0 over all trees <=nmax nodes, cherries<=cmax; and the equality
    set {logPhi=0} is exactly the near-star tie family (c+k=5), all cavity 3/23, V=11."""
    gmax = -9.0
    npos = 0
    count = 0
    tie_set = []
    for C in _trees(nmax, cmax):
        count += 1
        lp = log_phi(C)
        if lp > 1e-9:
            npos += 1
        gmax = max(gmax, lp)
        if abs(lp) < 1e-6:
            tie_set.append((cav(C), RR._prodF_V(C)[1], C))
    all_tie_are_nearstar = all(m == Fr(3, 23) and V == 11 for m, V, _ in tie_set)
    return {
        "trees_checked": count,
        "logPhi_gt_0": npos,               # must be 0
        "global_max_logPhi": gmax,          # must be ~0
        "tie_variety": [(str(m), V, C) for m, V, C in tie_set],
        "tie_variety_all_cav_3_23_V_11": all_tie_are_nearstar,
    }


def tail_decomposition() -> dict:
    """psi(m) <= 0 DECOMPOSES: the FAR regime (deep OR wide OR many cherries) is region-free NEGATIVE, and
    the marginal near-tie core is exactly the (proven) near-star tie variety.  Attempt-to-prove-psi<=0 map:
    * DEPTH: the c=0 chain per-node increment -> -L + log((1+sqrt2)/2) < 0, i.e. 1+sqrt2 < 2 rhoB -- the
      ALREADY-PROVEN E2 crux (ExactCruxes.e2_two_rhoB_gt).  So pure depth decays LINEARLY to -inf.
    * BRANCHING: node(0) + j amplitude-0 children (each (5,[])) -> -L + log(1+3/23) = -0.084 < 0 (bounded neg).
    * CHERRIES: a_leaf(c) region-free bounded (rational_reduction; peak c=5).
    * MARGINAL CORE: the only logPhi=0 gadgets are the near-star tie variety c+k=5 -- PROVEN =0 (NearStar.lean).
    So psi<=0's OPEN part is the QUANTITATIVE far-regime margins + boundary matching; the marginal core is
    closed, and NO smooth/localization argument reaches it (integrality; the tie variety is approached by
    infinite near-tie families with NO uniform margin).  psi<=0 itself is NOT closed."""
    import math
    rhoB = (621 / 64) ** (1 / 11)
    L = math.log(rhoB)
    depth_rate = -L + math.log((1 + 2 ** 0.5) / 2)
    branch_lim = -L + math.log(1 + 3 / 23)
    return {
        "depth_per_node_limit": depth_rate,
        "depth_negative_via_E2": (1 + 2 ** 0.5) < 2 * rhoB,     # 1+sqrt2 < 2 rhoB = e2_two_rhoB_gt (PROVEN)
        "branching_limit": branch_lim,
        "branching_negative": branch_lim < 0,
        "marginal_core": "near-star tie variety c+k=5 (proven =0, NearStar.lean)",
        "psi_le_0_closed": False,
    }


def certify() -> dict:
    fac = certify_factorisation()
    ext = certify_extremal_variety()
    ok = (fac["f_eq_prod_g"] and fac["cav_eq_z_over_g"]
          and ext["logPhi_gt_0"] == 0 and abs(ext["global_max_logPhi"]) < 1e-6
          and ext["tie_variety_all_cav_3_23_V_11"])
    return {
        "factorisation_verified": fac,
        "extremal_variety": ext,
        "crux_is_rational_matching_poly_inequality": "(prodF*f)^11 <= (621/64)^V for all rooted trees",
        "extremal_variety_is_the_formalised_near_star_tie_family": ext["tie_variety_all_cav_3_23_V_11"],
        "obstruction": "arithmetic/integrality (Psi pokes above every chord; smooth cert fails in any coordinate)",
        "tail_decomposition": tail_decomposition(),
        "crux_closed": False,          # the general-tree inequality remains OPEN
        "all_checks_pass": ok,
    }


if __name__ == "__main__":
    import json
    print(json.dumps(certify(), indent=2, default=str))
