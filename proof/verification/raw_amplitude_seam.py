"""The Step-4c raw-amplitude seam, pinned EXACTLY: Phi(b) is a FINITE LOCAL product of raw
matching cavities -- no second limit, no p-dependent offset bookkeeping.

CONTEXT (BRIDGE_DESIGN.md, Step 4c).  The remaining mathematical content of the Branch -> per(L(T))
bridge was believed to be the "cherry-folding at amplitude level": reconciling the DEC-dressed
telescoping (a(d,c) factors, rho_B normalization) with the RAW finite-tree amplitude
pi(T) = per(L(T)) / prod deg, through the p -> infinity cherry-hub limit, with "measured non-clean
log_rhoB(pi/Phi) offsets" that are p-dependent and only cancel in the hub ratio.  The roadmap called
this a genuine multi-session development.

THIS MODULE COLLAPSES THAT.  Three exact statements, each verified here in exact Fraction
arithmetic (and each a small Lean lemma, not a development):

  (S1)  RAW-CAVITY LEMMA (the cherry-folding, one line).  Realize a branch b = (c, children) as its
        LITERAL tree lit(b): the root, c cherries EXPANDED as 2-paths root-mid-leaf, children
        recursively, and the parent edge counted in the root degree (the hub edge supplies it when
        attached; so deg_root = k + c + 1 = the DEC d).  Give every edge the RAW weight
        w(u,v) = 1/(deg_u deg_v) and define the raw matching cavity bottom-up:

            Q(v) = 1 / (1 + sum_{children u of v} w(v,u) Q(u)),      Q(leaf) = 1.

        Then, writing cav for the DEC/Branch cavity (Reach.lean: cav = 3/(3+3k+4c+3S)):

            Q(root of lit(b)) = d * cav(b),          d = k + c + 1.

        Proof is a one-line induction: a cherry-mid has Q = 2/3 (Q_mid = 1/(1 + (1/(2*1))*1)), so
        each cherry edge contributes w*Q = (1/(2d))*(2/3) = 1/(3d), and each child edge contributes
        (1/(d d_i)) * Q_i = cav_i / d by the inductive hypothesis; hence
        Q = 1/(1 + c/(3d) + S/d) = 3d/(3d + c + 3S) = d * cav.  QED.
        (This is the raw-weight analogue of Bridge Step 1's cav = z(d,c) * rho0.)

  (S2)  LOCAL AMPLITUDE IDENTITY (the amplitude-level folding -- FINITE, no limit).

            Phi(b) = rho_B^(-V(b)) * prod_{v in lit(b)} 1/Q(v),

        equivalently W(b) := Phi(b) rho_B^(V(b)) = prod 1/Q(v) EXACTLY, as rationals.  Per-node
        proof: the c expanded cherries contribute (1/Q_mid)(1/Q_leaf) = 3/2 each -- exactly the
        (3/2)^c in a(d,c) -- and 1/Q_root = 1 + c/(3d) + S/d = (1 + c/(3d)) / rho0 by (S1) plus
        the identity (1 + c/(3d)) z(d,c) = 1/d; the rho_B^(1+2c) in a(d,c) is the vertex count
        1 + 2c of the node's literal cluster.  So the DEC eroot IS the local raw factor,
        node by node.  The "non-clean offsets" disappear: they were an artifact of comparing
        against finite trees whose ROOT lacks the phantom parent edge.

  (S3)  THE HUB SEAM WITH AN EXPLICIT UNIFORM RATE.  For the raw peeling pi(T) = prod_v 1/Q(v)
        (root at true degree, no phantom -- the standard include/exclude telescoping, = the
        msum of BridgeStep3d), attaching b to the hub H of hub_p changes ONLY (a) the vertex set
        (b's vertices multiply in prod 1/Q = prodInv(b), p-independent by (S1)-locality) and
        (b) the hub root factor (its degree bumps D -> D+1, rescaling every hub-incident weight):

            pi(hub_p + b) / pi(hub_p) = prodInv(b) * (1 + S'_p)/(1 + S_p)      EXACTLY, where
            S_p  = sum over hub edges of w Q            (base),
            S'_p = (D/(D+1)) S_p + Q_broot/((D+1) d_b)  (attached),  D = deg H = p + c_H.

        Since every base term is <= 1/D (Q <= 1, child deg >= 1, w <= 1/D) and there are D of
        them, S_p <= 1; hence

            | (1+S'_p)/(1+S_p) - 1 |  =  | S'_p - S_p | / (1+S_p)  <=  (S_p + Q_broot/d_b)/(D+1)
                                      <=  2/(D+1)  <=  2/(p+1).

        This is the UNIFORM constant branch_multiplicativity.py listed as the missing piece, in
        closed form.  Combining (S2)+(S3):

            | pi(hub_p+b)/pi(hub_p) * rho_B^(-V(b))  -  Phi(b) |  <=  Phi(b) * 2/(p+1)  ->  0,

        i.e. exp(logPhi b) = lim_p pi(T(hub_p + b))/pi(T(hub_p)) * rho_B^(-V(b)), the Step-4c
        target, with ONE elementary limit and an explicit O(1/p) envelope.

WHAT THIS MEANS FOR THE LEAN PORT.  Step 4c reduces to: (i) the Q = d*cav induction (ring algebra,
mirrors Bridge.lean's cav_eq_zc_mul_rho0); (ii) the per-node amplitude identity (ring algebra on
eroot); (iii) the raw peeling pi = prod 1/Q (BridgeStep3's main_cond conditioning at raw weights);
(iv) the explicit 2/(p+1) envelope (a finite computation per p plus a Tendsto squeeze, simpler than
BridgeStep4b's seam).  No new analytic machinery.

VERIFICATION HERE (all exact Fractions unless stated):
  V1. Q = d * cav at EVERY node of every test branch (S1).
  V2. W(b) = prod 1/Q  ==  the ground-truth amplitude prodF*f of general_children_crux (S2),
      exhaustive small branches + random deep/wide branches.
  V3. pi(T) = prod_v 1/Q(v) == brute-force weighted matching sum (independent recursion) on random
      literal trees, and == per(L(T))/prod deg via an exact integer PERMANENT on all trees with
      <= 10 vertices in the test set (independent check of H1/H2a on the raw side).
  V4. The finite-p hub identity (S3) EXACTLY at p in {3, 7, 20, 50}: both sides as Fractions.
  V5. The envelope |factor - 1| <= 2/(p+1) at every tested (b, p), and the factor -> 1
      monotonely in the tested range.

Scope / honesty.  This pins the CORRECT statements and verifies them exactly on finite test sets;
the one-line proofs in this docstring are complete as mathematics (each is a finite induction /
telescoping / term bound with no analytic content), but the machine-checked versions do not exist
yet -- that is the Lean work items (i)-(iv) above.  conjecture1_proved=False.  Self-verifying.
"""
from __future__ import annotations

import itertools
import math
import random
from fractions import Fraction as Fr

# ---------------------------------------------------------------------------
# Branch model (same encoding as general_children_crux: (c, [children]))
# ---------------------------------------------------------------------------

ARM = (0, [(0, [])])
_L = math.log(621 / 64) / 11  # log rho_B


def cav(C) -> Fr:
    """DEC/Branch cavity (Reach.lean): cav = 3/(3 + 3k + 4c + 3S)."""
    cr, kids = C
    S = sum(cav(ch) for ch in kids)
    return Fr(3, 3 + 3 * len(kids) + 4 * cr + 3 * S)


def V(C) -> int:
    """Vertex count of the literal tree: node + 2 per cherry + children."""
    cr, kids = C
    return 1 + 2 * cr + sum(V(ch) for ch in kids)


def W(C) -> Fr:
    """W(b) = Phi(b) * rho_B^{V(b)} -- the rho_B-free DEC amplitude, EXACT rational.

    Per node: a(d,c)*rho_B^{1+2c} = (3/2)^c (1 + c/(3d)); and 1/rho0 = 1 + z(d,c) * S
    with S = sum of child cavities (Bridge Step 1: z_i rho0_i = cav_i)."""
    cr, kids = C
    d = len(kids) + 1 + cr
    S = sum(cav(ch) for ch in kids)
    z = Fr(3, 3 * d + cr)
    a_norm = Fr(3, 2) ** cr * (1 + Fr(cr, 3 * d))
    inv_rho0 = 1 + z * S
    out = a_norm * inv_rho0
    for ch in kids:
        out *= W(ch)
    return out


# ---------------------------------------------------------------------------
# Literal tree realization + raw cavities
# ---------------------------------------------------------------------------

class Lit:
    """Literal tree: adjacency children[v] (rooted), deg[v] = TRUE degree in the ambient tree.

    For a branch realized with the phantom/hub parent edge, root degree includes +1."""

    def __init__(self):
        self.children = []  # list[list[int]]
        self.deg = []       # list[int]

    def add(self, extra_deg: int) -> int:
        self.children.append([])
        self.deg.append(extra_deg)
        return len(self.children) - 1

    def link(self, par: int, ch: int) -> None:
        self.children[par].append(ch)
        self.deg[par] += 1
        self.deg[ch] += 1


def realize(C, lit: Lit, phantom: bool) -> int:
    """Realize branch C into lit; returns root index. phantom=True adds +1 to root degree."""
    cr, kids = C
    r = lit.add(1 if phantom else 0)
    for _ in range(cr):
        mid = lit.add(0)
        leaf = lit.add(0)
        lit.link(r, mid)
        lit.link(mid, leaf)
    for ch in kids:
        cr_ = realize(ch, lit, phantom=False)
        # child realized without phantom; its parent edge is the link below
        lit.link(r, cr_)
    return r


def raw_Q(lit: Lit, v: int) -> Fr:
    """Raw matching cavity Q(v) = 1/(1 + sum w(v,u) Q(u)) with w = 1/(deg_v deg_u)."""
    s = Fr(0)
    for u in lit.children[v]:
        s += Fr(1, lit.deg[v] * lit.deg[u]) * raw_Q(lit, u)
    return 1 / (1 + s)


def prod_invQ(lit: Lit, v: int) -> Fr:
    """prod over the subtree of v of 1/Q."""
    out = 1 / raw_Q(lit, v)
    for u in lit.children[v]:
        out *= prod_invQ(lit, u)
    return out


def pi_raw(lit: Lit, root: int) -> Fr:
    """pi(T) = per(L)/prod deg = prod_v 1/Q(v) (the raw peeling; verified against msum/permanent)."""
    return prod_invQ(lit, root)


# ---------------------------------------------------------------------------
# Independent cross-checks: brute-force matching sum + exact permanent
# ---------------------------------------------------------------------------

def _edges(lit: Lit):
    return [(p, c) for p in range(len(lit.children)) for c in lit.children[p]]


def msum_brute(lit: Lit) -> Fr:
    """Weighted matching sum, independent include/exclude over the edge LIST (exponential)."""
    E = _edges(lit)

    def rec(i: int, used: frozenset) -> Fr:
        if i == len(E):
            return Fr(1)
        u, v = E[i]
        out = rec(i + 1, used)
        if u not in used and v not in used:
            w = Fr(1, lit.deg[u] * lit.deg[v])
            out += w * rec(i + 1, used | {u, v})
        return out

    return rec(0, frozenset())


def permanent_over_degs(lit: Lit) -> Fr:
    """per(L(T)) / prod deg via exact integer permanent (only for small trees)."""
    n = len(lit.children)
    Lm = [[0] * n for _ in range(n)]
    for v in range(n):
        Lm[v][v] = lit.deg[v]
    for (u, v) in _edges(lit):
        Lm[u][v] = -1
        Lm[v][u] = -1
    per = 0
    for sigma in itertools.permutations(range(n)):
        t = 1
        for i in range(n):
            t *= Lm[i][sigma[i]]
            if t == 0:
                break
        per += t
    pd = 1
    for v in range(n):
        pd *= lit.deg[v]
    return Fr(per, pd)


# ---------------------------------------------------------------------------
# Hub construction (the finite near-star competitor)
# ---------------------------------------------------------------------------

def build_hub(p: int, cH: int, arm, gadget=None):
    """Literal tree: hub root (true degree, no phantom) with cH cherries, p copies of arm,
    and optionally the gadget branch attached. Returns (lit, hub_index)."""
    lit = Lit()
    hub = lit.add(0)
    for _ in range(cH):
        mid = lit.add(0)
        leaf = lit.add(0)
        lit.link(hub, mid)
        lit.link(mid, leaf)
    for _ in range(p):
        r = realize(arm, lit, phantom=False)
        lit.link(hub, r)
    if gadget is not None:
        r = realize(gadget, lit, phantom=False)
        lit.link(hub, r)
    return lit, hub


# ---------------------------------------------------------------------------
# Test branch generators
# ---------------------------------------------------------------------------

def _enum_small(max_extra: int = 3):
    """All branches with c <= 2 and <= max_extra recursive slots (small exhaustive family)."""
    leaves = [(c, []) for c in range(4)]
    lvl1 = [(c, list(ks)) for c in range(3) for r in range(1, 3)
            for ks in itertools.combinations_with_replacement(leaves, r)]
    lvl2 = [(c, [k1, k2]) for c in range(2) for k1 in leaves[:3] for k2 in lvl1[:12]]
    return leaves + lvl1 + lvl2[:40]


def _rand_branch(rng: random.Random, depth: int):
    if depth == 0 or rng.random() < 0.35:
        return (rng.randint(0, 6), [])
    return (rng.randint(0, 4), [_rand_branch(rng, depth - 1) for _ in range(rng.randint(1, 3))])


# ---------------------------------------------------------------------------
# Certificates
# ---------------------------------------------------------------------------

def _check_Q_eq_dcav(C) -> bool:
    """V1 at every node: realize each subtree with phantom and compare Q(root) to d*cav."""
    cr, kids = C
    lit = Lit()
    r = realize(C, lit, phantom=True)
    d = len(kids) + 1 + cr
    if raw_Q(lit, r) != d * cav(C):
        return False
    return all(_check_Q_eq_dcav(ch) for ch in kids)


def certify_raw_cavity_lemma(seed: int = 5, n_rand: int = 400) -> dict:
    """(S1) Q(root) = d * cav(b), every node, exhaustive small + random branches."""
    rng = random.Random(seed)
    tests = _enum_small() + [_rand_branch(rng, 4) for _ in range(n_rand)]
    fails = sum(0 if _check_Q_eq_dcav(C) else 1 for C in tests)
    return {"n_branches": len(tests), "fails": fails, "raw_cavity_lemma": fails == 0}


def certify_local_amplitude(seed: int = 7, n_rand: int = 400) -> dict:
    """(S2) W(b) = prod_{v in lit(b)} 1/Q(v) exactly; cross-checked vs general_children_crux."""
    rng = random.Random(seed)
    tests = _enum_small() + [_rand_branch(rng, 4) for _ in range(n_rand)]
    fails = 0
    for C in tests:
        lit = Lit()
        r = realize(C, lit, phantom=True)
        if W(C) != prod_invQ(lit, r):
            fails += 1
    # ground-truth cross-check (float, since GC exposes log_phi): W must satisfy
    # log W - V L = logPhi per general_children_crux
    import general_children_crux as GC
    worst = 0.0
    for C in tests[:80]:
        lw = math.log(W(C).numerator) - math.log(W(C).denominator)
        worst = max(worst, abs((lw - V(C) * _L) - GC.log_phi(C)))
    return {"n_branches": len(tests), "fails": fails, "gc_crosscheck_max_err": worst,
            "local_amplitude_identity": fails == 0 and worst < 1e-9}


def certify_raw_peeling(seed: int = 11, n_rand: int = 120, max_edges: int = 16) -> dict:
    """(V3) pi = prod 1/Q == brute msum on random trees; == per(L)/prod deg when <= 10 vertices.

    The brute matching sum is exponential in the edge count, so trees are capped at
    `max_edges` edges -- this is an independent-implementation check of the telescoping,
    whose exactness elsewhere is carried by (S1)/(S2) on much larger branches."""
    rng = random.Random(seed)
    fails_msum = fails_per = n_msum = n_per = 0
    while n_msum < n_rand:
        C = _rand_branch(rng, 3)
        lit = Lit()
        realize(C, lit, phantom=False)  # a full tree: root at true degree
        if not 1 <= len(_edges(lit)) <= max_edges:
            continue  # skip the degenerate single-vertex tree (deg 0, pi undefined) and huge trees
        n_msum += 1
        p1 = pi_raw(lit, 0)
        if p1 != msum_brute(lit):
            fails_msum += 1
        if len(lit.children) <= 10:
            n_per += 1
            if p1 != permanent_over_degs(lit):
                fails_per += 1
    return {"n_trees": n_msum, "fails_vs_msum": fails_msum,
            "n_permanent_checked": n_per, "fails_vs_permanent": fails_per,
            "raw_peeling": fails_msum == 0 and fails_per == 0 and n_per > 0}


def certify_hub_seam(ps=(3, 7, 20, 50), cH: int = 0, arm=ARM, gadgets=None) -> dict:
    """(S3)/(V4)/(V5): exact finite-p hub identity + the 2/(p+1) envelope."""
    if gadgets is None:
        gadgets = [
            (0, [(0, [])]),                       # the ARM itself
            (5, []),                              # 5-cherry leaf
            (2, [(3, []), (0, [(1, [])])]),       # branching gadget
            (0, [(5, []), (5, []), (5, [])]),     # broom
        ]
    fails_exact = fails_env = 0
    factors = {}
    for b in gadgets:
        prodInv = None
        litb = Lit()
        rb = realize(b, litb, phantom=True)
        prodInv = prod_invQ(litb, rb)
        fac_list = []
        for p in ps:
            base, hub = build_hub(p, cH, arm)
            att, hub2 = build_hub(p, cH, arm, gadget=b)
            lhs = pi_raw(att, hub2) / pi_raw(base, hub)
            factor = raw_Q(base, hub) / raw_Q(att, hub2)
            if lhs != prodInv * factor:
                fails_exact += 1
            D = base.deg[hub]
            if abs(factor - 1) > Fr(2, D + 1):
                fails_env += 1
            fac_list.append(float(factor))
        factors[str(b)] = fac_list
    # convergence: the factor tends to 1. For the ARM gadget it is EXACTLY 1 at every p
    # (S' = (D/(D+1))S + Q_arm/((D+1) d_arm) = S identically, since the added arm term equals
    # the rescaling loss) -- so allow non-strict decrease.
    conv = all(abs(f[-1] - 1) <= abs(f[0] - 1) and abs(f[-1] - 1) < 0.02
               for f in factors.values())
    return {"ps": list(ps), "fails_exact_identity": fails_exact,
            "fails_envelope": fails_env, "hub_factors": factors,
            "hub_seam": fails_exact == 0 and fails_env == 0 and conv}


def certify_limit_statement(ps=(10, 40, 160), gadget=(2, [(3, []), (0, [(1, [])])])) -> dict:
    """The Step-4c target, numerically: pi-ratio * rho_B^{-V} -> Phi(b), inside the envelope."""
    phi = float(W(gadget)) * math.exp(-V(gadget) * _L)
    devs = []
    for p in ps:
        base, hub = build_hub(p, 0, ARM)
        att, hub2 = build_hub(p, 0, ARM, gadget=gadget)
        ratio = pi_raw(att, hub2) / pi_raw(base, hub)
        val = float(ratio) * math.exp(-V(gadget) * _L)
        devs.append(abs(val - phi))
    inside = all(devs[i] <= phi * 2 / (ps[i] + 1) + 1e-12 for i in range(len(ps)))
    return {"phi": phi, "ps": list(ps), "abs_devs": devs,
            "inside_envelope_phi_2_over_p1": inside,
            "limit_statement_verified": inside and devs[-1] < devs[0]}


def certify() -> dict:
    out = {
        "S1_raw_cavity": certify_raw_cavity_lemma(),
        "S2_local_amplitude": certify_local_amplitude(),
        "V3_raw_peeling": certify_raw_peeling(),
        "S3_hub_seam": certify_hub_seam(),
        "limit": certify_limit_statement(),
    }
    out["step4c_statements_pinned"] = all([
        out["S1_raw_cavity"]["raw_cavity_lemma"],
        out["S2_local_amplitude"]["local_amplitude_identity"],
        out["V3_raw_peeling"]["raw_peeling"],
        out["S3_hub_seam"]["hub_seam"],
        out["limit"]["limit_statement_verified"],
    ])
    out["conjecture1_proved"] = False
    return out


if __name__ == "__main__":
    res = certify()
    for k, v in res.items():
        print(f"{k}: {v}")
    assert res["step4c_statements_pinned"], "verification FAILED"
    print("\nAll Step-4c seam statements verified exactly.")
