"""Nonlinear-JSR recasting of Phi<=1, and the DGT-hypothesis audit (why the cone tool does not transfer).

Phi<=1 is a MARGINAL, CONSTRAINED joint-spectral-radius problem (lyapunov.py / invariant_polytope.py):
in the chain case the constrained JSR is ~0.9817<1 with the supremum Phi=1 attained on the tie orbit,
and a Guglielmi-Zennaro INVARIANT POLYTOPE certifies chains.  The open part is the BRANCHING (tree)
recursion.  The lit lead was the nonlinear-JSR machinery for sub-homogeneous order-preserving cone
maps (Deidda-Guglielmi-Tudisco, arXiv:2507.11314) -- a polytopal algorithm with finite-time
convergence -- which would extend the chain polytope to trees.  This module recasts the problem in
that language and AUDITS the hypotheses.  Self-verifying; it does NOT close Phi<=1.

THE OPERATOR.  Per rooted subtree carry the state (Phi, mu) = (amplitude, root cavity).  A node with
c cherries and children states (Phi_i, mu_i), i=1..k, produces
    mu'  = 3 / (3 + 3k + 4c + 3 * sum_i mu_i),
    Phi' = a(d,c) * (1 + z(d,c) * sum_i mu_i) * prod_i Phi_i,   d=k+1+c, z=3/(3d+c),
    a(d,c) = (3/2)^c (1 + c/3d) / rhoB^{1+2c}.
node_op reproduces (log Phi, cav) EXACTLY (checked).  Phi<=1 for all trees  <=>  the nonlinear
spectral radius of node_op is <= 1.

HYPOTHESIS AUDIT (verify()):
 (H1) ORDER-PRESERVING: YES.  Phi' is nondecreasing in every child Phi_i and mu_i; mu' is
      nonincreasing in every child mu_i.  (The DGT monotonicity hypothesis holds.)
 (H2) SUB-HOMOGENEOUS: NO (for branching).  Scaling all child amplitudes by lambda scales Phi' by
      lambda^k -- the node map is DEGREE-k homogeneous, i.e. SUPER-homogeneous for k>=2.  DGT (and
      classical nonlinear Perron-Frobenius) require SUB-homogeneity (degree<=1).  Only k=1 (chains)
      is degree-1; that sub-case is exactly what invariant_polytope.py already certifies.  So the DGT
      cone framework covers the chain sub-case but NOT the branching tail -- the actual open crux.
 (H3) MARGINAL VARIETAL MAXIMISER: YES.  The reachable frontier max Phi = 1 EXACTLY, attained only on
      the 6-point tie variety (near-star family N(c,k), c+k=5; 6 isolated rational cavities in
      [0.086,0.333]); everywhere else Phi<1.

VERDICT.  The nonlinear-JSR recasting is clean and the maximiser is exactly the marginal 6-point tie
variety, but the branching amplitude is a DEGREE-k MULTIPLICATIVE CASCADE (a critical/boundary
"smoothing transform"), which is SUPER-homogeneous and so falls OUTSIDE the sub-homogeneous cone
theory the polytopal algorithm needs.  In log-coordinates the branching operator is additive/tropical
(degree 1, order-preserving), but its Collatz-Wielandt eigenvalue is exactly the value function Psi --
the circular potential (cavity_potential.py).  So neither the cone form (blocked by super-homogeneity)
nor the tropical form (circular) closes it out-of-the-box.  The one genuinely-untried ingredient is
the invariant-MEASURE dual on the 6-point tie variety (a branching stationary measure / boundary case
of the smoothing transform), which needs real adaptation.  depth_collapse/conjecture1 remain OPEN.

Depends on general_children_crux.  math + std-lib.
"""
from __future__ import annotations

import math
import random

import general_children_crux as GC

_rhoB = (621 / 64) ** (1 / 11)
TIE_MU = 3 / 23


def node_op(c, kids):
    """kids = list of (Phi, mu); returns (Phi', mu') for a node with c cherries."""
    k = len(kids)
    d = k + 1 + c
    z = 3 / (3 * d + c)
    S = sum(mu for (_, mu) in kids)
    mu2 = 3 / (3 + 3 * k + 4 * c + 3 * S)
    a = (1.5 ** c * (1 + c / (3 * d))) / _rhoB ** (1 + 2 * c)
    Phi2 = a * (1 + z * S) * math.prod([P for (P, _) in kids]) if kids else a
    return (Phi2, mu2)


def _state(C):
    cr, kids = C
    return node_op(cr, [_state(k) for k in kids])


def h1_order_preserving(trials=20000, seed=1):
    rng = random.Random(seed)
    ok = True
    for _ in range(trials):
        c = rng.randint(0, 5)
        k = rng.randint(1, 3)
        kids = [(rng.uniform(0.2, 1.0), rng.uniform(0.01, 1.0)) for _ in range(k)]
        P0, m0 = node_op(c, kids)
        i = rng.randrange(k)
        up = list(kids); up[i] = (kids[i][0] + 0.05, kids[i][1])
        if node_op(c, up)[0] < P0 - 1e-12:
            ok = False
        upm = list(kids); upm[i] = (kids[i][0], min(1.0, kids[i][1] + 0.05))
        P2, m2 = node_op(c, upm)
        if P2 < P0 - 1e-12 or m2 > m0 + 1e-12:
            ok = False
    return ok


def h2_homogeneity_degree():
    """Scaling all child Phi by 2 scales Phi' by 2^k -> degree-k (super-homogeneous for k>=2)."""
    out = {}
    for k in (1, 2, 3, 4):
        base = node_op(0, [(0.5, 0.3)] * k)[0]
        scaled = node_op(0, [(1.0, 0.3)] * k)[0]
        out[k] = round(scaled / base, 6)  # == 2^k
    sub_homog = all(out[k] <= 2 + 1e-9 for k in out)  # sub-homog would need ratio <= 2 (degree<=1)
    return {"scale_ratios_vs_2^k": out, "is_sub_homogeneous": sub_homog}


def h3_tie_variety():
    """Reachable frontier max Phi = 1 at the tie; the Phi>0.99 set = the 6-point near-star tie variety."""
    rng = random.Random(7)
    F = {}
    def add(pts):
        for (P, mu) in pts:
            b = round(mu, 6)
            if b not in F or P > F[b]:
                F[b] = max(F.get(b, -9.0), P)
    add([node_op(c, []) for c in range(0, 80)])
    for it in range(10):
        states = [(F[b], b) for b in F]
        fs = states if len(states) <= 500 else rng.sample(states, 500)
        add([node_op(c, [rng.choice(fs) for _ in range(k)])
             for c in range(0, 9) for k in (1, 2, 3) for _ in range(3000)])
    mx = max(F.values())
    near1 = sorted(b for b in F if F[b] > 0.99)
    # exact tie anchors: near-star N(c,k), c+k=5
    ARM = (0, [(0, [])])
    anchors = []
    for c in range(6):
        N = (c, [ARM] * (5 - c))
        anchors.append((c, 5 - c, round(float(GC.cav(N)), 6), round(GC.log_phi(N), 6)))
    return {"frontier_maxPhi": round(mx, 6), "maxPhi_at_tie": abs(mx - 1) < 1e-4,
            "n_reachable_cav_Phi_gt_0.99": len(near1),
            "tie_anchors_c_k_cav_logPhi": anchors}


def verify(check_trees=3000):
    rng = random.Random(0)
    def rt(dep):
        if dep == 0 or rng.random() < 0.4:
            return (rng.randint(0, 6), [])
        return (rng.randint(0, 5), [rt(dep - 1) for _ in range(rng.randint(1, 3))])
    repro = all(abs(math.log(_state(C)[0]) - GC.log_phi(C)) < 1e-9 and
                abs(_state(C)[1] - float(GC.cav(C))) < 1e-12
                for C in (rt(4) for _ in range(check_trees)))
    H2 = h2_homogeneity_degree()
    H3 = h3_tie_variety()
    return {
        "node_op_reproduces_logPhi_cav": repro,
        "H1_order_preserving": h1_order_preserving(),
        "H2_homogeneity": H2,
        "H3_tie_variety": H3,
        "dgt_applies_to_branching": (not H2["is_sub_homogeneous"]) and False,  # sub-homog fails => no
        "depth_collapse_closed": False,
        "conjecture1_proved": False,
        "note": ("Phi<=1 recast as nonlinear spectral radius <=1 of the order-preserving (Phi,mu) node "
                 "operator. H1 order-preserving holds; H3 maximiser = the marginal 6-point tie variety. "
                 "BUT H2: the branching map is DEGREE-k homogeneous (super-homog for k>=2), violating the "
                 "SUB-homogeneity that DGT / nonlinear Perron-Frobenius require -- the cone polytope "
                 "algorithm covers only chains (k=1, already certified by invariant_polytope). The "
                 "branching amplitude is a critical multiplicative cascade (boundary smoothing transform); "
                 "its tropical/log form has Collatz-Wielandt eigenvalue = the circular potential Psi. "
                 "Nonlinear-JSR does NOT close it out-of-the-box; the untried ingredient is the invariant-"
                 "measure dual on the tie variety. conjecture1 OPEN."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
