"""The K-boundary, pinned: the Kelmans exchange with PER-VERTEX (mixed) cherry loads.

CONTEXT (R47 campaign, the named open hypothesis A_mono_K-BOUNDARY).  psi_close.py proves the
adjacent-Kelmans pi-monotonicity for the UNIFORM-load backbone model (every backbone vertex carries the
same c >= 3 cherries; symbolic corner certificate after the shift da=1+u, db=2+v, c=3+s).  The R7 rewrite,
however, runs on the stratum-(ii) family -- backbones of HUBS carrying five-cherry ARMS with hub loads
de-loading through {5,...,1,0} -- which in the backbone model is exactly PER-VERTEX loads: arm-centers are
backbone leaves with load 5, hubs are internal backbone vertices with load c0 in {0..5}.  Uniform-c >= 3
misses this domain; maximizer_structure.py further records that hub-to-hub arm moves can DECREASE pi.  So
the honest question is: for MIXED loads, exactly where is the adjacent Kelmans step monotone?

WHAT THIS MODULE PROVES (exact rational arithmetic + symbolic Polya certificates; every claim an
assert in run_all()):

  (1) MODEL + GROUND TRUTH.  pi of a loaded backbone (beta, c: V->N) via the per-vertex factorization
          pi(beta[c]) = prod_v F(deg_v, c_v) * Psi(beta; z),   z_v = 3/(3*deg_v + 4*c_v),
      verified EXACTLY against per(L(T))/prod deg of the LITERAL tree (cherries expanded as length-2
      paths; matching-sum identity itself anchored against a brute permanent).

  (2) EXACT IDENTITY, mixed loads.  For the adjacent Kelmans step a <- b the environment quantities
      (FQ, MQ, FS, MS) are load-blind, and
          pi(beta') - pi(beta) = P * FS * FQ * Phi(sigma_Q, sigma_S),
      Phi bilinear with coefficients c1..c4 explicit in (da, db, c_a, c_b).  Verified exactly over
      all trees <= 7 vertices x mixed load patterns (912 steps).

  (3) THE TWO-HUB EXCHANGE DICHOTOMY (new THEOREM, all p >= q >= 1, symbolic).  On the two-hub
      family (hub a: p arms + load ca; hub b: q arms + load cb; hubward p >= q):
        * cb >= 1  =>  the merge b -> a STRICTLY INCREASES pi   (30/30 load cells, all-nonneg
          numerator + positive constant over positive denominator after p = 1+s+r, q = 1+s);
        * cb  = 0, ca >= 2  =>  the merge STRICTLY DECREASES pi (all-nonpos certificates);
        * cb  = 0, ca <= 1  =>  decreases except a FINITE exact exception set
          {(0,0): (1,1),(2,1),(2,2),(3,1); (1,0): (1,1)} (closed by shifted certificates).
      So the ONLY hubward-monotonicity obstruction is a DE-LOADED DONOR -- and that case is
      provably wrong-way, so no local rewrite fix exists.

  (4) GENERAL-ENVIRONMENT BOX THEOREM (all N, symbolic).  For ANY loaded backbone, hubward
      da >= db >= 2, with every environment neighbour of a and b satisfying
      3*deg + 4*load >= 23 (z <= 3/23; arm-leaves give exactly 23), the step is
      pi-non-decreasing for 25 of the 30 cb >= 1 load cells (box corners all-nonneg after
      da = 2+v+u, db = 2+v).  The 5 remaining cells fail only the crude sigma_S = 0 corner
      (they ARE increasing on the exact family) -- the box, not the move, fails there.

CONSEQUENCE FOR THE R7 REWRITE (A_mono_K / A_mono_H): fire K/H only hubward and only while the
donor still carries load >= 1; de-load (R6) only the final hub, LAST.  Under that ordering every
fired step lands in the certified region.  WHAT REMAINS OPEN (the true K-boundary, now sharp):
(a) the 5 receiver-much-lighter cells in general environments (needs a mover-side sub-box),
(b) exchanges next to a low-z vertex (3*deg+4*load < 23, e.g. a small bare hub),
(c) eliminating de-loaded-donor configurations -- provably NOT a monotone-move question but the
    fixed-n vertex-budget comparison (the "verified to n=240" territory).
conjecture1_proved=False.

Requires networkx, sympy.  Self-verifying: run_all() at the bottom; every claim is an assert.
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import networkx as nx


# ---------------------------------------------------------------- loaded model
def z_of(deg: int, c: int) -> Fr:
    """Activity of a backbone vertex with backbone degree deg and cherry load c."""
    return Fr(3, 3 * deg + 4 * c)


def F_of(deg: int, c: int) -> Fr:
    """F factor of a backbone vertex: F(D) = (3/2)^c + (c/(2D))*(3/2)^(c-1), D = deg + c."""
    D = deg + c
    if c == 0:
        return Fr(1)
    return Fr(3, 2) ** c + Fr(c, 2 * D) * Fr(3, 2) ** (c - 1)


def psi_weighted(G: nx.Graph, z: dict) -> Fr:
    """sum over matchings M of prod_{v in M} z_v -- linear tree/forest DP.
    (a_v, b_v) = subtree matching sums with v unmatched / v matched to a child:
    a_v = prod_c (a_c + b_c);  b_v = z_v * sum_c z_c a_c prod_{c'!=c} (a_c'+b_c')."""
    if G.number_of_nodes() == 0:
        return Fr(1)
    total = Fr(1)
    seen = set()
    for root in G.nodes():
        if root in seen:
            continue
        comp = nx.node_connected_component(G, root)
        seen |= comp
        # iterative post-order over the component tree
        parent = {root: None}
        order = [root]
        for v in order:
            for w in G.neighbors(v):
                if w not in parent:
                    parent[w] = v
                    order.append(w)
        a = {}
        b = {}
        for v in reversed(order):
            kids = [w for w in G.neighbors(v) if parent.get(w) == v]
            av = Fr(1)
            for c in kids:
                av *= a[c] + b[c]
            bv = Fr(0)
            for c in kids:
                rest = Fr(1)
                for c2 in kids:
                    if c2 is not c:
                        rest *= a[c2] + b[c2]
                bv += z[v] * z[c] * a[c] * rest
            a[v], b[v] = av, bv
        total *= a[root] + b[root]
    return total


def pi_loaded(beta: nx.Graph, load: dict) -> Fr:
    """pi of the loaded backbone via the per-vertex factorization."""
    z = {v: z_of(beta.degree(v), load[v]) for v in beta.nodes()}
    p = Fr(1)
    for v in beta.nodes():
        p *= F_of(beta.degree(v), load[v])
    return p * psi_weighted(beta, z)


# ------------------------------------------------------- literal ground truth
def literal_tree(beta: nx.Graph, load: dict) -> nx.Graph:
    """The literal tree: backbone plus, per vertex v, load[v] length-2 cherry paths."""
    G = beta.copy()
    nxt = max(beta.nodes()) + 1
    for v in beta.nodes():
        for _ in range(load[v]):
            G.add_edge(v, nxt)
            G.add_edge(nxt, nxt + 1)
            nxt += 2
    return G


def pi_literal(T: nx.Graph) -> Fr:
    """per(L(T)) / prod deg for a tree, via the matching-sum identity
        per(L(T)) = sum_{matchings M} prod_{v NOT in M} deg(v)
    (each transposition contributes (-1)(-1) = +1 in the permanent expansion;
    dividing by prod deg gives pi = sum_M prod_{v in M} 1/deg v).  The identity
    itself is anchored against a brute-force permanent in verify_permanent_anchor."""
    z = {v: Fr(1, T.degree(v)) for v in T.nodes()}
    return psi_weighted(T, z)


def _brute_permanent(T: nx.Graph) -> int:
    nodes = sorted(T.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    L = [[0] * n for _ in range(n)]
    for v in nodes:
        L[idx[v]][idx[v]] = T.degree(v)
    for u, v in T.edges():
        L[idx[u]][idx[v]] = -1
        L[idx[v]][idx[u]] = -1
    tot = 0
    for perm in itertools.permutations(range(n)):
        p = 1
        for i in range(n):
            p *= L[i][perm[i]]
            if p == 0:
                break
        tot += p
    return tot


def verify_permanent_anchor(n_max: int = 8) -> dict:
    """Anchor pi_literal's matching-sum identity against the brute permanent on
    every tree <= n_max vertices."""
    checked = 0
    for n in range(2, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            d = Fr(1)
            for v in T.nodes():
                d *= T.degree(v)
            assert pi_literal(T) == Fr(_brute_permanent(T)) / d, n
            checked += 1
    return {"permanent_anchor_exact": True, "cases": checked}


def verify_factorization(n_max: int = 6, load_patterns=((0,), (1,), (3,), (5,), (0, 5), (2, 5), (0, 3, 5))) -> dict:
    """(1): pi_loaded == pi_literal for every backbone <= n_max vertices and cyclically-assigned
    mixed load patterns (covers uniform and mixed, loads 0..5)."""
    checked = 0
    for n in range(2, n_max + 1):
        for beta in nx.nonisomorphic_trees(n):
            beta = nx.convert_node_labels_to_integers(beta)
            nodes = sorted(beta.nodes())
            for pat in load_patterns:
                load = {v: pat[i % len(pat)] for i, v in enumerate(nodes)}
                lhs = pi_loaded(beta, load)
                rhs = pi_literal(literal_tree(beta, load))
                assert lhs == rhs, (n, pat, lhs, rhs)
                checked += 1
    return {"factorization_exact": True, "cases": checked}


# ----------------------------------------------------- mixed-load Kelmans step
def kelmans_step(G: nx.Graph, a, b):
    if not G.has_edge(a, b):
        return None
    movers = [w for w in list(G.neighbors(b)) if w != a]
    if not movers:
        return None
    H = G.copy()
    for w in movers:
        H.remove_edge(b, w)
        H.add_edge(a, w)
    return H if nx.is_tree(H) else None


def _environment_quantities(beta: nx.Graph, a, b, w: dict):
    others = [x for x in beta.nodes() if x != a]
    comp_b = nx.node_connected_component(beta.subgraph(others), b)
    Ra = [x for x in beta.nodes() if x != a and x not in comp_b]
    movers = [x for x in comp_b if x != b]
    FQ = psi_weighted(beta.subgraph(Ra), w)
    FS = psi_weighted(beta.subgraph(movers), w)
    MQ = (psi_weighted(beta.subgraph([a] + Ra), w) - FQ) / w[a]
    MS = (psi_weighted(beta.subgraph([b] + movers), w) - FS) / w[b]
    return FQ, MQ, FS, MS


def _coeffs(da: int, db: int, ca: int, cb: int):
    """Bilinear coefficients c1..c4 for the mixed-load adjacent Kelmans step.
    After the step: deg a -> da+db-1, deg b -> 1; loads UNCHANGED (cherries ride
    with their vertex).  Only a,b change degree, so only their F and z move."""
    Fa, Fb = F_of(da, ca), F_of(db, cb)
    Fap, Fbp = F_of(da + db - 1, ca), F_of(1, cb)
    za, zb = z_of(da, ca), z_of(db, cb)
    zap, zbp = z_of(da + db - 1, ca), z_of(1, cb)
    c1 = Fap * Fbp * (1 + zap * zbp) - Fa * Fb * (1 + za * zb)
    c2 = Fap * Fbp * zap - Fa * Fb * za
    c3 = Fap * Fbp * zap - Fa * Fb * zb
    c4 = -Fa * Fb * za * zb
    return c1, c2, c3, c4


def verify_identity(n_max: int = 7, load_patterns=((0, 5), (5, 0), (2, 5, 0), (5,), (0,), (1, 4))) -> dict:
    """(2): the exact bilinear identity for mixed loads:
    pi' - pi = P * FS * FQ * (c1 + c2 sQ + c3 sS + c4 sQ sS),  P = prod of untouched F's."""
    checked = 0
    for n in range(3, n_max + 1):
        for beta in nx.nonisomorphic_trees(n):
            beta = nx.convert_node_labels_to_integers(beta)
            nodes = sorted(beta.nodes())
            for pat in load_patterns:
                load = {v: pat[i % len(pat)] for i, v in enumerate(nodes)}
                z = {v: z_of(beta.degree(v), load[v]) for v in beta.nodes()}
                for a, b in itertools.permutations(beta.nodes(), 2):
                    bp = kelmans_step(beta, a, b)
                    if bp is None:
                        continue
                    FQ, MQ, FS, MS = _environment_quantities(beta, a, b, z)
                    c1, c2, c3, c4 = _coeffs(beta.degree(a), beta.degree(b), load[a], load[b])
                    sQ, sS = MQ / FQ, MS / FS
                    Phi = c1 + c2 * sQ + c3 * sS + c4 * sQ * sS
                    P = Fr(1)
                    for v in beta.nodes():
                        if v not in (a, b):
                            P *= F_of(beta.degree(v), load[v])
                    lhs = pi_loaded(bp, load) - pi_loaded(beta, load)
                    assert lhs == P * FS * FQ * Phi, (n, pat, a, b)
                    checked += 1
    return {"identity_exact": True, "cases": checked}


# ------------------------------------------------ (3) the monotone domain, exactly
def corner_census(load_vals=(0, 1, 2, 3, 4, 5), deg_max: int = 12, z1_load: int = 0):
    """For each (ca, cb) load pair, over 1<=da<=deg_max, 2<=db<=deg_max: are all four
    corners >= 0 with the box cap z1 = z_of(1, z1_load) on both sides (z1_load = the
    minimum load among environment neighbours; 0 = fully pessimistic, 5 = all-arm env)?
    Returns {(ca,cb): {"all_nonneg": bool, "worst": (value, da, db, corner)}}."""
    out = {}
    z1 = z_of(1, z1_load)
    for ca in load_vals:
        for cb in load_vals:
            worst = (Fr(1), None, None, None)
            ok = True
            for da in range(1, deg_max + 1):
                for db in range(2, deg_max + 1):
                    c1, c2, c3, c4 = _coeffs(da, db, ca, cb)
                    Q, S = (da - 1) * z1, (db - 1) * z1
                    cs = {"C0": c1, "C1": c1 + c2 * Q, "C3": c1 + c3 * S,
                          "C2": c1 + c2 * Q + c3 * S + c4 * Q * S}
                    m = min(cs.values())
                    if m < worst[0]:
                        name = min(cs, key=cs.get)
                        worst = (m, da, db, name)
                    if m < 0:
                        ok = False
            out[(ca, cb)] = {"all_nonneg": ok, "worst": (float(worst[0]), worst[1], worst[2], worst[3])}
    return out


def true_step_census(n_max: int = 8, load_vals=(0, 5), hub_arm_only: bool = False):
    """Ground truth: enumerate actual mixed-load Kelmans steps and record every
    pi-DECREASING one, keyed by (ca, cb, da, db).  load assignment: all functions
    V -> load_vals would explode; use all assignments for n <= 6, cyclic patterns
    beyond."""
    bad = {}
    checked = 0
    for n in range(3, n_max + 1):
        for beta in nx.nonisomorphic_trees(n):
            beta = nx.convert_node_labels_to_integers(beta)
            nodes = sorted(beta.nodes())
            if n <= 6:
                assigns = itertools.product(load_vals, repeat=n)
            else:
                assigns = [tuple(load_vals[i % len(load_vals)] for i in range(n)),
                           tuple(load_vals[(i + 1) % len(load_vals)] for i in range(n))]
            for pat in assigns:
                load = dict(zip(nodes, pat))
                for a, b in itertools.permutations(beta.nodes(), 2):
                    bp = kelmans_step(beta, a, b)
                    if bp is None:
                        continue
                    d = pi_loaded(bp, load) - pi_loaded(beta, load)
                    checked += 1
                    if d < 0:
                        key = (load[a], load[b], beta.degree(a), beta.degree(b))
                        rec = bad.setdefault(key, {"count": 0, "worst": Fr(0)})
                        rec["count"] += 1
                        if d < rec["worst"]:
                            rec["worst"] = d
    return {"steps_checked": checked, "decreasing_classes": {k: {"count": v["count"], "worst": float(v["worst"])}
                                                            for k, v in sorted(bad.items())}}


# ------------------------------- (4) THE TWO-HUB EXCHANGE DICHOTOMY (exact, all p>=q>=1)
# On the pure two-hub family -- hub a with p arm-leaves (load-5 backbone leaves) + own load ca,
# adjacent hub b with q arm-leaves + load cb -- the environment sigmas are EXACT (every arm is a
# load-5 leaf: z = 3/23, rho = 1):  sigma_Q = p*3/23,  sigma_S = q*3/23.  So the sign of the
# hub-merge b -> a is the sign of the explicit rational
#     Phi2(p,q,ca,cb) = c1 + c2*(3p/23) + c3*(3q/23) + c4*(9pq/529),
# with c1..c4 = _coeffs(p+1, q+1, ca, cb).

TWOHUB_CB0_NONNEG_EXCEPTIONS = {
    (0, 0): {(1, 1), (2, 1), (2, 2), (3, 1)},
    (1, 0): {(1, 1)},
}


def two_hub_phi(p: int, q: int, ca: int, cb: int) -> Fr:
    z1 = z_of(1, 5)                       # = 3/23, the arm activity
    c1, c2, c3, c4 = _coeffs(p + 1, q + 1, ca, cb)
    return c1 + c2 * p * z1 + c3 * q * z1 + c4 * p * q * z1 * z1


def verify_two_hub_dichotomy_grid(pq_max: int = 40) -> dict:
    """Exact-grid form of the dichotomy, hubward p >= q >= 1:
       cb >= 1            =>  Phi2 > 0   (merge strictly increases pi),
       cb = 0, ca >= 2    =>  Phi2 < 0   (merge strictly DECREASES pi),
       cb = 0, ca <= 1    =>  Phi2 < 0 except the finite exception set above.
    Also cross-checks Phi2's sign against the actual pi difference on the literal
    two-hub trees for a diagonal sample."""
    checked = 0
    for ca in range(6):
        for cb in range(6):
            for p in range(1, pq_max + 1):
                for q in range(1, p + 1):
                    ph = two_hub_phi(p, q, ca, cb)
                    if cb >= 1:
                        assert ph > 0, (ca, cb, p, q)
                    elif ca >= 2:
                        assert ph < 0, (ca, cb, p, q)
                    else:
                        exc = (p, q) in TWOHUB_CB0_NONNEG_EXCEPTIONS[(ca, cb)]
                        assert (ph >= 0) == exc, (ca, cb, p, q)
                    checked += 1
    # ground-truth cross-check on the literal family (sign of pi' - pi)
    xchecked = 0
    for (ca, cb, p, q) in [(5, 5, 4, 3), (0, 5, 6, 2), (3, 1, 5, 5), (2, 0, 4, 2),
                           (5, 0, 6, 3), (0, 0, 1, 1), (0, 0, 4, 4), (1, 0, 1, 1), (1, 0, 3, 2)]:
        G = nx.Graph(); G.add_edge(0, 1)
        load = {0: ca, 1: cb}; nxt = 2
        for _ in range(p):
            G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
        for _ in range(q):
            G.add_edge(1, nxt); load[nxt] = 5; nxt += 1
        Gp = kelmans_step(G, 0, 1)
        d = pi_loaded(Gp, load) - pi_loaded(G, load)
        ph = two_hub_phi(p, q, ca, cb)
        assert (d > 0) == (ph > 0) and (d < 0) == (ph < 0), (ca, cb, p, q)
        xchecked += 1
    return {"two_hub_grid_ok": True, "grid_cases": checked, "literal_crosschecks": xchecked}


def certify_two_hub_symbolic() -> dict:
    """THE SYMBOLIC CERTIFICATE (all p >= q >= 1, per load cell).  Substitute
    p = 1 + s + r, q = 1 + s (r, s >= 0 <=> p >= q >= 1), clear denominators, and
    inspect coefficient signs of the numerator polynomial in (r, s):

      * cb in {1..5}, ca in {0..5} (30 cells): numerator has ALL-NONNEGATIVE
        coefficients and a STRICTLY POSITIVE constant term over a positive
        denominator  =>  Phi2 > 0 for ALL p >= q >= 1.       [monotone, all N]
      * cb = 0, ca in {2..5} (4 cells): all-NONPOSITIVE numerator, strictly
        negative constant  =>  Phi2 < 0 for ALL p >= q >= 1. [anti-monotone, all N]
      * cb = 0, ca in {0,1} (2 cells): genuinely mixed; closed by the shifted
        certificates below + the finite exception lists.

    For the 2 mixed cells the sign is settled COMPLETELY by:
      (0,0): q >= 3 all-nonpos via q = 3+s'; q in {1,2} are 1-var polynomials in p,
             negative for p >= 4 resp. p >= 3 (all-nonpos after shift), exceptions
             (1,1),(2,1),(2,2),(3,1) checked exactly.
      (1,0): q >= 2 all-nonpos via q = 2+s'; q = 1 negative for p >= 2, exception (1,1).
    """
    import sympy as sp
    r, s = sp.symbols("r s", nonnegative=True)

    def cell_poly(ca, cb, psub, qsub):
        dasym, dbsym = psub + 1, qsub + 1

        def Fs(deg, c):
            if c == 0:
                return sp.Integer(1)
            D = deg + c
            return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

        def zs(deg, c):
            return sp.Integer(3) / (3 * deg + 4 * c)

        z1 = sp.Rational(3, 23)
        Fa, Fb = Fs(dasym, ca), Fs(dbsym, cb)
        Fap, Fbp = Fs(dasym + dbsym - 1, ca), Fs(1, cb)
        za, zb = zs(dasym, ca), zs(dbsym, cb)
        zap, zbp = zs(dasym + dbsym - 1, ca), zs(1, cb)
        c1 = Fap * Fbp * (1 + zap * zbp) - Fa * Fb * (1 + za * zb)
        c2 = Fap * Fbp * zap - Fa * Fb * za
        c3 = Fap * Fbp * zap - Fa * Fb * zb
        c4 = -Fa * Fb * za * zb
        Phi = c1 + c2 * psub * z1 + c3 * qsub * z1 + c4 * psub * qsub * z1 ** 2
        num, den = sp.fraction(sp.together(Phi))
        pnum = sp.Poly(sp.expand(num), r, s)
        pden = sp.Poly(sp.expand(den), r, s)
        dc = pden.coeffs()
        dsg = 1 if all(cf > 0 for cf in dc) else (-1 if all(cf < 0 for cf in dc) else 0)
        assert dsg != 0, (ca, cb, "denominator not sign-definite")
        return [cf * dsg for cf in pnum.coeffs()], pnum.eval({r: 0, s: 0}) * dsg

    out = {"increasing_cells": 0, "decreasing_cells": 0}
    qq = 1 + s
    pp = qq + r
    for cb in range(6):
        for ca in range(6):
            if cb >= 1:
                nc, const = cell_poly(ca, cb, pp, qq)
                assert all(cf >= 0 for cf in nc) and const > 0, (ca, cb)
                out["increasing_cells"] += 1
            elif ca >= 2:
                nc, const = cell_poly(ca, cb, pp, qq)
                assert all(cf <= 0 for cf in nc) and const < 0, (ca, cb)
                out["decreasing_cells"] += 1
    # the two mixed cb=0 cells: shifted all-nonpos certificates + finite exceptions
    for (ca, qmin, pmin_by_smallq) in [(0, 3, {1: 4, 2: 3}), (1, 2, {1: 2})]:
        qq2 = qmin + s
        pp2 = qq2 + r
        nc, const = cell_poly(ca, 0, pp2, qq2)
        assert all(cf <= 0 for cf in nc) and const < 0, (ca, 0, "q-tail")
        for qfix, pmin in pmin_by_smallq.items():
            pp3 = pmin + r
            nc, const = cell_poly(ca, 0, pp3, sp.Integer(qfix))
            assert all(cf <= 0 for cf in nc) and const < 0, (ca, 0, qfix)
        # the finitely many remaining pairs match the recorded exception set exactly
        for p in range(1, max(pmin_by_smallq.values()) + 1):
            for q in range(1, min(p, qmin - 1) + 1):
                if q in pmin_by_smallq and p >= pmin_by_smallq[q]:
                    continue
                exc = (p, q) in TWOHUB_CB0_NONNEG_EXCEPTIONS[(ca, 0)]
                assert (two_hub_phi(p, q, ca, 0) >= 0) == exc, (ca, 0, p, q)
    out["mixed_cells_closed"] = 2
    return out


# ---------------- (5) GENERAL ENVIRONMENTS: the box-corner certificate (25 cells, all N)
GENERAL_ENV_CERTIFIED_CELLS = [
    (0, 1), (0, 2), (0, 3), (0, 4),
    (1, 1), (1, 2), (1, 3),
    (2, 1), (2, 2), (2, 3), (2, 4),
    (3, 1), (3, 2), (3, 3), (3, 4),
    (4, 1), (4, 2), (4, 3), (4, 4), (4, 5),
    (5, 1), (5, 2), (5, 3), (5, 4), (5, 5),
]


def certify_general_env_box() -> dict:
    """GENERAL-ENVIRONMENT THEOREM (box certificate, all N).  For the adjacent hubward
    Kelmans step (da >= db >= 2) on ANY loaded backbone in which every environment
    neighbour x of a and of b satisfies 3*deg(x) + 4*load(x) >= 23 (z_x <= 3/23; a
    load-5 arm-leaf achieves 23 exactly, a bare hub needs degree >= 8), the step is
    pi-non-decreasing for every load cell (ca, cb) in GENERAL_ENV_CERTIFIED_CELLS.

    Proof: sigma_Q in [0, (da-1)*3/23], sigma_S in [0, (db-1)*3/23] (marginal bounds,
    load-blind since each z_x <= 3/23 and rho_x <= 1), Phi bilinear => min at a box
    corner; each corner, over the shift da = 2+v+u, db = 2+v (u,v >= 0 <=> da >= db >= 2),
    has an all-nonnegative numerator over a positive denominator.  Verified here
    symbolically per cell.  The remaining cb >= 1 cells ({(0,5),(1,4),(1,5),(2,5),(3,5)})
    are NOT box-certifiable (the crude sigma_S = 0 corner fails) but ARE strictly
    increasing on the exact two-hub family -- the box, not the move, is what fails."""
    import sympy as sp
    u, v = sp.symbols("u v", nonnegative=True)
    da_s = 2 + v + u
    db_s = 2 + v

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    z1 = sp.Rational(3, 23)
    certified = 0
    for (ca, cb) in GENERAL_ENV_CERTIFIED_CELLS:
        Fa, Fb = Fs(da_s, ca), Fs(db_s, cb)
        Fap, Fbp = Fs(da_s + db_s - 1, ca), Fs(1, cb)
        za, zb = zs(da_s, ca), zs(db_s, cb)
        zap, zbp = zs(da_s + db_s - 1, ca), zs(1, cb)
        c1 = Fap * Fbp * (1 + zap * zbp) - Fa * Fb * (1 + za * zb)
        c2 = Fap * Fbp * zap - Fa * Fb * za
        c3 = Fap * Fbp * zap - Fa * Fb * zb
        c4 = -Fa * Fb * za * zb
        Q, S = (da_s - 1) * z1, (db_s - 1) * z1
        for expr in (c1, c1 + c2 * Q, c1 + c3 * S, c1 + c2 * Q + c3 * S + c4 * Q * S):
            num, den = sp.fraction(sp.together(expr))
            pnum = sp.Poly(sp.expand(num), u, v)
            pden = sp.Poly(sp.expand(den), u, v)
            dc = pden.coeffs()
            dsg = 1 if all(cf > 0 for cf in dc) else (-1 if all(cf < 0 for cf in dc) else 0)
            assert dsg != 0 and all(cf * dsg >= 0 for cf in pnum.coeffs()), (ca, cb)
        certified += 1
    return {"box_certified_cells": certified}


def three_hub_residual_probe(p_max: int = 8) -> dict:
    """The 5 non-box-certifiable cb>=1 cells, probed on REAL 3-hub backbones
    (A-B-C path; merge B->A with movers = B's arms + the C hub-subtree, i.e. the
    exact configuration whose (sigma_Q hi, sigma_S lo) corner defeats the box AND
    the (db-2)*z1 sub-box): 0 decreases found.  Evidence the residual-cell corner
    failure is a CERTIFICATE artifact, not a real failure -- the cells likely close
    with an exact treatment of the single hub-mover term (its z*rho contribution),
    left as the sharp follow-up."""
    decreases = 0
    tested = 0
    for (ca, cb) in [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]:
        for p in range(1, p_max + 1):
            for q in range(1, p + 1):
                for rr in (1, 4, 8):
                    for cc_ in (0, 5):
                        G = nx.Graph(); G.add_edge(0, 1); G.add_edge(1, 2)
                        load = {0: ca, 1: cb, 2: cc_}
                        nxt = 3
                        for hub, cnt in ((0, p), (1, q), (2, rr)):
                            for _ in range(cnt):
                                G.add_edge(hub, nxt); load[nxt] = 5; nxt += 1
                        d = pi_loaded(kelmans_step(G, 0, 1), load) - pi_loaded(G, load)
                        tested += 1
                        if d < 0:
                            decreases += 1
    assert decreases == 0, "residual-cell decrease found -- update still_open!"
    return {"three_hub_residual_tested": tested, "decreases": decreases}


# ------------------------------------------------- (6) in-family witnesses + run_all
def verify_witnesses() -> dict:
    """The K-boundary is REAL: de-loaded-donor merges strictly DECREASE pi on
    stratum-(ii) trees (hubs + load-5 arm-leaves) -- these are the configurations the
    rewrite must never fire; they are exactly the vertex-budget cases."""
    def two_hub_tree(p, q, ca, cb):
        G = nx.Graph(); G.add_edge(0, 1)
        load = {0: ca, 1: cb}; nxt = 2
        for _ in range(p):
            G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
        for _ in range(q):
            G.add_edge(1, nxt); load[nxt] = 5; nxt += 1
        return G, load

    decreases = 0
    for (p, q, ca, cb) in [(5, 4, 5, 0), (8, 6, 3, 0), (10, 10, 0, 0)]:
        G, load = two_hub_tree(p, q, ca, cb)
        d = pi_loaded(kelmans_step(G, 0, 1), load) - pi_loaded(G, load)
        assert d < 0, (p, q, ca, cb)
        decreases += 1
    increases = 0
    for (p, q, ca, cb) in [(5, 4, 5, 5), (8, 3, 3, 2), (5, 1, 0, 5), (4, 1, 1, 4)]:
        G, load = two_hub_tree(p, q, ca, cb)
        d = pi_loaded(kelmans_step(G, 0, 1), load) - pi_loaded(G, load)
        assert d > 0, (p, q, ca, cb)
        increases += 1
    return {"deloaded_donor_decreases": decreases, "loaded_donor_increases": increases}


def run_all():
    out = {}
    out["anchor"] = verify_permanent_anchor()
    out["factorization"] = verify_factorization()
    out["identity"] = verify_identity()
    out["two_hub_grid"] = verify_two_hub_dichotomy_grid()
    out["two_hub_symbolic"] = certify_two_hub_symbolic()
    out["general_env_box"] = certify_general_env_box()
    out["residual_probe"] = three_hub_residual_probe()
    out["witnesses"] = verify_witnesses()
    out["k_boundary_status"] = {
        "monotone_certified_all_N": "hubward da>=db>=2, donor load cb>=1: 25 cells for ANY "
                                    "z<=3/23 environment (box) + all 30 cells on the exact "
                                    "two-hub family (exact sigmas)",
        "provably_anti_monotone": "cb=0 (de-loaded donor), ca>=2: strictly decreasing for ALL "
                                  "p>=q>=1 -- no local fix exists; ca<=1: decreasing except a "
                                  "finite explicit exception set",
        "still_open": [
            "cb>=1 cells {(0,5),(1,4),(1,5),(2,5),(3,5)} in general (non-two-hub) environments: "
            "box fails at the (sigma_Q hi, sigma_S lo) corner and the (db-2)*z1 sub-box still fails "
            "the same corner, but 0 real decreases on 3-hub probes (three_hub_residual_probe) -- "
            "likely an artifact; needs exact treatment of the single hub-mover term",
            "steps whose environment contains a low-z vertex (3*deg+4*load < 23, e.g. a small "
            "bare hub) adjacent to the exchange",
            "the de-loaded-donor configurations themselves: provably NOT reducible by K/H -- "
            "eliminating them is the fixed-n vertex-budget comparison (the n<=240 territory), "
            "NOT a rewrite-monotonicity question",
        ],
        "rewrite_ordering_consequence": "fire K/H only hubward and only while the donor still "
                                        "carries load >= 1; de-load (R6) ONLY the final hub, last",
        "conjecture1_proved": False,
    }
    for k, vv in out.items():
        print(f"  {k}: {vv}")
    return out


if __name__ == "__main__":
    run_all()
