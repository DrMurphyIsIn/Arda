"""Conjecture Piece 3 (matched form): the star maximizes pi over all backbones.

At matched centers and cherries, the star K_{1,N-1} strictly maximizes pi(beta[c])
over ALL backbone trees beta on N centers (each center carrying c cherries). This is
the "the backbone is a star" condition of the star-of-cherry-bundles conjecture, in
the natural matched formulation, and it generalizes Theorem thm:starpath (star beats
path) to star-beats-every-backbone.

Reduction to a polynomial in c.  Every matching term of pi(beta[c]) carries the same
factor (3/2)^{(c-1)N} (because a center of degree d contributes F(d)=(3/2)^{c-1}(3d+c)/(2d)
when free, and a matched backbone edge contributes (3/2)^{2c}/(d_u d_v); the (3/2)
exponents sum to (c-1)N + 2|M| across every matching M). Hence
    R_beta(c) := pi(beta[c]) / (3/2)^{(c-1)N}
             = sum_{M matching of beta} (9/4)^{|M|} * prod_{(u,v) in M} 1/((deg_u+c)(deg_v+c))
                                       * prod_{v unmatched} (3(deg_v+c)+c) / (2(deg_v+c))
is a RATIONAL FUNCTION of c with rational coefficients (deg = backbone degree). So
sign(pi_star - pi_beta) = sign(R_star(c) - R_beta(c)); clearing denominators gives an
integer polynomial in c whose positivity for c >= 3 is certified by exact real-root
isolation.

certify_star_beats_backbones(N) proves, for every non-star tree beta on N nodes,
R_star(c) - R_beta(c) > 0 for all real c >= 3. Verified True for N = 2..10 (105 trees at
N=10). For ALL N the statement reduces to a single exchange lemma -- the hubward leaf
transfer (move a leaf-center from its non-hub parent to a maximum-degree center) strictly
increases pi -- which is verified numerically (see tests) but not proven in general here.

Honest scope: this settles the backbone condition at MATCHED centers/cherries for
backbones of up to 10 centers, all c >= 3. It does NOT prove the full conjecture (which
also needs the leg-length condition -- see legs.py, proven at rate level -- and an
all-N proof of the exchange lemma, and the exact vertex-count global maximum).
"""
from __future__ import annotations

import networkx as nx
import sympy as sp

c = sp.symbols("c", positive=True)

MAX_CERTIFIED_N = 10   # certify_star_beats_backbones proven True for all N <= this


def _R(G):
    """pi(G[c]) / (3/2)^{(c-1)N} as an exact rational function of c (G = backbone)."""
    nodes = list(G.nodes())
    D = {v: G.degree(v) + c for v in nodes}
    free = {v: (3 * D[v] + c) / (2 * D[v]) for v in nodes}   # (3/2)^{1-c} F(D_v)
    edges = list(G.edges())

    def rec(i, used):
        if i == len(edges):
            t = sp.Integer(1)
            for v in nodes:
                if v not in used:
                    t = t * free[v]
            return t
        s = rec(i + 1, used)
        u, v = edges[i]
        if u in used or v in used:
            return s
        w = sp.Rational(9, 4) / (D[u] * D[v])               # (3/2)^2 / (D_u D_v)
        return s + w * rec(i + 1, used | {u, v})

    return sp.cancel(rec(0, frozenset()))


def _is_star(T) -> bool:
    n = T.number_of_nodes()
    return max(dict(T.degree()).values()) == n - 1


def _poly_positive_for_c_ge_3(diff) -> bool:
    """Certify diff(c) > 0 for all real c >= 3 by exact real-root isolation."""
    num, _den = sp.fraction(sp.cancel(diff))
    p = sp.Poly(sp.expand(num), c)
    if p.LC() <= 0:                       # star must win as c -> infinity too
        return False
    if p.eval(3) <= 0:
        return False
    return not any(r >= 3 for r in p.real_roots())


def certify_star_beats_backbones(n_centers: int) -> bool:
    """Prove the star K_{1,N-1} strictly maximizes pi(beta[c]) over all backbones
    beta on N = n_centers centers, for every real c >= 3.

    Returns True iff, for every non-star tree beta on N nodes, R_star(c) - R_beta(c)
    is positive for all c >= 3 (exact root isolation). N >= 2.
    """
    if n_centers < 2:
        return True
    trees = list(nx.nonisomorphic_trees(n_centers))
    star = next(T for T in trees if _is_star(T))
    Rs = _R(star)
    for T in trees:
        if _is_star(T):
            continue
        if not _poly_positive_for_c_ge_3(Rs - _R(T)):
            return False
    return True


# ---------------------------------------------------------------------------
# Toward an all-N proof: an exact factorization + a rigorously star-maximal half.
#
# Because g(D) := D*F(D) = (K/2)(3D+c) is AFFINE in D (K=(3/2)^{c-1}), pi factors:
#     pi(beta[c]) = ( prod_v F(D_v) ) * Psi(beta),
#     Psi(beta)   = sum_{M matching} prod_{(u,v) in M} (3/2)^{2c} / (g(D_u) g(D_v)).
# The first factor is MAXIMIZED by the star and provably so: log F is convex
# (d^2/dx^2 [log(3x+c) - log x] = (6cx + c^2)/(x^2 (3x+c)^2) > 0), so
# sum_v log F(D_v) at fixed sum_v D_v is Schur-convex, hence maximized at the
# majorization-largest center-degree sequence -- which is the star's
# (N-1+c, 1+c, ..., 1+c), as the star's degree sequence majorizes every tree's.
# The second factor Psi is star-MINIMAL (fewest matchings). So pi(star) >= pi(beta)
# reduces to prod_F(star)/prod_F(beta) >= Psi(beta)/Psi(star): a provable convexity
# gain against a matching-count loss. Only the first half is proven here; the
# Psi-ratio bound is the remaining (intrinsically tight) step.
# ---------------------------------------------------------------------------
from fractions import Fraction as _Fr   # noqa: E402


def _F_num(D, cc):
    """F(D) at integer cherry count cc, exact rational."""
    return _Fr(3, 2) ** cc + _Fr(cc, 2 * D) * _Fr(3, 2) ** (cc - 1)


def _g_num(D, cc):
    """g(D) = D * F(D) = (K/2)(3D+c), affine in D (exact rational)."""
    return D * _F_num(D, cc)


def pi_factored(G, cc):
    """Return (prod_F, Psi) with pi(G[cc]) = prod_F * Psi (exact rationals)."""
    nodes = list(G.nodes())
    D = {v: G.degree(v) + cc for v in nodes}
    prod_F = _Fr(1)
    for v in nodes:
        prod_F *= _F_num(D[v], cc)
    edges = list(G.edges())

    def rec(i, used):
        if i == len(edges):
            return _Fr(1)
        s = rec(i + 1, used)
        u, v = edges[i]
        if u in used or v in used:
            return s
        w = _Fr(3, 2) ** (2 * cc) / (_g_num(D[u], cc) * _g_num(D[v], cc))
        return s + w * rec(i + 1, used | {u, v})

    return prod_F, rec(0, frozenset())


def _majorizes(seq_a, seq_b):
    """True iff sorted-descending seq_a majorizes seq_b (equal sums assumed)."""
    a = sorted(seq_a, reverse=True)
    b = sorted(seq_b, reverse=True)
    if sum(a) != sum(b):
        return False
    ca = cb = 0
    for i in range(len(a)):
        ca += a[i]
        cb += b[i]
        if ca < cb:
            return False
    return True


def certify_star_beats_broom_all_N():
    """Prove the star K_{1,N-1} strictly beats its NEAREST rival for ALL N, c.

    Among backbones on N centers, the runner-up (second-largest pi) is always the
    "broom" B_N: a hub of degree N-2 carrying N-3 leaves and one length-2 leg
    (degree sequence (N-2, 2, 1, ..., 1)). We prove pi(star) > pi(broom) for every
    integer N >= 5 and real c >= 3.

    Method (exact, root-free): both pi share the factor F(1+c)^{N-2}; dividing it out
    leaves S - B, a rational function of (N, c) and integer powers of 3/2. Setting
    X = (3/2)^c and shifting N = 5+m, c = 3+s (m, s >= 0), numerator and denominator
    are polynomials in (m, s, X) with only NONNEGATIVE coefficients -- so both are
    positive and pi(star) - pi(broom) > 0. Returns True iff the certificate holds.
    """
    Nn, cc = sp.symbols("N c", positive=True)
    Th = sp.Rational(3, 2)

    def Ff(D):
        return Th**cc + cc / (2 * D) * Th**(cc - 1)

    def Wt(du, dv):
        return Th**(2 * cc) / (du * dv)

    Dl = 1 + cc
    S = Ff(Nn - 1 + cc) * Ff(Dl) + (Nn - 1) * Wt(Nn - 1 + cc, Dl)        # pi_star / F(1+c)^{N-2}
    DH, Dq = Nn - 2 + cc, 2 + cc
    wHL, wHq, wql = Wt(DH, Dl), Wt(DH, Dq), Wt(Dq, Dl)
    B = (Ff(DH) * Ff(Dq) + (Nn - 3) * wHL * Ff(Dq) / Ff(Dl) + wHq         # pi_broom / F(1+c)^{N-2}
         + wql * Ff(DH) / Ff(Dl) + (Nn - 3) * wHL * wql / Ff(Dl)**2)

    X = sp.symbols("X", positive=True)

    def to_X(z):
        z = sp.powsimp(sp.expand(z), force=True)
        return sp.expand(z.subs({
            Th**(2 * cc): X**2, Th**(cc - 1): X * sp.Rational(2, 3),
            Th**(2 * cc - 1): X**2 * sp.Rational(2, 3), Th**(2 * cc - 2): X**2 * sp.Rational(4, 9),
            Th**(2 * cc - 3): X**2 * sp.Rational(8, 27), Th**cc: X,
            Th**(cc + 1): X * Th, Th**(2 * cc + 1): X**2 * Th}))

    num, den = sp.fraction(sp.together(S - B))
    num_x, den_x = to_X(num), to_X(den)
    if [p for p in (num_x.atoms(sp.Pow) | den_x.atoms(sp.Pow))
            if p.has(cc) and getattr(p, "base", None) == Th]:
        return False
    m, s = sp.symbols("m s", nonnegative=True)
    for expr in (num_x, den_x):
        coeffs = sp.Poly(sp.expand(expr.subs({Nn: 5 + m, cc: 3 + s})), m, s, X).coeffs()
        if not (all(k >= 0 for k in coeffs) and any(k > 0 for k in coeffs)):
            return False
    return True


#: the top-three near-star competitor families (gadget attached to hub 'H'), by deficit j
NEAR_STAR_FAMILIES = {
    "broom_(N-2,2)":   [("H", "q"), ("q", "l")],
    "F2_(N-3,3)":      [("H", "q"), ("q", "a"), ("q", "b")],
    "F3_(N-3,2,2)":    [("H", "q1"), ("q1", "a"), ("H", "q2"), ("q2", "d")],
}


def certify_star_beats_near_star(gadget_edges, hub="H"):
    """Prove pi(star) > pi(hub + B bare leaves + fixed gadget) for ALL N, all c >= 3.

    A "near-star" is a hub carrying B bare leaves plus a fixed gadget (gadget_edges, a
    tree containing 'hub'); N = B + |gadget vertices|. Method: form the bracket
    R = pi/F(1+c)^{B-1} (bounded (3/2)-powers), so
        sign(pi_star - pi_fam) = sign( R_star * F(1+c)^{g-1} - R_fam ),  g = |gadget|.
    Setting X=(3/2)^c and shifting N, c the numerator and denominator are polynomials in
    (m, s, X) with nonnegative coefficients -> positive. Exact, root-free.
    """
    Nn = sp.Symbol("N", positive=True)
    B_ = sp.Symbol("B", positive=True)
    X = sp.symbols("X", positive=True)
    m, s = sp.symbols("m s", nonnegative=True)
    Th = sp.Rational(3, 2)

    def Ff(D):
        return Th**c + c / (2 * D) * Th**(c - 1)

    def Wt(du, dv):
        return Th**(2 * c) / (du * dv)

    def bracket(edges):
        G = nx.Graph()
        G.add_node(hub)
        G.add_edges_from(edges)
        gv = list(G.nodes())
        gd = {v: G.degree(v) for v in gv}

        def D(v):
            return (B_ + gd[v] + c) if v == hub else (gd[v] + c)

        es = list(G.edges())
        matchings = []

        def gen(i, used, chosen):
            if i == len(es):
                matchings.append(chosen)
                return
            gen(i + 1, used, chosen)
            u, v = es[i]
            if u not in used and v not in used:
                gen(i + 1, used | {u, v}, chosen + [(u, v)])

        gen(0, set(), [])
        hub_matched = sp.Integer(0)
        hub_free = sp.Integer(0)
        for M in matchings:
            used = set()
            for e in M:
                used |= set(e)
            wt = sp.Integer(1)
            for (u, v) in M:
                wt *= Wt(D(u), D(v))
            for v in gv:
                if v not in used and v != hub:
                    wt *= Ff(D(v))
            if hub in used:
                hub_matched += wt
            else:
                hub_free += wt
        Dh, Fl = D(hub), Ff(1 + c)
        R = Fl * (hub_matched + hub_free * Ff(Dh)) + hub_free * B_ * Wt(Dh, 1 + c)
        return sp.expand(R), len(gv)

    def to_X(z):
        z = sp.powsimp(sp.expand(z), force=True)
        subs = {}
        for a in range(0, 12):
            for b in range(-12, 13):
                if a == 0 and b == 0:
                    continue
                subs[Th**(a * c + b)] = X**a * Th**b
        return sp.expand(z.subs(subs))

    R_star, g_star = bracket([])                       # g_star = 1
    R_fam, g_fam = bracket(gadget_edges)
    R_star = R_star.subs(B_, Nn - g_star)
    R_fam = R_fam.subs(B_, Nn - g_fam)
    compare = R_star * Ff(1 + c)**(g_fam - 1) - R_fam
    num, den = sp.fraction(sp.together(compare))
    num_x, den_x = to_X(num), to_X(den)
    if [p for p in (num_x.atoms(sp.Pow) | den_x.atoms(sp.Pow))
            if p.has(c) and getattr(p, "base", None) == Th]:
        return False
    n_min = g_fam + 3                                  # smallest N where all matchings exist
    for expr in (num_x, den_x):
        coeffs = sp.Poly(sp.expand(expr.subs({Nn: n_min + m, c: 3 + s})), m, s, X).coeffs()
        if not (all(k >= 0 for k in coeffs) and any(k > 0 for k in coeffs)):
            return False
    return True


def certify_prodF_star_maximal(n_centers, cc=5):
    """Certify the star maximizes prod_v F(D_v) over all backbones on N centers.

    Two independent confirmations, both exact: (i) the star's center-degree
    sequence majorizes every tree's (so, with log F convex, prod_F is Schur-maximal
    at the star), and (ii) directly prod_F(star) >= prod_F(beta) for every beta.
    Returns True iff both hold for all trees on N = n_centers nodes.
    """
    if n_centers < 2:
        return True
    trees = list(nx.nonisomorphic_trees(n_centers))
    star = next(T for T in trees if _is_star(T))
    star_seq = [star.degree(v) + cc for v in star]
    pf_star, _ = pi_factored(star, cc)
    for T in trees:
        if _is_star(T):
            continue
        if not _majorizes(star_seq, [T.degree(v) + cc for v in T]):
            return False
        pf_T, _ = pi_factored(T, cc)
        if not pf_star > pf_T:
            return False
    return True
