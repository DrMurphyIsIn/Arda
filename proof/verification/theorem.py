"""Proven theorem: Pant's B_t = T(t,t,t,t) spider family is NOT maximal for the
Laplacian ratio, for every t >= 3 -- the branching tree B(3,t) strictly beats it.

pi factors through a matching-sum over the 4-center backbone: a center of degree d
with t length-2 cherries contributes (3/2)^t when "free" (each cherry is unmatched-or-
internally-matched: 1 + 1/2 = 3/2) and t/(2d)*(3/2)^(t-1) when the center matches one
of its own cherries. Running the backbone matching-sum with these gives closed forms
(verified against the exact integer Laplacian permanent, see tests):

    pi(B(3,t))     : backbone = star  K_{1,3}  (hub deg 3+t, three arms deg 1+t)
    pi(T(t,t,t,t)) : backbone = path  P_4      (ends deg 1+t, middles deg 2+t)

Their difference is

    pi(B(3,t)) - pi(T(t,t,t,t))
        = (3/2)^(4t) * 2 * P(t) / (81 (t+1)^3 (t+2)^2 (t+3)),
      P(t) = 56 t^4 + 72 t^3 - 162 t^2 - 432 t - 243.

Denominator and (3/2)^(4t) are positive for t > 0, so the sign is that of P(t).
P''(t) = 672 t^2 + 432 t - 324 > 0 for t >= 1, so P' is increasing; P'(3) = 6588 > 0,
hence P'(t) > 0 for t >= 3, so P is increasing on [3, inf); P(3) = 3483 > 0. Therefore
P(t) > 0 and pi(B(3,t)) > pi(T(t,t,t,t)) for ALL t >= 3.  QED.
"""
from __future__ import annotations

import sympy as sp

t = sp.symbols("t", positive=True)
k = sp.symbols("k", positive=True)
_HALF3 = sp.Rational(3, 2)


def _F(d):
    """Center-free backbone weight: cherries free (3/2)^t + center matched to a cherry."""
    return _HALF3 ** t + t / (2 * d) * _HALF3 ** (t - 1)


def _gfree():
    return _HALF3 ** t


def pi_backbone(nodes, edges, dmap):
    """Exact symbolic pi for a 'backbone tree of cherry-bundles' via matching-sum."""
    def matchings(es):
        if not es:
            yield []
            return
        e, rest = es[0], es[1:]
        for m in matchings(rest):
            yield m
        rest2 = [f for f in rest if not set(f) & set(e)]
        for m in matchings(rest2):
            yield [e] + m

    total = 0
    for M in matchings(edges):
        used = set()
        for e in M:
            used.update(e)
        term = 1
        for v in nodes:
            if v not in used:
                term *= _F(dmap[v])
        for (u, v) in M:
            term *= sp.Rational(1) / (dmap[u] * dmap[v]) * _gfree() * _gfree()
        total += term
    return sp.simplify(total)


def pi_branch_star():
    """pi(B(3,t)): hub deg 3+t, three arm-centers deg 1+t (backbone K_{1,3})."""
    return pi_backbone([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3)],
                       {0: 3 + t, 1: 1 + t, 2: 1 + t, 3: 1 + t})


def pi_pant_B():
    """pi(T(t,t,t,t)): Pant's B_t spider, path P_4 backbone, ends deg 1+t, mids deg 2+t."""
    return pi_backbone([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)],
                       {0: 1 + t, 1: 2 + t, 2: 2 + t, 3: 1 + t})


# The k=3 difference-sign polynomial (proven positive for t >= 3).
P = 56 * t**4 + 72 * t**3 - 162 * t**2 - 432 * t - 243


# --- general branching degree k: star K_{1,k} vs path P_{k+1} ---

def pi_star(k):
    """pi(B(k,t)): hub deg k+t joined to k arm-centers deg 1+t, each center t cherries."""
    return pi_backbone(list(range(k + 1)), [(0, i) for i in range(1, k + 1)],
                       {**{0: k + t}, **{i: 1 + t for i in range(1, k + 1)}})


def pi_path(k):
    """pi(T(t,...,t)) on k+1 spine vertices: path P_{k+1}, ends deg 1+t, middles deg 2+t."""
    m = k + 1
    return pi_backbone(list(range(m)), [(i, i + 1) for i in range(m - 1)],
                       {i: (1 + t if i in (0, m - 1) else 2 + t) for i in range(m)})


def sign_polynomial(k):
    """Numerator polynomial in t whose sign equals sign(pi_star(k) - pi_path(k))."""
    diff = sp.simplify((pi_star(k) - pi_path(k)) * (sp.Rational(2, 3)) ** ((k + 1) * t))
    num, _den = sp.fraction(sp.together(diff))
    return sp.Poly(sp.expand(num), t)


# --- why star>path holds for ALL k: asymptotic growth-base dominance ---
# Adding an arm multiplies pi(B(k,t)) by the base F(1+t); adding a center multiplies
# pi(path) by the dominant eigenvalue lambda(t) of the path matching recurrence. One
# checks F(1+t) > lambda(t)  <=>  w < F(1+t)(F(1+t)-F(2+t)),  w=(3/2)^{2t}/(2+t)^2, which
# reduces to ASYMPTOTIC_CUBIC(t) > 0. Hence pi(B(k,t)) >= (3/2)^t F(1+t)^k while the path
# is Theta(lambda^k) with lambda<F(1+t): the ratio grows like (F(1+t)/lambda)^k -> infinity.
ASYMPTOTIC_CUBIC = 4 * t**3 + 2 * t**2 - 12 * t - 9   # > 0 for all t >= 3  (largest root < 2)


def _F(d):
    return sp.Rational(3, 2) ** t + sp.Rational(1, 2) * t / d * sp.Rational(3, 2) ** (t - 1)


def star_arm_base():
    """F(1+t): the per-arm multiplicative growth base of pi(B(k,t))."""
    return _F(1 + t)


def path_eigen_base():
    """lambda(t): dominant eigenvalue of the path matching recurrence."""
    F2 = _F(2 + t)
    w = sp.Rational(3, 2) ** (2 * t) / (2 + t) ** 2
    return (F2 + sp.sqrt(F2**2 + 4 * w)) / 2


def proven_positive_for_t_at_least(poly, t0):
    """Rigorously certify poly(t) > 0 for all real t >= t0.

    True iff the leading coefficient is positive, poly(t0) > 0, and poly has NO real
    root in [t0, inf) (checked by exact real-root isolation). This is a genuine proof,
    not a sampling.
    """
    p = sp.Poly(poly, t) if not isinstance(poly, sp.Poly) else poly
    if p.LC() <= 0:
        return False
    if p.eval(t0) <= 0:
        return False
    return not any(r >= t0 for r in p.real_roots())


# ============================================================================
# ALL-k theorem: the star backbone K_{1,k} beats the path backbone P_{k+1} for
# EVERY integer k >= 3 and real t >= 3 -- a single closed proof superseding the
# finite band k in {3..12} and the asymptotic growth-base argument.
#
# Setup.  a=F(1+t), b=F(2+t), q1=(3/2)^{2t}/((1+t)(2+t)), q2=(3/2)^{2t}/(2+t)^2.
# The "open path" matching sequence z_1=a, z_2=ab+q1, z_i=b z_{i-1}+q2 z_{i-2}
# (i>=3) gives pi(S_N(t)) = a z_{N-1} + q1 z_{N-2}.  Normalising y_i=z_i/a^i, the
# bulk recurrence y_{k+1}=(b/a)y_k+(q2/a^2)y_{k-1} holds for k>=2, and
#     pi(B(k,t))     = a^{k-1} G(k),   G(k)=a F(k+t)+k(3/2)^{2t}/((k+t)(1+t)),
#     pi(S_{k+1}(t)) = a^{k-1} H(k),   H(k)=a^2 y_k + q1 y_{k-1}.
# So R_k := pi(B(k,t))/pi(S_{k+1}(t)) = G(k)/H(k).  From the bulk recurrence
# H(k+1)=(ab+q1)y_k+q2 y_{k-1}, hence
#     G(k+1)H(k)-G(k)H(k+1) = y_k B1(k) + y_{k-1} B2(k),
#     B1(k)=a^2 G(k+1)-(ab+q1)G(k),   B2(k)=q1 G(k+1)-q2 G(k).
# y_k,y_{k-1}>0 (matching sums).  B1,B2>0 for all k>=3, t>=3 (certified below by
# exact real-root-free coefficient positivity), so R_{k+1}>R_k.  With the base
# case R_3>1 (Theorem "P(t)>0"), R_k>1 for all k>=3.  QED.
# ============================================================================


def G_of_k(kk):
    """G(k), where pi(B(k,t)) = F(1+t)^{k-1} * G(k)."""
    return _F(1 + t) * _F(kk + t) + kk * _HALF3**(2 * t) / ((kk + t) * (1 + t))


def bracket_B1(kk):
    """B1(k) = a^2 G(k+1) - (a b + q1) G(k)  (coefficient on y_k)."""
    a, b = _F(1 + t), _F(2 + t)
    q1 = _HALF3**(2 * t) / ((1 + t) * (2 + t))
    return a * a * G_of_k(kk + 1) - (a * b + q1) * G_of_k(kk)


def bracket_B2(kk):
    """B2(k) = q1 G(k+1) - q2 G(k)  (coefficient on y_{k-1})."""
    q1 = _HALF3**(2 * t) / ((1 + t) * (2 + t))
    q2 = _HALF3**(2 * t) / (2 + t)**2
    return q1 * G_of_k(kk + 1) - q2 * G_of_k(kk)


def certify_bracket_positive(expr, k0, t0):
    """Rigorously certify expr(k, t) > 0 for ALL real k >= k0 and t >= t0.

    expr is a rational function of (k, t) and integer powers of 3/2. Set
    X := (3/2)^t > 0; the map (3/2)^(a*t) -> X^a is an exact identity, turning
    numerator and denominator into polynomials in (k, t, X). We verify the
    denominator has only nonnegative (k, t)-coefficients (so it is > 0 for
    k, t > 0), then shift k = k0 + u, t = t0 + s (u, s >= 0) and verify every
    coefficient of the numerator polynomial in (u, s, X) is nonnegative, with at
    least one strictly positive. Nonnegative coefficients with u, s >= 0 and
    X > 0 force the value > 0. This is a genuine Polya-type positivity
    certificate, not sampling. Returns False (fails loudly) if the X-substitution
    leaves any residual (3/2)^(a*t) power.
    """
    X = sp.symbols("X", positive=True)
    u, s = sp.symbols("u s", nonnegative=True)

    def to_X(z):
        z = sp.powsimp(sp.expand(z), force=True)
        z = z.subs({_HALF3**(2 * t): X**2, _HALF3**(t - 1): X * sp.Rational(2, 3),
                    _HALF3**(2 * t - 1): X**2 * sp.Rational(2, 3),
                    _HALF3**(2 * t - 2): X**2 * sp.Rational(4, 9), _HALF3**t: X})
        return sp.expand(z)

    num, den = sp.fraction(sp.together(sp.expand(expr)))
    num_x, den_x = to_X(num), to_X(den)
    residual = [p for p in (num_x.atoms(sp.Pow) | den_x.atoms(sp.Pow))
                if p.has(t) and getattr(p, "base", None) == _HALF3]
    if residual:
        return False
    if not all(c >= 0 for c in sp.Poly(den_x, k, t).coeffs()):
        return False
    shifted = sp.expand(num_x.subs({k: k0 + u, t: t0 + s}))
    coeffs = sp.Poly(shifted, u, s, X).coeffs()
    return bool(all(c >= 0 for c in coeffs) and any(c > 0 for c in coeffs))


def certify_starbeats_path_all_k():
    """Prove pi(B(k,t)) > pi(S_{k+1}(t)) for ALL integers k >= 3, reals t >= 3.

    True iff (i) base case k=3 holds for all t >= 3 (P(t) > 0), and (ii) both
    monotonicity brackets B1, B2 are positive on k >= 3, t >= 3 -- giving
    R_{k+1} > R_k, hence R_k > R_3 > 1 for every k >= 3.
    """
    base = proven_positive_for_t_at_least(P, 3)
    step = (certify_bracket_positive(bracket_B1(k), 3, 3)
            and certify_bracket_positive(bracket_B2(k), 3, 3))
    return bool(base and step)
