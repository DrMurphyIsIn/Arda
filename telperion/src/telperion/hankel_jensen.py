"""Degree-n Jensen-Polya hyperbolicity via the Hermite / Hankel-minor criterion --
the UNIFORM generalization of turan (d=2), jensen (d=3) and quartic_jensen (d=4).

Background.  RH <=> every Jensen polynomial  J^{d,n}(X) = sum_j C(d,j) gamma_{n+j} X^j
(EGF sequence gamma_k = k! a_k, a_k = [z^{2k}] xi(1/2+z)) is hyperbolic (real-rooted).
For d <= 4 real-rootedness has a short discriminant criterion; for d >= 5 it does
NOT.  The correct any-degree characterization is Hermite's:

    a real degree-d polynomial is STRICTLY hyperbolic (d distinct real roots)
    iff its HERMITE FORM is positive definite,

where the Hermite form is the d x d Hankel matrix  H = [ p_{i+j} ]_{0<=i,j<d}  of
the roots' Newton power sums  p_k = sum(root^k).  By Sylvester this is  <=>  every
leading principal minor  M_r = det[p_{i+j}]_{i,j<r}  is  > 0.

The power sums are rational in the coefficients (Newton's identities), with
denominator a power of the leading coefficient a_d = gamma_{n+d}.  Writing
tau_k = a_d^k p_k (a genuine POLYNOMIAL in the gammas) and factoring the row/column
powers of a_d out of the determinant gives an INTEGER-coefficient minor

    Dtau_r := det[ tau_{i+j} ]_{0<=i,j<r}  =  a_d^{r(r-1)} * M_r ,

and since a_d = gamma_{n+d} > 0 we have  sign(Dtau_r) = sign(M_r).  So the criterion
becomes  Dtau_r > 0  for r = 2 .. d  (r=1 is Dtau_1 = p_0 = d > 0, trivial), and each
Dtau_r is a polynomial in gamma_n .. gamma_{n+d} certified over rational enclosures by
the general WorstCornerCertificate.  RH-NECESSARY, finite shifts, enclosure-conditional
-- the same honest scope and trust model as turan/jensen/quartic.

Tractability.  Dtau_r is homogeneous of degree r(r-1): d=2 -> 2, d=3 -> {2,6},
d=4 -> {2,6,12}, d=5 -> {2,6,12,20}.  The monomial count of the top minor grows fast,
so nlinarith tractability must be checked per degree (that is the point of a general
emitter -- measure the wall, don't guess it).  Use `.monomial_counts()` to inspect.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache

import sympy as sp

from .worst_corner import WorstCornerCertificate


@lru_cache(maxsize=None)
def _power_sums(d: int):
    """Newton power sums p_0 .. p_{2d-2} of the roots of J^{d,n} with a_k = C(d,k) g_k,
    returned as sympy expressions in g0..gd (denominators are powers of g_d)."""
    g = sp.symbols(f"g0:{d + 1}", positive=True)
    a = [sp.binomial(d, k) * g[k] for k in range(d + 1)]   # a_k = coeff of X^k
    ad = a[d]                                              # leading coeff = g_d
    # elementary symmetric of the roots: e_i = (-1)^i a_{d-i}/a_d
    e = {i: sp.Integer(-1) ** i * a[d - i] / ad for i in range(1, d + 1)}
    p = {0: sp.Integer(d)}
    for k in range(1, 2 * (d - 1) + 1):
        if k <= d:
            # p_k = sum_{i=1}^{k-1} (-1)^{i-1} e_i p_{k-i} + (-1)^{k-1} k e_k
            expr = sum(sp.Integer(-1) ** (i - 1) * e[i] * p[k - i] for i in range(1, k))
            expr += sp.Integer(-1) ** (k - 1) * k * e[k]
        else:
            # p_k = sum_{i=1}^{d} (-1)^{i-1} e_i p_{k-i}
            expr = sum(sp.Integer(-1) ** (i - 1) * e[i] * p[k - i] for i in range(1, d + 1))
        p[k] = sp.together(sp.expand(expr))
    return [p[k] for k in range(2 * (d - 1) + 1)]


@lru_cache(maxsize=None)
def hankel_minors(d: int):
    """Leading principal Hankel minors Dtau_r (r=2..d) as expanded polynomials in
    g0..gd.  Returns a tuple of (r, poly).  tau_k = g_d^k p_k clears denominators."""
    g = sp.symbols(f"g0:{d + 1}", positive=True)
    gd = g[d]
    p = _power_sums(d)
    tau = [sp.expand(gd ** k * p[k]) for k in range(len(p))]
    # sanity: tau_k must be a genuine polynomial (no g_d left in a denominator)
    for k, t in enumerate(tau):
        if t.as_numer_denom()[1].free_symbols:
            raise AssertionError(f"tau_{k} did not clear denominator: {t}")
    out = []
    for r in range(2, d + 1):
        M = sp.Matrix(r, r, lambda i, j: tau[i + j])
        out.append((r, sp.expand(M.det())))
    return tuple(out)


# heuristic maxHeartbeats per minor -- the degree-r(r-1) top minors are heavy
def _heartbeats(poly) -> int:
    n = len(sp.Add.make_args(poly))
    return max(400000, 200000 * (1 + n // 8))


@dataclass
class HankelJensenCertificate:
    """Strict hyperbolicity of J^{d,n} for the interior shifts of a run of rational
    gamma_k enclosures, via the Hermite/Hankel-minor criterion.  enclosures[k] =
    (lo, hi); shifts n = 0 .. len-(d+1) are certified, each as d-1 worst-corner
    theorems {name}_n{n}_H{r} proving the leading Hankel minor Dtau_r > 0."""

    name: str
    enclosures: tuple
    degree: int
    _minors: tuple = field(default=None, repr=False, compare=False)

    def __post_init__(self):
        object.__setattr__(self, "_minors", hankel_minors(self.degree))

    def certified_shifts(self):
        return list(range(0, len(self.enclosures) - self.degree))

    def monomial_counts(self):
        """{r: number of monomials in Dtau_r} -- inspect tractability before emitting."""
        return {r: len(sp.Add.make_args(m)) for r, m in self._minors}

    def _certs_for(self, n: int):
        window = tuple(self.enclosures[n + i] for i in range(self.degree + 1))
        return [
            WorstCornerCertificate(f"{self.name}_n{n}_H{r}", m, window,
                                   max_heartbeats=_heartbeats(m))
            for r, m in self._minors
        ]

    def check(self) -> bool:
        if len(self.enclosures) < self.degree + 1:
            return False
        return all(c.check() for n in self.certified_shifts() for c in self._certs_for(n))

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: Hankel-minor hyperbolicity not certified -- refusing to emit")
        blocks = []
        for n in self.certified_shifts():
            blocks.append(f"-- shift n={n}: J^{{{self.degree},{n}}} strictly hyperbolic  "
                          f"(Hermite form PD: Dtau_r > 0, r=2..{self.degree})")
            for c in self._certs_for(n):
                blocks.append(c.lean().rstrip())
        return "\n\n".join(blocks) + "\n"
