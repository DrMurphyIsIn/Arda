"""Nonnegative cosine (trigonometric) polynomials -- the certificate family behind the
classical zero-free region of the Riemann zeta function.

`P(theta) = sum_{k<=d} a_k cos(k theta) >= 0` for all theta iff, with `x = cos theta in [-1,1]`
and `cos(k theta) = T_k(x)` (Chebyshev), the polynomial `p(x) = sum a_k T_k(x) >= 0` on
`[-1,1]`.  By Markov-Lukacs every such p is a MANIFESTLY nonnegative product

    p(x) = C * (1 + x)^a * (1 - x)^b * prod_i Q_i(x),   C > 0,

with each `Q_i` a perfect square `(linear)^2` or a positive-definite quadratic
`(2u x + v)^2 + w`, `w >= 0`.  The emitter rewrites `cos(k theta) -> T_k(cos theta)` via
`Real.cos_two_mul` / `Real.cos_three_mul`, proves `P(theta) = <factored form>` by `ring`, and
closes `0 <= <factored form>` by a `mul_nonneg` fold (boundary factors from
`-1 <= cos theta <= 1`, quadratics by `positivity`).

Mertens `3 + 4cos + cos2 = 2(1+cos)^2` is the seed (classical zero-free region
`zeta(s) != 0` for `Re > 1 - c/log|t|`); higher-degree nonnegative cosine polynomials give
BETTER constants c (arXiv:1410.3926).  Certificate ON the zero-free-region line -- it proves
NOTHING about RH; the analytic assembly (zeta growth bounds) that converts it into a region is a
separate medium-high piece (ZETA_FOUNDATION_SCOPE.md).  conjecture1_proved = False.

Scope: degree d <= 3 (the `cos_two_mul`/`cos_three_mul` range).  Higher degree needs the general
`Polynomial.Chebyshev.T_real_cos` expansion.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

_X = sp.Symbol("x", real=True)


def _ratlean(q) -> str:
    q = sp.Rational(q)
    return f"({q.p} : ℝ)" if q.q == 1 else f"(({q.p} : ℝ) / {q.q})"


def power_poly(coeffs):
    """p(x) = sum_k a_k T_k(x)  (x = cos theta)."""
    return sp.expand(sum(sp.Rational(c) * sp.chebyshevt(k, _X) for k, c in enumerate(coeffs)))


def _lean_linear(e) -> str:
    """Render a linear sympy poly u*x + v as Lean `u * Real.cos θ + v` (x -> cos θ)."""
    p = sp.Poly(e, _X)
    u = sp.Rational(p.coeff_monomial(_X))
    v = sp.Rational(p.coeff_monomial(1))
    ut = "Real.cos θ" if u == 1 else f"{_ratlean(u)} * Real.cos θ"
    if v == 0:
        return ut
    return f"{ut} + {_ratlean(v)}" if v > 0 else f"{ut} - {_ratlean(-v)}"


def _lean_of_poly(e) -> str:
    """Render a sympy polynomial in x as a Lean ℝ expression with x -> Real.cos θ."""
    e = sp.expand(e)
    terms = []
    poly = sp.Poly(e, _X)
    for (k,), coeff in sorted(poly.terms(), key=lambda t: -t[0][0]):
        coeff = sp.Rational(coeff)
        cs = _ratlean(abs(coeff))
        mono = "1" if k == 0 else "Real.cos θ" if k == 1 else f"Real.cos θ ^ {k}"
        piece = cs if k == 0 else (mono if abs(coeff) == 1 else f"{cs} * {mono}")
        terms.append(("-" if coeff < 0 else "+", piece))
    if not terms:
        return "0"
    out = ("-" + terms[0][1]) if terms[0][0] == "-" else terms[0][1]
    for sign, piece in terms[1:]:
        out += f" {sign} {piece}"
    return out


@dataclass
class TrigNonnegCertificate:
    """Certifies  0 <= sum_k coeffs[k] * cos(k*theta)  via the Markov-Lukacs manifest
    factorization of p(x)=sum a_k T_k(x) on x=cos theta in [-1,1]. Degree <= 3."""

    name: str
    coeffs: tuple

    def degree(self) -> int:
        d = len(self.coeffs) - 1
        while d > 0 and self.coeffs[d] == 0:
            d -= 1
        return d

    def _factors(self):
        """Ordered manifest factors of p(x): list of (lean_str, nonneg_proof, sympy_expr).
        Product (as sympy) equals p(x); each factor is manifestly >= 0."""
        p = power_poly(self.coeffs)
        rts = sp.roots(sp.Poly(p, _X))
        a = int(rts.get(sp.Integer(-1), 0))
        b = int(rts.get(sp.Integer(1), 0))
        q = sp.expand(sp.cancel(p / ((_X + 1) ** a * (1 - _X) ** b)))
        C, sos = self._sos(q)
        factors = []
        if C != 1:
            factors.append((_ratlean(C), f"(by norm_num : (0:ℝ) ≤ {_ratlean(C)})", sp.Rational(C)))
        factors += [(f"(1 + Real.cos θ)", "h1", 1 + _X)] * a
        factors += [(f"(1 - Real.cos θ)", "h1'", 1 - _X)] * b
        factors += sos                            # each: (lean_str, proof_str, check_expr)
        return factors, a, b

    def _sos(self, q):
        """q(x) >= 0 on R -> (positive constant C, list of (lean_str, proof, check_expr)) where
        each lean_str is a MANIFEST square `(lin)^2` or completed square `A*(lin)^2 + w`."""
        q = sp.expand(q)
        C = sp.Integer(1)
        sos = []
        cont, facs = sp.factor_list(q)
        C = sp.Rational(cont)
        for base, mult in facs:
            bpol = sp.Poly(base, _X)
            bd = bpol.degree()
            if bd == 1 and mult % 2 == 0:
                lin = base ** (mult // 2)
                ls = _lean_linear(sp.expand(lin))
                sos.append((f"({ls}) ^ 2", f"(sq_nonneg ({ls}))", sp.expand(lin ** 2)))
            elif bd == 2 and sp.discriminant(bpol) < 0:
                A, B, Cc = (sp.Rational(bpol.coeff_monomial(_X ** i)) for i in (2, 1, 0))
                lin = _X + B / (2 * A)
                w = Cc - B ** 2 / (4 * A)
                ls = _lean_linear(sp.expand(lin))
                le = f"{_ratlean(A)} * ({ls}) ^ 2 + {_ratlean(w)}"
                proof = f"(by positivity : (0:ℝ) ≤ {le})"
                for _ in range(mult):
                    sos.append((f"({le})", proof, sp.expand(A * lin ** 2 + w)))
            elif bd == 0:
                C *= sp.Rational(base) ** mult
            else:
                raise ValueError(f"{self.name}: factor {base}^{mult} not manifestly nonneg")
        return C, sos

    def check(self) -> bool:
        if self.degree() > 3 or self.degree() < 1:
            return False
        p = power_poly(self.coeffs)
        f = sp.lambdify(_X, p, "mpmath")
        import mpmath as mp
        if any(f(mp.mpf(-1) + mp.mpf(2) * i / 400) < -1e-12 for i in range(401)):
            return False
        try:
            prod, _, _ = self._factors()[0], None, None
            fs, _, _ = self._factors()
            got = sp.Integer(1)
            for _, _, e in fs:
                got *= e
            return sp.expand(got - p) == 0
        except Exception:
            return False

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: not a certifiable nonneg cosine poly (deg 1..3) -- refusing to emit")
        d = self.degree()
        fs, a, b = self._factors()
        lhs_terms = []
        for k, ak in enumerate(self.coeffs):
            if ak == 0:
                continue
            if k == 0:
                lhs_terms.append(_ratlean(ak))
            else:
                arg = "θ" if k == 1 else f"({k} * θ)"
                coeff = "" if ak == 1 else f"{_ratlean(ak)} * "
                lhs_terms.append(f"{coeff}Real.cos {arg}")
        lhs = " + ".join(lhs_terms)
        form = " * ".join(fac[0] for fac in fs)
        # left-nested mul_nonneg proof term matching  f0 * f1 * f2 * ...
        proof = fs[0][1]
        for fac in fs[1:]:
            proof = f"(mul_nonneg {proof} {fac[1]})"
        rw = ("rw [Real.cos_two_mul, Real.cos_three_mul]" if d >= 3 else
              "rw [Real.cos_two_mul]" if d == 2 else "skip")
        return (
            f"/-- Nonnegative cosine polynomial (zero-free-region certificate family):\n"
            f"    0 <= {lhs}.  Markov-Lukacs manifest form on x = cos θ. Proves nothing about RH. -/\n"
            f"theorem {self.name} (θ : ℝ) : 0 ≤ {lhs} := by\n"
            f"  have h1 : (0:ℝ) ≤ 1 + Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]\n"
            f"  have h1' : (0:ℝ) ≤ 1 - Real.cos θ := by nlinarith [Real.cos_le_one θ]\n"
            f"  have key : {lhs} = {form} := by {rw}; ring\n"
            f"  rw [key]\n"
            f"  exact {proof}\n"
        )
