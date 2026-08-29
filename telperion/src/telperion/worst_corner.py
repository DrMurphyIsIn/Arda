"""General worst-corner positivity emitter: certify P(g) > 0 over a positive box
[lo_i, hi_i], in-kernel, for ANY polynomial P in g0..gm with positive variables.

This is the abstraction the bespoke turan/jensen/toeplitz bridges are instances of.
Every monomial c * prod g_i^{e_i} (all g_i >= 0) is bounded at the WORST CORNER:
positive-coefficient monomials at the enclosure floor (prod lo_i^{e_i}), negative
ones at the ceiling (prod hi_i^{e_i}), each via a `mul_le_mul` product-monotonicity
chain.  If the resulting worst-corner sum is > 0, `nlinarith` assembles the (linear)
certificate.  Verified tractable to degree 6 / 16 monomials (the quartic Jensen
discriminant compiled in 14s).

To prove P < 0, pass -P.  The generator is untrusted; the Lean kernel is the arbiter.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp


def _rat(f: Fr) -> str:
    f = Fr(f)
    return f"({f.numerator} : ℝ)" if f.denominator == 1 else f"(({f.numerator} : ℝ) / {f.denominator})"


def _factors(mono) -> list[int]:
    fs: list[int] = []
    for s, p in mono.as_powers_dict().items():
        fs += [int(str(s)[1:])] * int(p)   # symbol 'g3' -> index 3
    return sorted(fs)


def _chain(fs: list[int], lower: bool) -> str:
    """mul_le_mul fold proving  prod lo <= prod g  (lower) or  prod g <= prod hi."""
    if lower:
        acc, gnn = f"a{fs[0]}", f"n{fs[0]}"
        for f in fs[1:]:
            acc = f"(mul_le_mul {acc} a{f} (by norm_num) {gnn})"
            gnn = f"(mul_nonneg {gnn} n{f})"
    else:
        acc, hnn = f"b{fs[0]}", f"(le_trans n{fs[0]} b{fs[0]})"
        for f in fs[1:]:
            acc = f"(mul_le_mul {acc} b{f} n{f} {hnn})"
            hnn = f"(mul_nonneg {hnn} (le_trans n{f} b{f}))"
    return acc


@dataclass
class WorstCornerCertificate:
    """Prove `poly > 0` over the positive box `enclosures[i] = (lo_i, hi_i)` for the
    variables g0..gm appearing in `poly` (a sympy expression). `enclosures` indexes
    by variable subscript."""

    name: str
    poly: object                      # sympy expr in g0..gm
    enclosures: tuple                 # ((lo0,hi0), (lo1,hi1), ...)
    max_heartbeats: int = 400000

    def _enc(self):
        return [(Fr(lo), Fr(hi)) for (lo, hi) in self.enclosures]

    def _terms(self):
        return sp.expand(self.poly).as_ordered_terms()

    def _vars(self) -> list[int]:
        return sorted(int(str(s)[1:]) for s in sp.expand(self.poly).free_symbols)

    def worst_corner_lo(self) -> Fr:
        e = self._enc()
        tot = Fr(0)
        for t in self._terms():
            cf, mono = t.as_coeff_Mul()
            cf = Fr(sp.Rational(cf))
            prod = cf
            for f in _factors(mono):
                lo, hi = e[f]
                prod *= (lo if cf > 0 else hi)
            tot += prod
        return tot

    def check(self) -> bool:
        e = self._enc()
        if any(not (0 <= lo <= hi) for lo, hi in e):
            return False
        return self.worst_corner_lo() > 0

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: worst-corner bound not positive -- refusing to emit")
        e = self._enc()
        vs = self._vars()
        hyps = " ".join(
            f"(a{i} : {_rat(e[i][0])} ≤ g{i}) (b{i} : g{i} ≤ {_rat(e[i][1])})" for i in vs)
        binders = " ".join(f"g{i}" for i in vs)
        nlines = "".join(
            f"  have n{i} : (0 : ℝ) ≤ g{i} := le_trans (by norm_num) a{i}\n" for i in vs)
        mlines, goal_terms, hints = [], [], []
        for j, t in enumerate(self._terms()):
            cf, mono = t.as_coeff_Mul()
            cf = Fr(sp.Rational(cf))
            fs = _factors(mono)
            gp = "*".join(f"g{f}" for f in fs)
            if cf > 0:
                lp = "*".join(f"({_rat(e[f][0])})" for f in fs)
                mlines.append(f"  have M{j} : {lp} ≤ {gp} := {_chain(fs, True)}\n")
            else:
                hp = "*".join(f"({_rat(e[f][1])})" for f in fs)
                mlines.append(f"  have M{j} : {gp} ≤ {hp} := {_chain(fs, False)}\n")
            sign = "+" if cf > 0 else "-"
            goal_terms.append(f"{sign} {_rat(abs(cf))}*{gp}")
            hints.append(f"M{j}")
        goal = " ".join(goal_terms).lstrip("+ ")
        return (
            f"set_option maxHeartbeats {self.max_heartbeats} in\n"
            f"theorem {self.name} {{{binders} : ℝ}} {hyps} :\n"
            f"    0 < {goal} := by\n"
            f"{nlines}{''.join(mlines)}"
            f"  nlinarith [{', '.join(hints)}]\n"
        )
