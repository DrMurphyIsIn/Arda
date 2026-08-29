"""Degree-4 (quartic) Jensen-Polya hyperbolicity for the Riemann xi -- the d=4 rung
above turan.py (d=2) and jensen.py (d=3).

The quartic Jensen polynomial  J^{4,n}(X) = sum_j C(4,j) gamma_{n+j} X^j  (with the
EGF sequence gamma_k = k! a_k, a_k = [z^{2k}] xi(1/2+z)) has ALL FOUR roots real
(hyperbolic) iff the standard quartic criterion holds on its coefficients
(a4,b,cc,d,e) = (gamma_{n+4}, 4gamma_{n+3}, 6gamma_{n+2}, 4gamma_{n+1}, gamma_n):

    Delta4 > 0   AND   P = 8 a4 cc - 3 b^2 < 0   AND   D < 0 ,

where D = 64 a4^3 e - 16 a4^2 cc^2 + 16 a4 b^2 cc - 16 a4^2 b d - 3 b^4.  Note
P < 0  <=>  gamma_{n+3}^2 > gamma_{n+2} gamma_{n+4}  (a Turan inequality).  Each of
the three conditions is certified over rational gamma enclosures by the general
WorstCornerCertificate (Delta4 is 16 monomials of degree 6 -- verified tractable,
compiles in ~14s).  RH-NECESSARY, finite shifts, enclosure-conditional -- same
honest scope as turan/jensen.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp

from .worst_corner import WorstCornerCertificate


def _quartic_conditions():
    """(Delta4>0, P_turan>0 [= P<0], negD>0 [= D<0]) as sympy polys in g0..g4."""
    g0, g1, g2, g3, g4 = sp.symbols("g0 g1 g2 g3 g4", positive=True)
    a4, b, cc, d, e = g4, 4 * g3, 6 * g2, 4 * g1, g0
    Delta = sp.expand(
        256 * a4**3 * e**3 - 192 * a4**2 * b * d * e**2 - 128 * a4**2 * cc**2 * e**2
        + 144 * a4**2 * cc * d**2 * e - 27 * a4**2 * d**4 + 144 * a4 * b**2 * cc * e**2
        - 6 * a4 * b**2 * d**2 * e - 80 * a4 * b * cc**2 * d * e + 18 * a4 * b * cc * d**3
        + 16 * a4 * cc**4 * e - 4 * a4 * cc**3 * d**2 - 27 * b**4 * e**2
        + 18 * b**3 * cc * d * e - 4 * b**3 * d**3 - 4 * b**2 * cc**3 * e + b**2 * cc**2 * d**2)
    P_turan = g3**2 - g2 * g4                                   # P < 0  <=>  this > 0
    negD = sp.expand(-(64 * g0 * g4**3 - 576 * g2**2 * g4**2 + 1536 * g2 * g3**2 * g4
                       - 256 * g1 * g3 * g4**2 - 768 * g3**4))   # D < 0  <=>  -D > 0
    return Delta, P_turan, negD


@dataclass
class QuarticJensenCertificate:
    """Hyperbolicity of J^{4,n} for the interior shifts of a run of rational
    gamma_k = k! a_k enclosures.  enclosures[k] = (lo, hi); shifts n = 0 .. len-5
    are certified (each needs gamma_n .. gamma_{n+4}), each as three worst-corner
    theorems ({name}_n{n}_disc / _P / _D)."""

    name: str
    enclosures: tuple

    def certified_shifts(self):
        return list(range(0, len(self.enclosures) - 4))

    def _certs_for(self, n: int):
        D4, P, nD = _quartic_conditions()
        enc = tuple(self.enclosures[n + i] for i in range(5))
        return [
            WorstCornerCertificate(f"{self.name}_n{n}_disc", D4, enc, max_heartbeats=1000000),
            WorstCornerCertificate(f"{self.name}_n{n}_P", P, enc),
            WorstCornerCertificate(f"{self.name}_n{n}_D", nD, enc, max_heartbeats=800000),
        ]

    def check(self) -> bool:
        if len(self.enclosures) < 5:
            return False
        return all(c.check() for n in self.certified_shifts() for c in self._certs_for(n))

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: quartic hyperbolicity not certified -- refusing to emit")
        blocks = []
        for n in self.certified_shifts():
            blocks.append(f"-- shift n={n}: J^{{4,{n}}} hyperbolic  (Delta4 > 0  &&  P < 0  &&  D < 0)")
            for c in self._certs_for(n):
                blocks.append(c.lean().rstrip())
        return "\n\n".join(blocks) + "\n"
