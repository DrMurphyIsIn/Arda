"""Weil explicit-formula positivity -- the PSD certifier (WorstCorner / leading-minor
machinery) pointed at the Weil quadratic form instead of at Jensen polynomials.

RH <=> Weil's quadratic functional  W(g, g) >= 0  for all test functions g (Weil; Bombieri;
Connes).  On a FINITE test-function basis {g_1, ..., g_N} the Weil form is a symmetric Gram
matrix

    M_{jk} = W(g_j, g_k) = sum_rho  ĝ_j(gamma_rho) ĝ_k(gamma_rho),

a Gram matrix of the vectors (ĝ_j(gamma))_gamma, hence POSITIVE DEFINITE when the zeros gamma
are real -- i.e. RH.  Crucially, the entries M_{jk} are given by the explicit formula
(archimedean Gamma'/Gamma = digamma terms + a prime sum + boundary terms) and are computed
WITHOUT any knowledge of the zeros.  So `M positive-definite on a finite basis` is a
NECESSARY condition for RH that is checkable from the arithmetic/archimedean side alone.

This certificate CONSUMES rational brackets `lo_{jk} <= M_{jk} <= hi_{jk}` on the entries (the
brackets come from rigorous numerics of the digamma integral + prime sum -- the transcendental
import, exactly analogous to the a_k enclosures the turan/jensen certs consume) and proves, by
Sylvester's criterion, that every symmetric matrix in the box is positive-definite: each
leading principal minor `D_r > 0` is a polynomial in the entries, certified over the box by
the general `WorstCornerCertificate`.

HONEST SCOPE.  Finite-basis Weil positivity is a NECESSARY condition for RH (RH => M >= 0 always);
verifying it is consistent with RH, never a proof.  Same honest ceiling as Robin/Jensen -- a
new ANGLE (the natural home for a PSD/SOS certificate, and RH-EQUIVALENT via Weil's criterion),
not progress toward proving RH.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp

from .worst_corner import WorstCornerCertificate


@dataclass
class WeilPositivityCertificate:
    """Positive-definiteness of a symmetric NxN Weil-form matrix whose entries lie in given
    rational brackets, via Sylvester's leading-minor criterion + WorstCornerCertificate.
    `entries[(i, j)] = (lo, hi)` for i <= j (symmetric)."""

    name: str
    n: int
    entries: dict

    def _index(self):
        idx, c = {}, 0
        for i in range(self.n):
            for j in range(i, self.n):
                idx[(i, j)] = c
                c += 1
        return idx

    def _gvar(self, idx, i, j):
        i, j = min(i, j), max(i, j)
        return sp.Symbol(f"g{idx[(i, j)]}", positive=True)

    def _enclosures(self):
        idx = self._index()
        enc = [None] * len(idx)
        for (i, j), (lo, hi) in self.entries.items():
            enc[idx[(min(i, j), max(i, j))]] = (Fr(lo), Fr(hi))
        return tuple(enc)

    def _minors(self):
        """WorstCornerCertificate per leading principal minor D_r > 0, r = 1..n."""
        idx = self._index()
        enc = self._enclosures()
        out = []
        for r in range(1, self.n + 1):
            Msub = sp.Matrix(r, r, lambda i, j: self._gvar(idx, i, j))
            Dr = sp.expand(Msub.det())
            out.append(WorstCornerCertificate(f"{self.name}_minor{r}", Dr, enc,
                                              max_heartbeats=400000 * max(1, r - 1)))
        return out

    def check(self) -> bool:
        if any(not (0 <= Fr(lo) <= Fr(hi)) for lo, hi in self.entries.values()):
            return False
        return all(c.check() for c in self._minors())

    def lean(self) -> str:
        if not self.check():
            raise ValueError(f"{self.name}: leading-minor positivity not certified -- refusing to emit")
        blocks = [
            f"/- Weil-form positive-definiteness on a {self.n}-dim test basis, via Sylvester:\n"
            f"   every symmetric matrix with entries in the given brackets has all leading\n"
            f"   principal minors D_r > 0, hence is positive-definite.  The Weil matrix (entries\n"
            f"   from the explicit formula: digamma + prime sum) lies in the box, so the Weil form\n"
            f"   is PSD on this basis -- a NECESSARY condition for RH (never a proof). -/"
        ]
        for c in self._minors():
            blocks.append(c.lean().rstrip())
        return "\n\n".join(blocks) + "\n"
