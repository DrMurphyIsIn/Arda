"""Diophantine constraint on sporadic ties: a tie forces 11 | n.

The summit of Brualdi-Goldwasser is competitor extremality -- no tree other than the near-star family
reaches Phi^11 = 1.  The open danger is a SPORADIC LARGE TIE: some big tree that happens to hit the
resonance.  This module gives a rigorous 23-adic constraint that thins that danger.

THE AMPLITUDE FORM (verified vs rooted_phi.phi11_rooted for all trees n<=9, any root):

    Phi^11(rooted at r) = (64/621)^n * (prod_v a_v)^11,   a_v = 1 + z_v * S_v  (rational cavity),

so every a_v is rational (the cavity z_v = 1/deg, m_v = z_v/a_v is a rational recursion) and prod_v a_v
is a rational number.

THE CONSTRAINT.  If Phi^11 = 1 at some root (a tie), then (prod a_v)^11 = (621/64)^n.  Taking the 23-adic
valuation (v_23(621) = 1 since 621 = 3^3 * 23, v_23(64) = 0):

    11 * v_23(prod a_v) = n * v_23(621/64) = n,

and since v_23 of a rational is an integer, 11 | n.  Equivalently prod a_v = (621/64)^(n/11) exactly.

CONSEQUENCE.  A tie can occur ONLY at n in {11, 22, 33, ...}.  Combined with the exhaustive check (the
unique tie for n <= 14 is the n = 11 near-star), the sporadic-tie search is confined to n = 22, 33, 44, ...
-- an 11-fold sparser set.  The other primes give no extra divisibility: 2-adic 11 v_2 = -6n, 3-adic
11 v_3 = 3n, both integral once 11 | n, so 23 is the sole binding prime.

HONEST SCOPE.  This is a NECESSARY condition (a real reduction of the tail candidates), NOT a proof of
competitor extremality: n = 22, 33, ... remain open (they need the density / competitor bound).  The
amplitude form is verified numerically here and is the (Lean-open) input; the 11|n consequence given the
form is a clean valuation argument (padic vocabulary).  Builds on the existing 23-adic machinery in
padic.py.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .padic import padic_val_frac


def amp_product(n, edges, root=0):
    """prod_v a_v for the unloaded rooted cavity (z_v = 1/d_v, d_v = #children + 1 virtual parent;
    a_v = 1 + z_v * S_v, m_v = z_v/a_v).  Exact Fraction.  By the amplitude form,
    Phi^11(rooted at `root`) = (64/621)^n * amp_product^11 = rooted_phi.phi11_rooted(n, edges, root)."""
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    prod = [Fr(1)]

    def rec(v, parent):
        kids = [w for w in g[v] if w != parent]
        z = Fr(1, len(kids) + 1)
        S = sum((rec(w, v) for w in kids), Fr(0))
        a = 1 + z * S
        prod[0] *= a
        return z / a

    rec(root, None)
    return prod[0]


def tie_forces_divisibility(prod_a: Fr) -> int:
    """Given prod a_v of a would-be tie (so (prod a_v)^11 = (621/64)^n), return n = 11 * v_23(prod a_v),
    the ONLY n at which this prod_a could tie.  (n must then be a positive multiple of 11.)"""
    return 11 * padic_val_frac(prod_a, 23)


@dataclass(frozen=True)
class SporadicTieConstraintCertificate:
    """Certifies: (1) the amplitude form Phi^11 = (64/621)^n (prod a_v)^11 on all trees up to n_max;
    (2) the near-star tie has prod a_v = 621/64 with v_23 = 1, giving n = 11; (3) the 23-adic consequence
    that any tie has 11 | n, consistent with the exhaustive fact that no tie occurs at n not divisible by
    11 through n_max."""

    n_max: int = 9

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def amplitude_form_holds(self) -> bool:
        import networkx as nx

        from .rooted_phi import phi11_rooted
        for n in range(3, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                if Fr(64, 621) ** nn * amp_product(nn, e, 0) ** 11 != phi11_rooted(nn, e, 0):
                    return False
        return True

    def near_star_tie_valuation(self) -> bool:
        from .fractal_eigenvalue import near_star_edges
        nn, e = near_star_edges(5)
        pa = amp_product(nn, e, 0)
        return pa == Fr(621, 64) and padic_val_frac(pa, 23) == 1 and tie_forces_divisibility(pa) == nn

    def no_tie_off_multiples_of_11(self) -> bool:
        """Exhaustive: through n_max no tree with n not divisible by 11 is a tie (rooted bg_phi11 < 1)."""
        import networkx as nx

        from .rooted_phi import bg_phi11_fast
        for n in range(2, self.n_max + 1):
            if n % 11 == 0:
                continue
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                if bg_phi11_fast(nn, e) >= 1:
                    return False
        return True

    def check(self) -> bool:
        return (self.amplitude_form_holds()
                and self.near_star_tie_valuation()
                and self.no_tie_off_multiples_of_11())

    def lean(self) -> str:
        return (
            "-- SPORADIC-TIE CONSTRAINT: a tie forces 11 | n.  Given the amplitude form\n"
            "-- Phi^11 = (64/621)^n (prod a_v)^11 (a_v rational), Phi^11=1 => (prod a_v)^11 = (621/64)^n,\n"
            "-- so 11 * v_23(prod a_v) = n * v_23(621) = n (v_23(621)=1), hence 11 | n.\n"
            "theorem v23_621 : (¬ (23^2 ∣ (621:ℤ))) ∧ (23 ∣ (621:ℤ)) := by norm_num   -- v_23(621)=1\n"
            "-- (the 11 | n step is padicValRat.mul telescoping over the rational prod a_v; see padic.py)\n"
        )
