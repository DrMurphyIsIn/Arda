"""R2 double-near-star family bound via GLUING SUBMULTIPLICATIVITY -- a clean proof for a,b >= 3.

`double_near_star.py` (parallel session) identified the multi-hub extremal as the double near-star DN(a,b)
(two hubs joined, carrying a and b length-2 arms) and observed a uniform numerical gap (peak 0.852 at
DN(4,5)).  This module proves the FAMILY BOUND `Phi^11(DN(a,b)) < 1` for the dangerous region a,b >= 3 by a
clean submultiplicativity, complementing the raw 2-variable optimization.

THE IDENTITY.  Root DN(a,b) at the LARGER hub (WLOG a <= b, root = the b-arm hub; verified to be the
bg_phi11 maximizing root).  The smaller hub, as a child, presents EXACTLY as a near-star hub:
`a_small = 1 + (1/(a+1))(a/3) = (4a+3)/(3(a+1)) = a_hub(a)` -- identical to the N(0,a) hub amplitude.  Hence

    Phi^11(DN(a,b)) / (Phi^11(N(0,a)) * Phi^11(N(0,b)))  =  [ a_bigroot / a_hub(b) ]^11 ,

because the (64/621)^n and (3/2)^(arm) factors and the `a_small = a_hub(a)` factor all cancel EXACTLY.

THE CONDITION.  `a_bigroot = 1 + (1/(b+2))(b/3 + 3/(4a+3))` (big hub: degree b+1, +1 impurity, children =
b arms + the small hub with cavity 3/(4a+3)); `a_hub(b) = 1 + (1/(b+1))(b/3)`.  Then

    a_bigroot <= a_hub(b)  <=>  9(b+1) <= b(4a+3)  <=>  2b(2a-3) >= 9.

For a >= 3: `2a-3 >= 3`, so `2b(2a-3) >= 6b >= 18 >= 9` (b >= a >= 3).  Hence the submultiplicativity holds,
and

    Phi^11(DN(a,b)) <= Phi^11(N(0,a)) * Phi^11(N(0,b)) <= 1

by the PROVEN near-star tail (`near_star_tail`), STRICT unless both factors = 1 (a=b=5), and even there the
inequality a_bigroot < a_hub(b) is strict (`2b(2a-3)=50>9`), so DN(5,5) < 1.  CASE A (a,b >= 3) CLOSED.

RESIDUAL.  (B) min(a,b) <= 2: DN(1,b), DN(2,b) are one-variable families, uniformly < 1 (max 0.789 at
DN(2,4)); a near_star_tail-style one-variable bound, verified here over a range.  And the SEPARATE R2 piece
`DN is the multi-hub Phi^11-maximizer at each n` is the parallel session's (verified n <= 13).  This module
closes the FAMILY bound for a,b>=3; it is not the full multi-hub front.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .fractal_eigenvalue import near_star_edges
from .rooted_phi import bg_phi11_fast, phi11_rooted


def double_near_star(a, b):
    """DN(a,b): hubs 0 (a arms) and 1 (b arms) joined by an edge.  n = 2 + 2a + 2b.  Returns (n, edges)."""
    e = [(0, 1)]
    nid = 2
    for _ in range(a):
        e += [(0, nid), (nid, nid + 1)]
        nid += 2
    for _ in range(b):
        e += [(1, nid), (nid, nid + 1)]
        nid += 2
    return 2 + 2 * a + 2 * b, tuple(e)


def a_hub(k):
    """The N(0,k) hub amplitude (4k+3)/(3(k+1)) -- also the DN small-hub amplitude a_small."""
    return Fr(4 * k + 3, 3 * (k + 1))


def a_bigroot(a, b):
    """The DN(a,b) big-hub (b arms) root amplitude: 1 + (1/(b+2))(b/3 + 3/(4a+3))."""
    return 1 + Fr(1, b + 2) * (Fr(b, 3) + Fr(3, 4 * a + 3))


def _ns(k):
    n, e = near_star_edges(k)
    return bg_phi11_fast(n, e)


@dataclass(frozen=True)
class R2SubmultiplicativeCertificate:
    """Certifies the Case-A proof: for 3 <= a <= b, root at the big hub gives the exact ratio
    [a_bigroot/a_hub(b)]^11, submultiplicativity holds via 2b(2a-3) >= 9, hence DN(a,b) <= ns(a) ns(b) <= 1;
    plus the Case-B small-hub bound over a range."""

    hi: int = 12

    def ratio_identity(self) -> bool:
        """For a <= b, bg_phi11(DN) is at the big hub and Phi^11(DN)/(ns(a) ns(b)) = [a_bigroot/a_hub(b)]^11."""
        for a in range(1, self.hi):
            for b in range(a, self.hi):
                n, e = double_near_star(a, b)
                atbig = phi11_rooted(n, e, 1)                    # hub 1 = the b-arm (big) hub
                if bg_phi11_fast(n, e) != atbig:
                    return False
                if atbig / (_ns(a) * _ns(b)) != (a_bigroot(a, b) / a_hub(b)) ** 11:
                    return False
        return True

    def caseA_submultiplicative(self) -> bool:
        """For a,b >= 3: 2b(2a-3) >= 9 (the proof), and it certifies a_bigroot <= a_hub(b), hence
        DN(a,b) <= ns(a) ns(b)."""
        for a in range(3, self.hi):
            for b in range(a, self.hi):
                if not (2 * b * (2 * a - 3) >= 9):
                    return False
                if not (a_bigroot(a, b) <= a_hub(b)):
                    return False
                n, e = double_near_star(a, b)
                if bg_phi11_fast(n, e) > _ns(a) * _ns(b):
                    return False
        return True

    def caseB_small_hub(self) -> bool:
        """min(a,b) <= 2: DN(1,b), DN(2,b) are uniformly < 1 over the range (max 0.789 at DN(2,4))."""
        for small in (1, 2):
            for b in range(small, 4 * self.hi):
                n, e = double_near_star(small, b)
                if bg_phi11_fast(n, e) >= 1:
                    return False
        return True

    def check(self) -> bool:
        return self.ratio_identity() and self.caseA_submultiplicative() and self.caseB_small_hub()

    def lean(self) -> str:
        return (
            "-- R2 CASE A: DN(a,b) submultiplicativity for a,b >= 3.  Root at the big hub; the small hub\n"
            "-- presents as a_hub(a), so Phi^11(DN)/(ns(a) ns(b)) = (a_bigroot/a_hub(b))^11, and\n"
            "-- a_bigroot <= a_hub(b)  <=>  2b(2a-3) >= 9, which holds for a,b >= 3.\n"
            "theorem dn_submult_condition (a b : ℕ) (ha : 3 ≤ a) (hb : a ≤ b) : 9 ≤ 2*b*(2*a-3) := by\n"
            "  have : 3 ≤ 2*a-3 := by omega\n"
            "  nlinarith [ha, hb, this]\n"
            "-- Then Phi^11(DN(a,b)) <= ns(a) ns(b) <= 1 by the proven near-star tail (near_star_tail).\n"
        )
