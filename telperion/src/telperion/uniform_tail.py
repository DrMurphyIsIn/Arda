"""Uniform-in-recursion monotone-tail certificate -- ARM-DOMINANCE.

The dimensional lift crosses any FIXED dimension; the general crux has unbounded
type-dimension (each subtree a coordinate).  The uniform monotone-tail certificate
that would close it reduces to a single, sharp, RECURSION-UNIFORM claim:

  ARM-DOMINANCE: at every hub state, the ARM (the profile (1/3, phi_arm)) is the
  optimal added child -- Phi^11(hub + arm) >= Phi^11(hub + X) for every achievable
  child X.  (The exact marginal, INCLUDING the prod-deg penalty, not the naive
  linearization.)

If arm-dominance holds uniformly, then every non-arm direction is a monotone tail
(steeper decrease), the all-arm near-star is the extremizer at every hub, and the
near-star bridge closes it.  The crucial empirical finding: arm-dominance holds
UNIFORMLY across all hub states EXCEPT the single finite base case (cr=0, k=0, the
empty hub -- where the first child is a leaf that BUILDS an arm).  So the uniform
tail has the SAME base + tail structure as the 1-D bridge, lifted to hub-state
space: a finite base of exceptions + arm-dominance everywhere beyond.

This module certifies arm-dominance per hub state (a finite family of exact
inequalities) and checks its uniformity + base exceptions.  A COMPLETE uniform
proof needs (a) arm-dominance as one inequality UNIFORM in the hub state (an SOS
over the state parameters) and (b) a size-preserving exchange to the near-star --
the remaining open piece, now named precisely.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def _rec(cr, kids):
    ch = [_rec(*k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + cr
    z = Fr(3, 3 * d + cr)
    m = z / (1 + z * S)
    a11 = (Fr(3, 2) ** (11 * cr)) * (Fr(64, 621) ** (1 + 2 * cr))
    p = a11 * (1 + z * S) ** 11
    for _, q in ch:
        p *= q
    return (m, p)


ARM = (0, [(0, [])])
LEAF = (0, [])
CHERRY = (1, [])


def hub_phi(cr, children):
    return _rec(cr, list(children))[1]


def _default_children():
    return [ARM, LEAF, CHERRY,
            (0, [(0, [(0, [])])]),          # arm-of-arm
            (0, [(0, []), (0, [(0, [])])]),  # mixed
            (1, [(0, [(0, [])])])]           # cherry + arm


@dataclass(frozen=True)
class ArmDominanceCertificate:
    """At hub state (cr cherries, k existing arms): adding an ARM beats adding any
    other child X, i.e. Phi^11(hub + arm) >= Phi^11(hub + X) for each X."""

    name: str
    cr: int
    k: int
    children: tuple = None

    def _cands(self):
        return self.children or _default_children()

    def arm_value(self):
        return hub_phi(self.cr, [ARM] * self.k + [ARM])

    def check(self) -> bool:
        av = self.arm_value()
        return all(av >= hub_phi(self.cr, [ARM] * self.k + [X]) for X in self._cands())

    def lean(self) -> str:
        av = self.arm_value()
        lines = [
            f"-- {self.name}: ARM-DOMINANCE at hub state (cr={self.cr}, k={self.k}).\n"
            f"-- Adding an arm beats adding any other child X (exact Phi^11, with the\n"
            f"-- prod-deg penalty).  This is the recursion-uniform monotone tail: every\n"
            f"-- non-arm direction decreases Phi more, so the near-star is extremal.\n"
        ]
        for i, X in enumerate(self._cands()):
            if X == ARM:
                continue
            xv = hub_phi(self.cr, [ARM] * self.k + [X])
            # av >= xv  <=>  av.num * xv.den >= xv.num * av.den  (cross-multiplied)
            lhs = av.numerator * xv.denominator
            rhs = xv.numerator * av.denominator
            lines.append(f"theorem {self.name}_dom_{i} : "
                         f"({rhs}:ℤ) ≤ {lhs} := by norm_num")
        return "\n".join(lines) + "\n"


def arm_dominance_uniform(cr_range=range(0, 4), k_range=range(0, 8)):
    """Check arm-dominance across hub states; returns (holds_everywhere, exceptions)."""
    exceptions = []
    for cr in cr_range:
        for k in k_range:
            if not ArmDominanceCertificate("t", cr, k).check():
                exceptions.append((cr, k))
    return (not exceptions), exceptions
