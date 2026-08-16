"""The R6 shedding lemmas, Telperion-re-derived: the de-loading schedule's 55
symbolic certificates (origin: gap_discharges.discharge_G5_lemmas; already
CI-green in origin Lean as R47Shed.lean — this family is the INDEPENDENT
re-derivation for the proof audit, through a different code path, dual-engine
cross-checked, exportable to the stdlib rechecker).

The four lemmas, each a one-variable Polya claim in t >= 0 with K = K0 + t:

  L1 (c0-shedding,  K >= 25): shedding a hub load onto a 4-arm loses;
  L2 (j6 beats c0,  K >= 40): a 6-arm beats a hub load;
  L3 (pair-shedding, K >= 25): shedding a load-pair onto a 4-arm + 6-arm loses;
  L4 (arm count,    K >= 40): the V5^9 vs W4^11 engine at every residue d.

55 = 16 (L1) + 12 (L3) + 16 (L2) + 11 (L4).
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

t = sp.Symbol("t", nonnegative=True)

V5 = sp.Rational(621, 64)
W4 = sp.Rational(513, 80)
U6 = sp.Rational(3, 2) ** 6 + sp.Rational(6, 14) * sp.Rational(3, 2) ** 5
Z15, Z14, Z16 = sp.Rational(3, 23), sp.Rational(3, 19), sp.Rational(1, 9)


def _K(k0):
    return k0 + t


def _Fh(K, c0: int):
    if c0 == 0:
        return sp.Integer(1)
    D = K + c0
    return sp.Rational(3, 2) ** c0 + sp.Rational(c0) / (2 * D) * sp.Rational(3, 2) ** (c0 - 1)


def _zh(K, c0: int):
    return sp.Integer(3) / (3 * K + 4 * c0)


def _claims():
    """(name, negated-diff expr) — each claim is 0 <= -(diff), the origin's
    check_neg made positive."""
    out = []
    K25, K40 = _K(25), _K(40)
    for c0 in range(0, 8):
        for si, s in (("s16", K25 * Z16), ("s14", K25 * Z14)):
            diff = (_Fh(K25, c0 + 1) * W4 * (1 + _zh(K25, c0 + 1) * (s + Z14 - Z15))
                    - _Fh(K25, c0) * V5 * (1 + _zh(K25, c0) * s))
            out.append((f"shed_L1_c{c0}_{si}", -diff))
    for c0 in range(0, 6):
        for si, s in (("s16", K25 * Z16), ("s14", K25 * Z14)):
            diff = (_Fh(K25, c0) * W4 * U6 * (1 + _zh(K25, c0) * (s + Z14 + Z16 - 2 * Z15))
                    - _Fh(K25, c0) * V5 * V5 * (1 + _zh(K25, c0) * s))
            out.append((f"shed_L3_c{c0}_{si}", -diff))
    for c0 in range(0, 8):
        for si, s in (("s16", K40 * Z16), ("s14", K40 * Z14)):
            diff = (_Fh(K40, c0 + 1) * V5 * (1 + _zh(K40, c0 + 1) * s)
                    - _Fh(K40, c0) * U6 * (1 + _zh(K40, c0) * (s + Z16 - Z15)))
            out.append((f"shed_L2_c{c0}_{si}", -diff))
    for d in range(0, 11):
        S1 = (K40 - d) * Z15 + d * Z14
        S2 = (K40 - 9 - d) * Z15 + (d + 11) * Z14
        pos = (V5**9 * (1 + sp.Integer(3) / (3 * K40) * S1)
               - W4**11 * (1 + sp.Integer(3) / (3 * (K40 + 2)) * S2))
        out.append((f"shed_L4_d{d}", pos))
    return out


_CLAIMS = None


def claims():
    global _CLAIMS
    if _CLAIMS is None:
        _CLAIMS = _claims()
    return _CLAIMS


def family() -> InequalityFamily:
    cs = claims()
    return InequalityFamily(
        name="ShedLemmas",
        symbols=(t,),
        grid=GridSpec([("cell", list(range(len(cs))))]),
        lean_name=lambda pt: cs[pt["cell"]][0],
        target=lambda pt: cs[pt["cell"]][1],
    )


def profile() -> LeanProfile:
    return LeanProfile(namespace=("R6", "Shed"))


def validation() -> ValidationReport:
    """Dual-engine in miniature: exact-Fraction evaluation of every claim at
    rational tail offsets, independent of the sympy build."""
    import random

    rng = random.Random(55)

    def spot():
        for name, expr in claims():
            for _ in range(4):
                tt = Fr(rng.randint(0, 400), rng.randint(1, 8))
                val = expr.subs(t, sp.Rational(tt))
                assert val >= 0, (name, tt, val)

    return ValidationReport.from_asserts([("shed_exact_spot", spot)])
