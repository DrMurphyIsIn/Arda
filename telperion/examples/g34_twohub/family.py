"""The G34 two-hub residual domination, Telperion-re-derived.

Origin: proof/verification/g34_residual_domination.py — the two-hub core of
the G34 residual: every defected two-hub stuck configuration is strictly
below the same-n single-hub family.  Three encodable strata here (the exact
finite sweep T4 lives in ../g34_sweep as export+fingerprint):

* **T1 receiver tails** (144): defects on the receiver, pA = 60 + x,
  pB = 1 + y — the factor bound against the defect-carrying template;
* **T2 donor full** (192): arm2/3/4 on the donor, fully symbolic hubward
  (pA = pB + x, pB = 1 + y), j ≤ budget;
* **T3a both-large donor tails** (144): leaf/arm1/arm2-high on the donor,
  pB = 30 + y, pA = pB + x;
* **T3b small-donor certificates (witness-searched)**: pB ≤ 29 concrete,
  pA = 60 + t — per-residue comparator search over (c0, m4, nleaf), the
  winning template recorded (the residue-dependent-comparator phenomenon:
  at some odd residues the load-6 hub wins, NOT the defect template).
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

x, y = sp.symbols("x y", nonnegative=True)
t = sp.Symbol("t", nonnegative=True)

V5 = sp.Rational(621, 64)
W4 = sp.Rational(513, 80)
Z15, Z14 = sp.Rational(3, 23), sp.Rational(3, 19)

DEFECTS = {"leaf": (sp.Integer(1), 2), "arm1": (sp.Rational(3, 7), 9),
           "arm2": (sp.Rational(3, 11), 13)}
DONOR_FULL = {"arm2": (sp.Rational(3, 11), 6), "arm3": (sp.Rational(1, 5), 13),
              "arm4": (sp.Rational(3, 19), 13)}
HZ = {"leaf": (sp.Integer(1), 2), "arm1": (sp.Rational(3, 7), 9),
      "arm2hi": (sp.Rational(3, 11), 13)}
VD = {"leaf": 1, "arm1": 3, "arm2hi": 5}
FDS = {"leaf": sp.Integer(1), "arm1": sp.Rational(7, 4), "arm2hi": sp.Rational(11, 4)}


def Fs(deg, c: int):
    if c == 0:
        return sp.Integer(1)
    D = deg + c
    return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)


def _template(K, jv, zD, m):
    dT = K + 1 + jv
    return V5 * (W4 / V5) ** m * (
        1 + (sp.Integer(1) / dT) * ((K + 1 - m) * Z15 + m * Z14 + jv * zD)
    )


def _tail_claims():
    out = []
    # T1 receiver tails
    pB, pA = 1 + y, 60 + x
    K = pA + pB
    for name, (zD, jmax) in DEFECTS.items():
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dA = pA + jv + 1
                zA = sp.Integer(3) / (3 * dA + 4 * cA)
                zB = sp.Integer(1) / (pB + 1)
                clean = Fs(dA, cA) * ((1 + zA * pA * Z15) * (1 + zB * pB * Z15) + zA * zB)
                bound = clean * (1 + zA * jv * zD)
                out.append((f"twohub_T1_{name}_j{jv}_cA{cA}",
                            _template(K, jv, zD, m) - bound))
    # T2 donor full
    pB, pA = 1 + y, (1 + y) + x
    K = pA + pB
    for name, (zD, jmax) in DONOR_FULL.items():
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dB = pB + jv + 1
                zA = sp.Integer(3) / (3 * (pA + 1) + 4 * cA)
                zB = sp.Integer(3) / (3 * dB)
                config = Fs(pA + 1, cA) * (
                    (1 + zA * pA * Z15) * (1 + zB * (pB * Z15 + jv * zD)) + zA * zB
                )
                out.append((f"twohub_T2_{name}_j{jv}_cA{cA}",
                            _template(K, jv, zD, m) - config))
    # T3a both-large donor tails
    pB, pA = 30 + y, (30 + y) + x
    K = pA + pB
    for name, (zD, jmax) in HZ.items():
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dB = pB + jv + 1
                zA = sp.Integer(3) / (3 * (pA + 1) + 4 * cA)
                zB = sp.Integer(3) / (3 * dB)
                clean = Fs(pA + 1, cA) * ((1 + zA * pA * Z15) * (1 + zB * pB * Z15) + zA * zB)
                bound = clean * (1 + zB * jv * zD)
                out.append((f"twohub_T3a_{name}_j{jv}_cA{cA}",
                            _template(K, jv, zD, m) - bound))
    return out


_TAILS = None


def tail_claims():
    global _TAILS
    if _TAILS is None:
        _TAILS = _tail_claims()
    return _TAILS


def tails_family() -> InequalityFamily:
    cs = tail_claims()
    return InequalityFamily(
        name="TwoHubTails",
        symbols=(x, y),
        grid=GridSpec([("i", list(range(len(cs))))]),
        lean_name=lambda pt: cs[pt["i"]][0],
        target=lambda pt: cs[pt["i"]][1],
    )


# ---- T3b: small-donor witness-searched certificates --------------------------


def _smalldonor_cells():
    cells = []
    for name, (zD, jmax) in HZ.items():
        for pBv in range(1, 30):
            for jv in range(1, jmax + 1):
                for cA in range(6):
                    cells.append((name, pBv, jv, cA))
    return cells


def _smalldonor_candidates(cell):
    name, pBv, jv, cA = cell
    zD, _ = HZ[name]
    vD, FD = VD[name], FDS[name]
    pA1 = 60 + t
    dB = pBv + jv + 1
    zA = sp.Integer(3) / (3 * (pA1 + 1) + 4 * cA)
    zB = sp.Rational(1, dB)
    cfg = (Fs(pA1 + 1, cA) * FD**jv * V5**pBv
           * ((1 + zA * pA1 * Z15) * (1 + zB * (pBv * Z15 + jv * zD)) + zA * zB))
    n_const = 2 + 2 * cA + 11 * pBv + vD * jv
    out = []
    for c0 in range(0, 7):
        for m4 in range(0, 11):
            for nleaf in (0, 1):
                rem = n_const - 1 - 2 * c0 + 2 * m4 - nleaf
                if rem % 11:
                    continue
                Kc = rem // 11
                K = pA1 + Kc
                dT = K + nleaf
                zT = sp.Integer(3) / (3 * dT + 4 * c0)
                sig = (K - m4) * Z15 + m4 * Z14 + nleaf
                tmpl = Fs(dT, c0) * (W4 / V5) ** m4 * V5**Kc * (1 + zT * sig)
                out.append((f"c{c0}_m{m4}_l{nleaf}", tmpl - cfg))
    return out


def smalldonor_family() -> InequalityFamily:
    cells = _smalldonor_cells()
    return InequalityFamily(
        name="TwoHubSmallDonor",
        symbols=(t,),
        grid=GridSpec([("i", list(range(len(cells))))]),
        lean_name=lambda pt: (
            lambda c: f"twohub_T3b_{c[0]}_pB{c[1]}_j{c[2]}_cA{c[3]}"
        )(cells[pt["i"]]),
        witnesses=lambda pt: _smalldonor_candidates(cells[pt["i"]]),
        witnesses_complete=True,
    )


def profile() -> LeanProfile:
    return LeanProfile(namespace=("G34", "TwoHub"))


def validation() -> ValidationReport:
    """Dual-engine spots: exact-Fraction evaluation of sampled tail claims at
    rational offsets, plus small-donor existential spot checks."""
    import random

    rng = random.Random(34)

    def tails_spot():
        for name, expr in rng.sample(tail_claims(), 40):
            for _ in range(3):
                sub = {x: sp.Rational(rng.randint(0, 200), rng.randint(1, 8)),
                       y: sp.Rational(rng.randint(0, 200), rng.randint(1, 8))}
                assert expr.subs(sub) >= 0, (name, sub)

    def smalldonor_spot():
        cells = _smalldonor_cells()
        for cell in rng.sample(cells, 25):
            cands = _smalldonor_candidates(cell)
            tt = sp.Rational(rng.randint(0, 100), rng.randint(1, 4))
            assert any(e.subs(t, tt) >= 0 for _, e in cands), cell

    return ValidationReport.from_asserts(
        [("twohub_tails_spot", tails_spot), ("smalldonor_spot", smalldonor_spot)]
    )
