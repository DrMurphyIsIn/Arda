"""HypStarSymbolic, as a Telperion family: the R7' assembly's star-of-hubs
domination certificates — Telperion's first production use on mathematics it
did not inherit as a case study.

The Brualdi-Goldwasser campaign's R7' capstone consumes eight named
hypotheses; HypStarSymbolic is the depth-2 multi-hub discharge: every
defected star-of-hubs stuck configuration (top-defected or subs-defected) is
strictly dominated by a same-n single-hub comparator, for ALL arm counts
pT >= 0 and sub-hub sizes q >= 1 — 972 symbolic certificates in
(x, y) = (pT, q - 1), each an all-nonneg-witness rational inequality
(origin: proof/verification/g34_multi_starofhubs.py, certify_symbolic).

The per-residue comparator (c0, m4, nleaf) — the winning template varies with
n mod 11 — is data of the family, found once per cell by the same Polya test
the certifier applies and cached.  The claim per cell:

    0 <= comparator_template(x, y) - star_config(x, y).

conjecture1_proved = False; this family discharges ONE hypothesis of the
honest-conditional assembly, at Lean rigor once compiled.
"""
from __future__ import annotations

from fractions import Fraction

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

x, y = sp.symbols("x y", nonnegative=True)

V5 = sp.Rational(621, 64)
W4 = sp.Rational(513, 80)
Z15 = sp.Rational(3, 23)
Z14 = sp.Rational(3, 19)
DEFECTS = {"leaf": (0, 2), "arm1": (1, 9), "arm2": (2, 13)}  # load, jmax (top variant)


def Fs(deg, c: int):
    if c == 0:
        return sp.Integer(1)
    D = deg + c
    return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)


def zs(deg, c: int):
    return sp.Integer(3) / (3 * deg + 4 * c)


def _cells():
    cells = []
    for variant in ("top", "subs"):
        for S in range(2, 11):
            for cT in range(6):
                for cB in (0, 5):
                    for dname, (dload, jmax) in DEFECTS.items():
                        js = [1, jmax] if variant == "top" else [None]
                        for j in js:
                            cells.append(
                                {"variant": variant, "S": S, "cT": cT, "cB": cB,
                                 "defect": dname, "j": j if j is not None else -1}
                            )
    return cells


def _config_and_nconst(pt):
    """The star-of-hubs closed form (normalized by V5^(arm count)) and its
    n-offset — verbatim mathematics from the origin module."""
    variant, S, cT, cB = pt["variant"], pt["S"], pt["cT"], pt["cB"]
    dload, _ = DEFECTS[pt["defect"]]
    j = pt["j"]
    zDl, FDl = zs(1, dload), Fs(1, dload)
    pT, q = x, 1 + y
    if variant == "top":
        dt = pT + j + S
        zt = zs(dt, cT)
        zi = zs(q + 1, cB)
        sub_open = 1 + zi * q * Z15
        cfg = (
            Fs(dt, cT) * FDl**j * Fs(q + 1, cB) ** S * sub_open**S
            * (1 + zt * (pT * Z15 + j * zDl + S * zi / sub_open))
        )
        n_const = 1 + 2 * cT + j * (1 + 2 * dload) + S * (1 + 2 * cB)
    else:
        dt = pT + S
        zt = zs(dt, cT)
        zi = zs(q + 2, cB)
        sub_open = 1 + zi * (q * Z15 + zDl)
        cfg = (
            Fs(dt, cT) * FDl**S * Fs(q + 2, cB) ** S * sub_open**S
            * (1 + zt * (pT * Z15 + S * zi / sub_open))
        )
        n_const = 1 + 2 * cT + S * (1 + 2 * cB) + S * (1 + 2 * dload)
    return cfg, n_const


def _template(c0: int, m4: int, nleaf: int, Kc: int, S: int):
    K = x + S * (1 + y) + Kc
    dT = K + nleaf
    zT = sp.Integer(3) / (3 * dT + 4 * c0)
    sig = (K - m4) * Z15 + m4 * Z14 + nleaf
    return Fs(dT, c0) * (W4 / V5) ** m4 * V5**Kc * (1 + zT * sig)


def candidates(pt):
    """The per-residue comparator CANDIDATE SPACE (cheap to build — no
    certification here; the certifier's witness search does that once per
    cell, in parallel).  The winning template varies with n mod 11; the
    declared space is COMPLETE for the residue system, so exhaustion would be
    a proven hard case, not a shrug."""
    cfg, n_const = _config_and_nconst(pt)
    out = []
    for c0 in range(7):
        for m4 in range(11):
            for nleaf in (0, 1):
                rem = n_const - 1 - 2 * c0 + 2 * m4 - nleaf
                if rem % 11:
                    continue
                Kc = rem // 11
                out.append(
                    (f"c{c0}_m{m4}_l{nleaf}",
                     _template(c0, m4, nleaf, Kc, pt["S"]) - cfg)
                )
    return out


def lean_name(pt):
    j = f"_j{pt['j']}" if pt["j"] >= 0 else ""
    return (
        f"star_{pt['variant']}_S{pt['S']}_cT{pt['cT']}_cB{pt['cB']}"
        f"_{pt['defect']}{j}"
    )


def family() -> InequalityFamily:
    cells = _cells()
    return InequalityFamily(
        name="R7StarOfHubs",
        symbols=(x, y),
        grid=GridSpec([("cell", list(range(len(cells))))]),
        lean_name=lambda pt: lean_name(cells[pt["cell"]]),
        witnesses=lambda pt: candidates(cells[pt["cell"]]),
        witnesses_complete=True,
    )


def profile() -> LeanProfile:
    return LeanProfile(
        namespace=("R7Hyps", "StarOfHubs"),
        options=("set_option maxHeartbeats 1600000",),
    )


# ------------------------------------------------- independent exact validation
def _frac_pow(b: Fraction, e: int) -> Fraction:
    return b**e


def _config_fraction(pt, pT: Fraction, q: Fraction) -> Fraction:
    """The closed form re-implemented in bare fractions.Fraction — an
    INDEPENDENT evaluation path (no sympy) cross-checking the symbolic build."""
    z15 = Fraction(3, 23)

    def fs(deg: Fraction, c: int) -> Fraction:
        if c == 0:
            return Fraction(1)
        return _frac_pow(Fraction(3, 2), c) + Fraction(c) / (2 * (deg + c)) * _frac_pow(
            Fraction(3, 2), c - 1
        )

    def z(deg: Fraction, c: int) -> Fraction:
        return Fraction(3) / (3 * deg + 4 * c)

    variant, S, cT, cB = pt["variant"], pt["S"], pt["cT"], pt["cB"]
    dload, _ = DEFECTS[pt["defect"]]
    j = pt["j"]
    zDl, FDl = z(Fraction(1), dload), fs(Fraction(1), dload)
    if variant == "top":
        dt = pT + j + S
        zt, zi = z(dt, cT), z(q + 1, cB)
        sub_open = 1 + zi * q * z15
        return (
            fs(dt, cT) * _frac_pow(FDl, j) * _frac_pow(fs(q + 1, cB), S)
            * _frac_pow(sub_open, S)
            * (1 + zt * (pT * z15 + j * zDl + S * zi / sub_open))
        )
    dt = pT + S
    zt, zi = z(dt, cT), z(q + 2, cB)
    sub_open = 1 + zi * (q * z15 + zDl)
    return (
        fs(dt, cT) * _frac_pow(FDl, S) * _frac_pow(fs(q + 2, cB), S)
        * _frac_pow(sub_open, S)
        * (1 + zt * (pT * z15 + S * zi / sub_open))
    )


def validation() -> ValidationReport:
    """Numeric-first, two layers: (1) the sympy config agrees EXACTLY with an
    independent fractions.Fraction implementation at rational points;
    (2) the domination claim holds exactly at sampled (pT, q)."""
    import random

    rng = random.Random(1984)
    cells = _cells()

    def cross_check():
        for pt in rng.sample(cells, 40):
            cfg, _ = _config_and_nconst(pt)
            for _ in range(3):
                pT = Fraction(rng.randint(0, 40), rng.randint(1, 4))
                q = 1 + Fraction(rng.randint(0, 40), rng.randint(1, 4))
                sym_val = cfg.subs({x: sp.Rational(pT), y: sp.Rational(q - 1)})
                frac_val = _config_fraction(pt, pT, q)
                # direct exact comparison — never nsimplify an exact Rational
                assert sym_val == sp.Rational(frac_val), (pt, pT, q)

    def domination():
        for pt in rng.sample(cells, 40):
            cands = candidates(pt)
            for _ in range(3):
                sub = {
                    x: sp.Rational(rng.randint(0, 200), rng.randint(1, 8)),
                    y: sp.Rational(rng.randint(0, 200), rng.randint(1, 8)),
                }
                # the EXISTENTIAL claim: some candidate dominates at the point
                assert any(t.subs(sub) >= 0 for _, t in cands), (pt, sub)

    return ValidationReport.from_asserts(
        [("closed_form_cross_check", cross_check), ("domination_spot", domination)]
    )
