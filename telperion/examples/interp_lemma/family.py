"""The interpolation lemma, Telperion-re-derived — with two UPGRADES and one
honest routing.

Origin: proof/verification/interpolation_lemma.py.  Three strata here:

* **I1, upgraded to symbolic**: the exact sub-hub curve.  The origin checks
  ``cav_q = 23/(26q+23)`` and ``subOpen = 26/(23+3·cav)`` for q = 1..199;
  this family proves both as SYMBOLIC identities in q = 1 + y (y >= 0) — the
  infinite statement, not 199 instances of it.

* **I2, symbolic**: the sign polynomial — ``-3(1+z(c+T)) + z(23+3c)
  = 23z - 3 - 3Tz`` — the identity behind the heavy/light dichotomy.

* **Light tops, exact facts**: every finite config (3dt+4cT <= 22, all
  q_i = 1) strictly below its best same-n single-hub template, the template
  found by exact maximization and recorded as the witness.

HONEST ROUTING (not encoded here): the heavy-top sup and the DELTA sweep in
the origin module are FLOAT-GUARDED (math.exp, float RHO, 2% margin); their
exact counterparts live in the G1FIX endpoint modules
(g1_endpoint_certificates) — the audit ledger routes that stratum there.
"""
from __future__ import annotations

import functools
from fractions import Fraction as Fr

import sympy as sp

from telperion import GridSpec, InequalityFamily, LeanProfile, ValidationReport

# exact ports of the origin's F/z (kelmans_mixed_load.F_of / z_of)


def z_of(d: int | Fr, c: int) -> Fr:
    return Fr(3) / (3 * d + 4 * c)


def F_of(d: int | Fr, c: int) -> Fr:
    if c == 0:
        return Fr(1)
    D = d + c
    return Fr(3, 2) ** c + Fr(c) / (2 * D) * Fr(3, 2) ** (c - 1)


Z15 = z_of(1, 5)
DEFECTS = {"none": (0, Fr(0), Fr(1), (0, 0)),
           "leaf": (1, Fr(1), Fr(1), (1, 2)),
           "arm1": (3, Fr(3, 7), Fr(7, 4), (1, 9)),
           "arm2": (5, Fr(3, 11), Fr(11, 4), (1, 13))}

y = sp.Symbol("y", nonnegative=True)
c, z, T = sp.symbols("c z T", nonnegative=True)


# ---- I1 (symbolic in q = 1 + y) + I2 ----------------------------------------


def i1_family() -> InequalityFamily:
    q = 1 + y
    zi = sp.Integer(3) / (3 * (q + 1))          # z_of(q+1, 0), q symbolic
    sub_open = 1 + zi * q * sp.Rational(Z15)
    cav = zi / sub_open

    def equation(pt):
        if pt["i"] == 0:
            return (cav, sp.Integer(23) / (26 * q + 23))
        return (sub_open, sp.Integer(26) / (23 + 3 * cav))

    return InequalityFamily(
        name="InterpI1",
        symbols=(y,),
        grid=GridSpec([("i", [0, 1])]),
        lean_name=lambda pt: ("interp_I1_cavity" if pt["i"] == 0
                              else "interp_I1_subopen"),
        equation=equation,
    )


def i2_family() -> InequalityFamily:
    return InequalityFamily(
        name="InterpI2",
        symbols=(c, z, T),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "interp_I2_sign_poly",
        equation=lambda pt: (
            -3 * (1 + z * (c + T)) + z * (23 + 3 * c),
            23 * z - 3 - 3 * T * z,
        ),
    )


# ---- light tops (exact finite facts with template witnesses) -----------------


@functools.lru_cache(maxsize=None)
def best_template(n: int) -> tuple[Fr, tuple]:
    """Exact maximization over the single-hub template space (origin
    verify_delta.best_template, with the winner recorded)."""
    best, winner = None, None
    for c0 in range(0, 7):
        for nleaf in (0, 1, 2):
            rem = n - 1 - 2 * c0 - nleaf
            if rem <= 0:
                continue
            for K in range(max(1, rem // 13), rem // 9 + 2):
                t2 = rem - K
                if t2 < 0 or t2 % 2:
                    continue
                tot = t2 // 2
                if tot > 8 * K:
                    continue
                b, r = divmod(tot, K)
                loads = [b + 1] * r + [b] * (K - r)
                zh = z_of(K + nleaf, c0)
                p = F_of(K + nleaf, c0)
                s = Fr(0)
                for cl in loads:
                    p *= F_of(1, cl)
                    s += z_of(1, cl)
                s += nleaf
                p *= 1 + zh * s
                if best is None or p > best:
                    best, winner = p, (c0, nleaf, K)
    return best, winner


def _light_configs():
    out = []
    for cT in range(6):
        for name, (vD, zD, FD, jr) in DEFECTS.items():
            for j in range(jr[0], jr[1] + 1):
                for S in range(2, 8):
                    for pT in range(0, 8):
                        dt = pT + j + S
                        if 3 * dt + 4 * cT > 22:
                            continue
                        zt = z_of(dt, cT)
                        zi = z_of(2, 0)
                        so = 1 + zi * Z15
                        cfg = (F_of(dt, cT) * FD**j * F_of(1, 5) ** (pT + S)
                               * F_of(2, 0) ** S * so**S
                               * (1 + zt * (pT * Z15 + j * zD + S * zi / so)))
                        n = 1 + 2 * cT + 11 * pT + j * vD + S * 12
                        best, winner = best_template(n)
                        out.append(
                            (f"interp_light_cT{cT}_{name}_j{j}_S{S}_p{pT}",
                             cfg, n, best, winner)
                        )
    return out


_LIGHT = None


def light_configs():
    global _LIGHT
    if _LIGHT is None:
        _LIGHT = _light_configs()
    return _LIGHT


def light_family() -> InequalityFamily:
    cs = light_configs()
    return InequalityFamily(
        name="InterpLightTop",
        symbols=(),
        grid=GridSpec([("i", list(range(len(cs))))]),
        lean_name=lambda pt: cs[pt["i"]][0],
        target=lambda pt: sp.Rational(cs[pt["i"]][3] - cs[pt["i"]][1]),
    )


def light_spelling(pt):
    name, cfg, n, best, winner = light_configs()[pt["i"]]
    return (sp.Rational(cfg), "<", sp.Rational(best))


def witness_table() -> dict:
    """config name -> the winning template (c0, nleaf, K) — the audit's record
    of WHICH single-hub template dominates each light-top config."""
    return {name: winner for name, _, _, _, winner in light_configs()}


def profile() -> LeanProfile:
    return LeanProfile(namespace=("Interp",))


def validation() -> ValidationReport:
    """Dual-engine: I1 at integer points against the origin's Fraction path;
    light-top count and strictness re-asserted."""

    def i1_points():
        q_sym = 1 + y
        for q in range(1, 60):
            zi = z_of(q + 1, 0)
            sub_open = 1 + zi * q * Z15
            assert zi / sub_open == Fr(23, 26 * q + 23)
            fam = i1_family()
            lhs, rhs = fam.equation({"i": 0})
            val = (lhs - rhs).subs(y, q - 1)
            assert sp.simplify(val) == 0, q

    def light_strict():
        cs = light_configs()
        assert len(cs) >= 200, len(cs)
        for name, cfg, n, best, winner in cs:
            assert best > cfg, name

    return ValidationReport.from_asserts(
        [("I1_integer_points", i1_points), ("light_top_strict", light_strict)]
    )
