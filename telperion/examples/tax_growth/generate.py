"""The source-grouped ledger pieces, certified: the {2,3,23} tax and per-node
growth bounds.

The crux Phi^11 <= 1 reframes (verified exact) as  SUM_v growth_v <= TAX, where
  const_v(cr) = (3/2)^(11cr) * (64/621)^(1+2cr)   -- pure {2,3,23}, fn of cr
  growth_v    = ((3d+cr+3S)/(3d))^11 >= 1          -- geometric, magnitude 1+(cr+3S)/3d
  TAX = -log prod const_v = (per-node 2.2724)*nodes + (per-cherry 0.0848)*cherries.

The telescoping CLOSURE (SUM growth <= TAX) is the open wall -- no finite/closed
potential.  But the PIECES are finitely certifiable, and that is what this emits:

  * TAX EXACTNESS: const_v(cr) = 2^(6+cr) * 3^(5cr-3) / 23^(1+2cr) for cr = 0..6,
    an exact rational identity that EXHIBITS the pure-{2,3,23} factorization (the
    "hundreds of debt primes" of the naive per-prime ledger are geometric noise,
    not here);
  * GROWTH BOUNDS: per node, 1 <= growth_v (every node grows) and
    growth_v <= env(cr,r) = ((3d+cr+3r)/(3d))^11 (max at child cavity 1), the
    exact geometric envelope, symbolic in the child mass S in [0, r].

norm_num for the arithmetic identities/envelopes; linarith + gcongr for the
symbolic monotone bounds.  The Lean kernel is the arbiter.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent

CR_MAX = 6
GROWTH_CLASSES = [(0, 1), (0, 2), (0, 3), (1, 1), (1, 2)]  # (cr, r)


def const(cr: int) -> Fr:
    return (Fr(3, 2) ** (11 * cr)) * (Fr(64, 621) ** (1 + 2 * cr))


def tax_theorems() -> list[tuple[str, str]]:
    out = []
    for cr in range(CR_MAX + 1):
        e2, e3, e23 = 6 + cr, 5 * cr - 3, 1 + 2 * cr
        # place 3's exponent on the correct side (denominator when 5cr-3 < 0)
        num = f"2^{e2}" + (f" * 3^{e3}" if e3 >= 0 else "")
        den = f"23^{e23}" + ("" if e3 >= 0 else f" * 3^{-e3}")
        lhs = f"((3:ℚ)/2)^(11*{cr}) * (64/621)^(1+2*{cr})"
        rhs = f"({num} : ℚ) / ({den})"
        assert const(cr) == _eval_rhs(e2, e3, e23), cr
        out.append((f"tax_const_c{cr}", f"theorem tax_const_c{cr} : {lhs} = {rhs} := by norm_num\n"))
    return out


def _eval_rhs(e2, e3, e23) -> Fr:
    num = 2 ** e2 * (3 ** e3 if e3 >= 0 else 1)
    den = 23 ** e23 * (1 if e3 >= 0 else 3 ** (-e3))
    return Fr(num, den)


def growth_theorems() -> list[tuple[str, str]]:
    out = []
    for cr, r in GROWTH_CLASSES:
        d = r + 1 + cr
        env = Fr(3 * d + cr + 3 * r, 3 * d) ** 11        # ((3d+cr+3r)/(3d))^11
        tag = f"c{cr}_r{r}"
        # env value (exact geometric envelope)
        out.append((f"growth_env_{tag}",
                    f"theorem growth_env_{tag} : "
                    f"(({3*d+cr+3*r}:ℚ)/{3*d})^11 = {env.numerator}/{env.denominator}"
                    f" := by norm_num\n"))
        # symbolic bounds in the child mass S in [0, r]:
        #   lower: 1 <= ((3d+cr+3S)/(3d))^11   (every node grows)
        #   upper: ((3d+cr+3S)/(3d))^11 <= env  (max at S = r)
        base = f"(({3*d+cr}:ℝ) + 3*S)/{3*d}"
        out.append((f"growth_ge_one_{tag}",
                    f"theorem growth_ge_one_{tag} (S : ℝ) (h0 : 0 ≤ S) :\n"
                    f"    (1:ℝ) ≤ ({base})^11 := by\n"
                    f"  have hb : (1:ℝ) ≤ {base} := by rw [le_div_iff₀ (by norm_num)]; nlinarith\n"
                    f"  calc (1:ℝ) = 1^11 := by norm_num\n"
                    f"    _ ≤ ({base})^11 := by gcongr\n"))
        env_base = Fr(3 * d + cr + 3 * r, 3 * d)
        out.append((f"growth_le_env_{tag}",
                    f"theorem growth_le_env_{tag} (S : ℝ) (h0 : 0 ≤ S) (h1 : S ≤ {r}) :\n"
                    f"    ({base})^11 ≤ (({env_base.numerator}:ℝ)/{env_base.denominator})^11 := by\n"
                    f"  have hb : {base} ≤ ({env_base.numerator}:ℝ)/{env_base.denominator} := by\n"
                    f"    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith\n"
                    f"  have hpos : (0:ℝ) ≤ {base} := by positivity\n"
                    f"  gcongr\n"))
    return out


def build():
    thms = tax_theorems() + growth_theorems()
    body = "".join(t for _, t in thms)
    emitter = CustomAssemblyEmitter(
        statement_template="«thms»«branches»",
        branch_template="",
        fills=lambda fam: {"thms": body},
        branch_fills=lambda inst: {},
        theorems=len(thms),
    )
    return emit(certify(_trivial()), LeanProfile(namespace=("G1", "TaxGrowth")),
                [emitter], _validation(), file_name="TaxGrowth.lean")


def _trivial() -> InequalityFamily:
    return InequalityFamily(
        name="TaxGrowth", symbols=(), grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "taxgrowth_root", target=lambda pt: sp.Integer(0))


def _validation() -> ValidationReport:
    def tax_exact():
        for cr in range(CR_MAX + 1):
            e2, e3, e23 = 6 + cr, 5 * cr - 3, 1 + 2 * cr
            assert const(cr) == _eval_rhs(e2, e3, e23), cr
        # the tax coefficients are pure {2,3,23}: verify prod const is {2,3,23}-smooth
        import math
        node = -6 * math.log(2) + 3 * math.log(3) + math.log(23)
        cher = 2 * math.log(23) - math.log(2) - 5 * math.log(3)
        assert abs(node - 2.2724) < 1e-3 and abs(cher - 0.0848) < 1e-3

    def growth_bracket():
        for cr, r in GROWTH_CLASSES:
            d = r + 1 + cr
            # growth(S=0) >= 1 and growth(S=r) = env, monotone between
            lo = Fr(3 * d + cr, 3 * d) ** 11
            hi = Fr(3 * d + cr + 3 * r, 3 * d) ** 11
            assert lo >= 1 and hi >= lo

    return ValidationReport.from_asserts(
        [("tax_exact_233", tax_exact), ("growth_bracket", growth_bracket)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"TaxGrowth: {res.n_theorems} theorems ({CR_MAX+1} tax identities + "
          f"{len(GROWTH_CLASSES)*3} growth bounds), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
