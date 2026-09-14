#!/usr/bin/env python3
"""reflect_pilot.py -- ANDÚRIL A4 / G2 reflected-band pilot emitter.

Emits `ReflectedBand_t14.lean`: a REAL on-line band low in the critical strip whose
sign-chain is CHECKED BY THE LEAN KERNEL (`theorem ok : checkLine d.boxes = true := by
decide`) rather than carried as an Arb hypothesis.

Trust boundary (see CheckBand.lean docstring for the full statement):

  * KERNEL-COMPUTED: that the supplied `gLine` boxes are sign-definite and strictly
    alternate -- `checkLine d.boxes = true`, decided by the kernel on Int-only data.
  * VERIFIED-FROM-CANDIDATE (once-proven `checkLine_correct`): given the kernel result
    and the interval-membership facts `gLine t_k in box_k`, the T5 `hLine` chain follows.

The boxes come from `telperion.arb_enclosure.enclose_lambda(1/2, t_k)` -- the SAME Arb
enclosure trust class as the existing per-point `enclose_lambda` sign facts the
`XiLineZeros`/Bragg emitters already consume.  Arb returns dyadic (mantissa / 2^p)
rational endpoints; we rescale both endpoints of each band to a common exponent to get an
exact `DIntv (lo hi e : Int)`.  A wrong enclosure yields a refused/mismatched sign chain,
never a wrong certificate.  conjecture1_proved = False.

Hints only: the Arb pipeline is the untrusted candidate producer; everything the Lean file
asserts is either kernel-decided or a named `memR` hypothesis of the documented Arb class.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "telperion" / "src"))

from telperion.arb_enclosure import enclose_lambda  # noqa: E402

# --- pilot band configuration ------------------------------------------------------------
# Grid heights (integers, exactly representable as dyadic (t,0)) straddling the first zeros
# of zeta.  The first three nontrivial zeros sit at t ~ 14.13, 21.02, 25.01, so the grid
# [14, 15, 22] has gLine signs (-, +, -): TWO sign changes => TWO on-line zeros.
GRID = [14, 15, 22]
PREC_BITS = 256


def dyadic_of_fraction(f: Fraction) -> tuple[int, int]:
    """Return (mantissa, exp) with f = mantissa * 2^exp, for a dyadic Fraction f.

    Raises if f is not dyadic (denominator not a power of two)."""
    d = f.denominator
    if d & (d - 1) != 0:
        raise ValueError(f"non-dyadic fraction {f}")
    p = d.bit_length() - 1  # d == 2^p
    return f.numerator, -p


def box_to_dintv(lo: Fraction, hi: Fraction) -> tuple[int, int, int]:
    """Rescale a dyadic [lo, hi] to a common exponent, returning (loM, hiM, e) with
    lo == loM * 2^e and hi == hiM * 2^e EXACTLY (no rounding: inputs are dyadic)."""
    loM, loE = dyadic_of_fraction(lo)
    hiM, hiE = dyadic_of_fraction(hi)
    e = min(loE, hiE)
    loM <<= (loE - e)
    hiM <<= (hiE - e)
    assert Fraction(loM) * Fraction(2) ** e == lo
    assert Fraction(hiM) * Fraction(2) ** e == hi
    return loM, hiM, e


def sign_of(loM: int, hiM: int) -> str:
    if loM > 0:
        return "pos"
    if hiM < 0:
        return "neg"
    raise ValueError(f"box [{loM},{hiM}] straddles 0 -- not sign-definite")


def build():
    rows = []
    for t in GRID:
        (lo, hi), (ilo, ihi) = enclose_lambda(Fraction(1, 2), t, PREC_BITS)
        if not (ilo <= 0 <= ihi):
            raise RuntimeError(f"t={t}: imaginary box excludes 0 -- not on-line real")
        loM, hiM, e = box_to_dintv(lo, hi)
        rows.append({"t": t, "lo": loM, "hi": hiM, "e": e, "sign": sign_of(loM, hiM),
                     "lo_f": lo, "hi_f": hi})
    # sanity: strict sign alternation
    signs = [r["sign"] for r in rows]
    for a, b in zip(signs, signs[1:]):
        if a == b:
            raise RuntimeError(f"grid signs do not alternate: {signs}")
    return rows


LEAN_HEADER = '''\
/-  ReflectedBand_t14.lean -- ANDÚRIL A4 / G2 PILOT INSTANCE (AUTO-GENERATED).

    Emitted by telperion/examples/zeta_reflection/reflect_pilot.py.  DO NOT EDIT.

    A REAL on-line band in the critical strip whose SIGN CHAIN is checked by the LEAN
    KERNEL (`theorem ok : checkLine ReflectedBand_t14.d.boxes = true := by decide`), not by
    an Arb hypothesis.  This is the first G2 reflected band: a conclusion (n on-line zeros of
    completedRiemannZeta) with NO numeric hypotheses on the sign combinatorics -- the kernel
    computed it.

    Grid heights t in {gridlist}; the supplied dyadic gLine boxes (from
    `arb_enclosure.enclose_lambda`, documented Arb non-kernel input) have signs {signs},
    giving {n} sign changes => {n} on-line zeros.

    Trust boundary (see CheckBand.lean):
      * KERNEL-DECIDED here: `ok` -- the boxes are sign-definite and alternate.
      * NAMED Arb-class HYPOTHESES: `hmem*` -- each box encloses the true gLine value.  Same
        trust class as the `henc*` rational-bound hypotheses of XiLineZeros' bands.
    conjecture1_proved = False.
-/
import CheckBand

open DIntvProd ZetaReflection XiLineZeros

namespace ReflectedBand_t14
'''


def emit(rows) -> str:
    n = len(rows) - 1  # number of zeros = number of sign changes
    signs = [r["sign"] for r in rows]
    out: list[str] = []
    out.append(LEAN_HEADER.format(
        gridlist="{" + ", ".join(str(r["t"]) for r in rows) + "}",
        signs="(" + ", ".join(signs) + ")",
        n=n))
    out.append("")

    # The band data: the supplied dyadic gLine boxes.
    box_terms = ", ".join(f"⟨{r['lo']}, {r['hi']}, {r['e']}⟩" for r in rows)
    out.append("/-- The pilot band: supplied dyadic `gLine` enclosures at the grid heights. -/")
    out.append(f"def d : BandData := ⟨[{box_terms}]⟩")
    out.append("")

    # The KERNEL-decided sign-chain fact.
    out.append("/-- **KERNEL-CHECKED sign chain** (the G2 headline): the boxes are sign-definite")
    out.append("    and strictly alternate -- decided by the kernel, no Arb hypothesis. -/")
    out.append("theorem ok : checkLine d.boxes = true := by decide")
    out.append("")

    # The grid as a Fin (n+1) -> R map, via an explicit list.
    grid_vals = ", ".join(f"({r['t']} : ℝ)" for r in rows)
    out.append("/-- The grid heights as a `Fin` map (strictly increasing integers). -/")
    out.append(f"def grid : Fin {n + 1} → ℝ := ![{grid_vals}]")
    out.append("")

    # The reflected-band pilot theorem: consumes `ok` (kernel) + the named Arb memR
    # hypotheses + the elementary grid facts, and yields the T5 hLine chain.
    hmem_binders = []
    for i, r in enumerate(rows):
        hmem_binders.append(
            f"    (hmem{i} : DIntvProd.DIntv.memR (gLine ({r['t']} : ℝ)) "
            f"(d.boxes.get ⟨{i}, by decide⟩))")
    hmem_block = "\n".join(hmem_binders)

    out.append("/-- **THE G2 REFLECTED BAND.**  From the KERNEL-checked sign chain `ok` and the")
    out.append("    named Arb-class enclosure-membership hypotheses `hmem*`, the verbatim T5")
    out.append(f"    `hLine` chain of {n} on-line zeros of `completedRiemannZeta` in `[{rows[0]['t']}, {rows[-1]['t']}]`. -/")
    out.append(f"theorem pilot")
    out.append(hmem_block)
    out.append(f"    : ∃ xs : List ℝ, xs.length = {n} ∧ xs.IsChain (· < ·) ∧")
    out.append(f"        (∀ t ∈ xs, ({rows[0]['t']} : ℝ) ≤ t ∧ t ≤ ({rows[-1]['t']} : ℝ)) ∧")
    out.append("        (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by")
    out.append(f"  refine checkLine_correct d ({rows[0]['t']} : ℝ) ({rows[-1]['t']} : ℝ) {n}")
    out.append("    (by decide) grid ?_ ?_ ?_ ?_ ok")
    out.append("  · -- StrictMono grid")
    out.append("    intro i j hij")
    out.append("    fin_cases i <;> fin_cases j <;> simp_all [grid] <;> norm_num")
    out.append("  · -- T0 <= grid 0")
    out.append("    simp [grid]")
    out.append("  · -- grid (last) <= T1")
    out.append("    simp [grid, Fin.last]")
    out.append("  · -- membership at each index")
    out.append("    intro i")
    idx_cases = " <;> ".join([""])  # placeholder; real logic below
    out.append("    fin_cases i")
    for i in range(len(rows)):
        out.append(f"    · exact hmem{i}")
    out.append("")
    out.append("end ReflectedBand_t14")
    out.append("")
    return "\n".join(out)


def main():
    rows = build()
    print("Pilot band grid + dyadic gLine boxes:", file=sys.stderr)
    for r in rows:
        print(f"  t={r['t']:>3}  sign={r['sign']:>3}  "
              f"box=[{r['lo']}, {r['hi']}]*2^{r['e']}  "
              f"(~[{float(r['lo_f']):.3e}, {float(r['hi_f']):.3e}])", file=sys.stderr)
    src = emit(rows)
    out_path = Path(__file__).resolve().parent / "lean" / "ReflectedBand_t14.lean"
    out_path.write_text(src)
    print(f"Wrote {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
