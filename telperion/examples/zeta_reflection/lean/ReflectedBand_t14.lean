/-  ReflectedBand_t14.lean -- ANDÚRIL A4 / G2 PILOT INSTANCE (AUTO-GENERATED).

    Emitted by telperion/examples/zeta_reflection/reflect_pilot.py.  DO NOT EDIT.

    A REAL on-line band in the critical strip whose SIGN CHAIN is checked by the LEAN
    KERNEL (`theorem ok : checkLine ReflectedBand_t14.d.boxes = true := by decide`), not by
    an Arb hypothesis.  This is the first G2 reflected band: a conclusion (n on-line zeros of
    completedRiemannZeta) with NO numeric hypotheses on the sign combinatorics -- the kernel
    computed it.

    Grid heights t in {14, 15, 22}; the supplied dyadic gLine boxes (from
    `arb_enclosure.enclose_lambda`, documented Arb non-kernel input) have signs (neg, pos, neg),
    giving 2 sign changes => 2 on-line zeros.

    Trust boundary (see CheckBand.lean):
      * KERNEL-DECIDED here: `ok` -- the boxes are sign-definite and alternate.
      * NAMED Arb-class HYPOTHESES: `hmem*` -- each box encloses the true gLine value.  Same
        trust class as the `henc*` rational-bound hypotheses of XiLineZeros' bands.
    conjecture1_proved = False.
-/
import CheckBand

open DIntvProd ZetaReflection XiLineZeros

namespace ReflectedBand_t14


/-- The pilot band: supplied dyadic `gLine` enclosures at the grid heights. -/
def d : BandData := ⟨[⟨-1044698152212676548522446602224124909281741004027039251959375928821234953705152350605, -1044698152212676548522446602224124909281741004027039251959375928821234953704683566707, -298⟩, ⟨99717822596094950620729602861100111464133505311626406978039488235919103314107209029, 99717822596094950620729602861100111464133505311626406978039488235919103314206485179, -293⟩, ⟨-1038697258148445978346843730799869702389672245413623774565910343656944450297462331107, -1038697258148445978346843730799869702389672245413623774565910343656944450296258423069, -304⟩]⟩

/-- **KERNEL-CHECKED sign chain** (the G2 headline): the boxes are sign-definite
    and strictly alternate -- decided by the kernel, no Arb hypothesis. -/
theorem ok : checkLine d.boxes = true := by decide

/-- The grid heights as a `Fin` map (strictly increasing integers). -/
def grid : Fin 3 → ℝ := ![(14 : ℝ), (15 : ℝ), (22 : ℝ)]

/-- **THE G2 REFLECTED BAND.**  From the KERNEL-checked sign chain `ok` and the
    named Arb-class enclosure-membership hypotheses `hmem*`, the verbatim T5
    `hLine` chain of 2 on-line zeros of `completedRiemannZeta` in `[14, 22]`. -/
theorem pilot
    (hmem0 : DIntvProd.DIntv.memR (gLine (14 : ℝ)) (d.boxes.get ⟨0, by decide⟩))
    (hmem1 : DIntvProd.DIntv.memR (gLine (15 : ℝ)) (d.boxes.get ⟨1, by decide⟩))
    (hmem2 : DIntvProd.DIntv.memR (gLine (22 : ℝ)) (d.boxes.get ⟨2, by decide⟩))
    : ∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧
        (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧
        (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  refine checkLine_correct d (14 : ℝ) (22 : ℝ) 2
    (by decide) grid ?_ ?_ ?_ ?_ ok
  · -- StrictMono grid
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [grid] <;> norm_num
  · -- T0 <= grid 0
    simp [grid]
  · -- grid (last) <= T1
    simp [grid, Fin.last]
  · -- membership at each index
    intro i
    fin_cases i
    · exact hmem0
    · exact hmem1
    · exact hmem2

end ReflectedBand_t14
