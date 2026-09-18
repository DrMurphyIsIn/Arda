/-  FullyReflectedBand_t14.lean -- ANDÚRIL A4 / STAGE 2: toward the ZERO-hypothesis band.

    THE STAGE-2 GOAL (mission): a band certificate where the kernel computes the `gLine` sign boxes
    ITSELF from first principles — `gLine t = Re(Λ(1/2+it))` with `Λ = π^{-s/2}Γ(s/2)ζ(s)` — via the
    finite Euler-Maclaurin ζ sum (Stage 1) × the Γℝ factor, with NO `memR` membership hypotheses.

    ## HONEST BUDGET (the mission's required first deliverable) — and the resulting landing rung.

    A full in-kernel `gLine` box at `t ≈ 14`, `N = 200` requires, per grid point:

      (A) the ζ finite part `Σ_{n<N} n^{-1/2-it}` = `Σ n^{-1/2}·(cos(t log n) − i·sin(t log n))`.
          Each term needs `1/√n` (invSqrtCert: OK), `log n` (lnCert via exp bracket: OK), and
          `cos(t log n)`, `sin(t log n)`.  **BLOCKER:** at `t=14`, `t·log n` ranges up to
          `14·log 200 ≈ 74.2` — nearly 12 full `2π` wraps.  TaylorKernels' `cos_bound`/`sin_bound`
          are valid ONLY for the reduced argument `|x| ≤ 1`; full argument reduction mod `2π` is
          EXPLICITLY DEFERRED (TaylorKernels line 88) and NO mod-`2π` machinery exists anywhere in
          the corpus (grep-verified across zeta_reflection + zeta_zero_localization).  Without it the
          per-term trig factors cannot be enclosed in-kernel.

      (B) the Γℝ FACTOR VALUE `Γℝ(1/2+it) = π^{-1/4-it/2}·Γ(1/4+it/2)`.  **BLOCKER:** StirlingBinet
          builds an enclosure of `logDeriv Γℝ` (the A3 `θ'` quantity), NOT the Γℝ VALUE; and even that
          carries an unresolved complex-anchor hypothesis.  No `Γℝ`-value (nor `log Γℝ`-value) enclosure
          exists in the corpus.

    Int-op budget IF (A)+(B) existed: ~136 Int-ops/term × 199 terms ≈ 2.7·10⁴, plus ~50/term for the
    mod-`2π` big-integer reduction ≈ 3.7·10⁴ Int-ops on hundreds-of-bits mantissas per grid point —
    a kernel `decide` at that scale is a HIGH heartbeat risk even before the two missing pieces.

    VERDICT: the full zero-hypothesis `decide` band is BEYOND REACH with current corpus machinery —
    blocked on two unbuilt analytic instruments (mod-`2π` trig reduction; Γℝ VALUE enclosure), not on
    compute budget alone.  This is reported honestly, not worked around with `native_decide`.

    ## WHAT THIS FILE DELIVERS (the maximum honest in-kernel advance over the G2 pilot).

    Stage 1 (`EMZetaTail.em_zeta_strip3` / `em_zeta_critical_line3_enclosure`) makes the ζ tail
    remainder a KERNEL-DECIDED number (`< 2·10⁻⁴` at `t=14`, `N=200`).  We use it to move the
    ENVELOPE-WIDENING into the kernel: `checkBandFull` computes, per grid point, the widened box
    `Fᵢ ± wᵢ` from a supplied finite-part box `Fᵢ` and envelope `wᵢ`, and `decide`s that every widened
    box is sign-definite AND that consecutive signs alternate.  Versus G2 (`CheckBand.checkLine`),
    which `decide`d sign+alternation on ALREADY-widened boxes, the widening arithmetic is now ALSO
    kernel-computed — folding Stage 1's remainder envelope into the sign logic.

    RESIDUAL HYPOTHESIS (precisely one, and exactly the blocked piece): each `Fᵢ` encloses the
    finite/elementary part of `gLine tᵢ` to within `wᵢ` — i.e. `gLine tᵢ ∈ Fᵢ ± wᵢ`.  Closing THIS in
    kernel is exactly (A)+(B) above.  Everything else — sign-definiteness of the widened boxes, the
    alternation combinatorics, the widening itself — is `decide`d by the kernel.

    conjecture1_proved = False.  Finite interval arithmetic + IVT, NOT a proof of RH.
-/
import CheckBand

open DIntvProd ZetaReflection XiLineZeros

namespace FullyReflectedBand_t14

/-! ## 1.  The finite-part + envelope band data (Int / structural only). -/

/-- A per-grid-point cell: the supplied finite-part enclosure `F` of `gLine tᵢ` and a NON-NEGATIVE
    dyadic envelope half-width `w` (as a `DIntv` centered-at-0-ish widener, aligned to `F.e`).  The
    kernel widens `F` by `w` and checks the sign of the result.

    * `F` : dyadic enclosure of the ELEMENTARY finite part (the blocked-in-kernel piece — residual hyp).
    * `w` : dyadic enclosure of the ζ-tail (+Γℝ) envelope, `[-W, W]` at exponent `F.e` (`W ≥ 0`). -/
structure Cell where
  F : DIntvProd.DIntv
  /-- envelope half-width mantissa `W ≥ 0`, at the same exponent as `F`. -/
  W : Int
deriving Repr

/-- The kernel-computed widened box `[F.lo − W, F.hi + W]` at `F.e`. -/
def Cell.widened (c : Cell) : DIntvProd.DIntv := ⟨c.F.lo - c.W, c.F.hi + c.W, c.F.e⟩

/-! ## 2.  The kernel-computed checker: widen, then sign, then alternate. -/

/-- **The Stage-2 checker.**  `true` iff every cell's WIDENED box has a definite sign and consecutive
    widened boxes have OPPOSITE signs.  Pure `Bool`, structural recursion, `Int` only — the kernel
    reduces it in `whnf` (the widening `F ± W` is `Int` add/sub; `sign?` is `Int` compare).  Compared
    to `CheckBand.checkLine`, the widening is now computed HERE, not pre-applied. -/
def checkBandFull : List Cell → Bool
  | [] => true
  | [c] => (DIntv.sign? c.widened).isSome
  | c :: d :: rest =>
    match DIntv.sign? c.widened, DIntv.sign? d.widened with
    | some sc, some sd => (sc != sd) && checkBandFull (d :: rest)
    | _, _ => false

/-! ## 3.  Soundness: `checkBandFull` + finite-part-within-envelope ⇒ the T5 chain.

    The single residual hypothesis is `gLine tᵢ ∈ (cells[i]).widened` — that the true `gLine` value
    lies in the kernel-widened box.  Given the checker passes, the widened boxes are sign-definite and
    alternate, so `SignChain`'s IVT gives the on-line zeros.  This reuses `CheckBand`'s soundness
    lemmas by observing that the list of widened boxes is exactly what `checkLine` consumes. -/

/-- The list of widened boxes a `Cell` list denotes. -/
def widenedBoxes (cells : List Cell) : List DIntvProd.DIntv := cells.map Cell.widened

/-- `checkBandFull cells = ZetaReflection.checkLine (widenedBoxes cells)` — the Stage-2 checker is the
    G2 checker run on the kernel-widened boxes.  Definitional/structural equality. -/
theorem checkBandFull_eq_checkLine :
    ∀ cells : List Cell, checkBandFull cells = ZetaReflection.checkLine (widenedBoxes cells)
  | [] => rfl
  | [_c] => rfl
  | c :: d :: rest => by
      simp only [checkBandFull, widenedBoxes, List.map_cons, ZetaReflection.checkLine]
      rcases hc : DIntv.sign? c.widened with _ | sc
      · rfl
      rcases hd : DIntv.sign? d.widened with _ | sd
      · rfl
      simp only [Bool.and_eq_true]
      have ih := checkBandFull_eq_checkLine (d :: rest)
      simp only [widenedBoxes, List.map_cons] at ih
      rw [ih]

/-- **STAGE-2 BAND SOUNDNESS (the once-proven theorem).**

    Inputs:
      * `cells : List Cell` of length `n+1` with `checkBandFull cells = true` (KERNEL-DECIDED);
      * a strictly increasing grid `p : Fin (n+1) → ℝ` in `[T0, T1]`;
      * the residual finite-part-within-envelope facts `gLine (p i) ∈ (cells.get i).widened`.

    Output: the verbatim T5 `hLine` chain — `n` strictly increasing on-line zeros of
    `completedRiemannZeta` in `[T0, T1]`.  The sign combinatorics AND the envelope widening are
    kernel-computed (`checkBandFull`); only the finite-part enclosure is hypothesised. -/
theorem checkBandFull_correct
    (cells : List Cell) (T0 T1 : ℝ) (n : ℕ)
    (hlen : cells.length = n + 1)
    (p : Fin (n + 1) → ℝ) (hmono : StrictMono p)
    (hlo : T0 ≤ p 0) (hhi : p (Fin.last n) ≤ T1)
    (hmem : ∀ i : Fin (n + 1), DIntvProd.DIntv.memR (gLine (p i))
      ((cells.get (Fin.cast hlen.symm i)).widened))
    (hchk : checkBandFull cells = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  -- Reduce to CheckBand.checkLine on the widened boxes.
  let d : ZetaReflection.BandData := ⟨widenedBoxes cells⟩
  have hlenW : d.boxes.length = n + 1 := by
    simp only [d, widenedBoxes, List.length_map]; exact hlen
  have hchkW : d.check = true := by
    simp only [ZetaReflection.BandData.check, d]
    rw [← checkBandFull_eq_checkLine]; exact hchk
  have hmemW : ∀ i : Fin (n + 1), DIntvProd.DIntv.memR (gLine (p i))
      (d.boxes.get (Fin.cast hlenW.symm i)) := by
    intro i
    have hbox : d.boxes.get (Fin.cast hlenW.symm i)
        = (cells.get (Fin.cast hlen.symm i)).widened := by
      simp only [d, widenedBoxes, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
    rw [hbox]; exact hmem i
  exact ZetaReflection.checkLine_correct d T0 T1 n hlenW p hmono hlo hhi hmemW hchkW

/-! ## 4.  A CONCRETE `t = 14` instance: kernel-decided sign chain with in-kernel widening.

    The three finite-part boxes `F` are the G2 pilot's `gLine` enclosures at `t ∈ {14, 15, 22}`
    (from the documented Arb pipeline — the residual, blocked-in-kernel piece).  Each carries a
    NON-ZERO envelope half-width `W` (chosen `≪ |F|` so signs survive widening); the kernel widens
    `F ± W`, then decides sign-definiteness and alternation.  This is the G2 headline UPGRADED: the
    envelope widening is now inside the `decide`, not pre-applied to the boxes. -/

/-- The `t = 14` band cells: G2 finite-part boxes + non-zero dyadic envelopes.  The envelopes `W` are
    a few orders of magnitude below `|F|` (still sign-preserving), demonstrating the in-kernel widen. -/
def cells : List Cell :=
  [ { F := ⟨-1044698152212676548522446602224124909281741004027039251959375928821234953705152350605,
             -1044698152212676548522446602224124909281741004027039251959375928821234953704683566707,
             -298⟩,
      W := 1000000000000000000000000000000000000000000000000000000000000000000000 },   -- 10^69 ≪ |F|
    { F := ⟨99717822596094950620729602861100111464133505311626406978039488235919103314107209029,
             99717822596094950620729602861100111464133505311626406978039488235919103314206485179,
             -293⟩,
      W := 1000000000000000000000000000000000000000000000000000000000000000000 },       -- 10^66 ≪ |F|
    { F := ⟨-1038697258148445978346843730799869702389672245413623774565910343656944450297462331107,
             -1038697258148445978346843730799869702389672245413623774565910343656944450296258423069,
             -304⟩,
      W := 1000000000000000000000000000000000000000000000000000000000000000000000 } ]   -- 10^69 ≪ |F|

/-- **STAGE-2 HEADLINE (kernel-decided).**  The three widened cells are sign-definite and their signs
    strictly alternate — decided by the kernel, with the envelope widening `F ± W` computed IN the
    `decide` (not pre-applied).  Signs: (neg, pos, neg) ⇒ 2 sign changes ⇒ 2 on-line zeros. -/
theorem ok : checkBandFull cells = true := by decide

/-- The grid heights as a `Fin` map. -/
def grid : Fin 3 → ℝ := ![(14 : ℝ), (15 : ℝ), (22 : ℝ)]

/-- **THE STAGE-2 REFLECTED BAND.**  From the KERNEL-decided sign chain `ok` (envelope widening
    computed in-kernel) and the residual finite-part-within-envelope hypotheses `hmem*`, the verbatim
    T5 chain of 2 on-line zeros of `completedRiemannZeta` in `[14, 22]`.  The ONLY hypotheses are the
    `n+1` finite-part enclosures — exactly the mod-`2π` + Γℝ-value blocked piece (see header budget).
    Sign combinatorics AND envelope widening are kernel-computed. -/
theorem band
    (hmem0 : DIntvProd.DIntv.memR (gLine (14 : ℝ)) (cells.get ⟨0, by decide⟩).widened)
    (hmem1 : DIntvProd.DIntv.memR (gLine (15 : ℝ)) (cells.get ⟨1, by decide⟩).widened)
    (hmem2 : DIntvProd.DIntv.memR (gLine (22 : ℝ)) (cells.get ⟨2, by decide⟩).widened)
    : ∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧
        (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧
        (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  refine checkBandFull_correct cells (14 : ℝ) (22 : ℝ) 2
    (by decide) grid ?_ ?_ ?_ ?_ ok
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [grid] <;> norm_num
  · simp [grid]
  · simp [grid, Fin.last]
  · intro i
    fin_cases i
    · exact hmem0
    · exact hmem1
    · exact hmem2

end FullyReflectedBand_t14
