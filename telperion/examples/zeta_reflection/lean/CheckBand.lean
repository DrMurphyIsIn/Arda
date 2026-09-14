/-  CheckBand.lean -- ANDÚRIL A4 / milestone G2: the reflected-band pilot checker.

    This file delivers the FIRST band certificate whose numeric sign-chain the KERNEL
    ITSELF checks by computation (`theorem ok : checkLine d = true := by decide`) rather
    than carrying it as an Arb hypothesis.

    ## The honest pilot rung (on-line-only, low height)

    The mission's descoped-but-real target: `checkLine` operates over a SUPPLIED-and-verified
    table of `gLine` boxes (dyadic `DIntv` intervals).  Concretely, the trust boundary splits:

      * COMPUTED BY THE KERNEL (via `decide`/`rfl` on `checkLine d = true`):  the sign-chain
        LOGIC -- that each supplied box is sign-definite (`sign? = some b`) and that the signs
        strictly ALTERNATE across the grid.  This is pure `Int` arithmetic (min/max/compare on
        the `DIntv` mantissas), structural `List` recursion, NO `Rat`, NO well-founded
        recursion -- exactly the A0-measured-green `checkAlt` shape from `Spike/Toy.lean`.

      * VERIFIED-FROM-CANDIDATE (the once-proven `checkLine_correct`):  IF the checker passes
        AND each supplied box genuinely encloses `gLine tᵢ` (`DIntvProd.DIntv.memR (gLine tᵢ)
        boxᵢ`), THEN the verbatim T5 `hLine` chain of `n` on-line zeros of
        `completedRiemannZeta` holds -- via `sign?_pos`/`sign?_neg` (a box with a definite sign
        pins the sign of any real it contains) → opposite signs give a sign change →
        `SignChain.exists_zero_of_sign_change`'s IVT.

    What this SHRINKS vs the `XiLineZeros` per-instance template: there, each band carried `n`
    hand-written rational-bound hypotheses on `gLine` plus per-interval IVT bookkeeping.  Here
    the sign-definiteness AND the sign-alternation combinatorics are KERNEL-COMPUTED from an
    `Int`-only table; the residual per-band hypotheses are just the `n+1` interval-membership
    facts `gLine tᵢ ∈ boxᵢ` (the "did the untrusted Arb pipeline hand us a correct enclosure?"
    obligation).

    ## The exact remaining gap to full T5-replacement

    At this rung the membership facts `gLine tᵢ ∈ boxᵢ` are HYPOTHESES.  Closing them in-kernel
    means COMPUTING each `gLine tᵢ` box from `EMZetaComplex.em_zeta_critical_line_enclosure`
    (the ζ factor) × `StirlingBinet.logDeriv_gammaR_enclosure` (the Γℝ factor) with a
    tight-enough envelope.  The available K=1 ζ envelope `‖1/2+it‖ ≈ t` is far too loose to
    sign-determine `completedRiemannZeta` at real heights (at t≈14, |Λ| ~ 1e-2 but the K=1
    envelope is ~14); a sign-tight box needs the K≥2 Euler–Maclaurin remainder (A2 theorem 1's
    hard Bernoulli tail, currently `StirlingBinetWip`'s `sorry`).  That is the single, precisely
    identified blocker between this pilot and full numeric-hypothesis-free bands.

    conjecture1_proved = False.  This is finite interval arithmetic + IVT, NOT a proof of RH.
-/
import EMZetaComplex
import XiLineZeros
import DIntvCorrect

open DIntvProd XiLineZeros

namespace ZetaReflection

/-! ## 1.  The band-data table (Int / structural only). -/

/-- A reflected on-line band, as an `Int`-only table the untrusted Arb pipeline emits.

    * `boxes` : the supplied dyadic `DIntv` enclosures of `gLine` at the grid heights.  Each
      `DIntv` is three `Int`s (`lo`, `hi`, `e`); NO `Rat` anywhere.
    * everything the KERNEL checks (`checkLine`) reads ONLY `boxes` -- the grid heights and
      their enclosure-membership live in the SOUNDNESS theorem's hypotheses, not the checker.

    Kept deliberately minimal for the G2 pilot: the height list, its monotonicity and the
    `memR` facts are threaded through `checkLine_correct` as explicit arguments (the honest
    residual trust boundary), so `BandData` carries only what the kernel computes on. -/
structure BandData where
  /-- Supplied dyadic enclosures of `gLine` at the `n+1` grid heights. -/
  boxes : List DIntvProd.DIntv
deriving Repr

/-! ## 2.  The kernel-computed checker (structural `List` recursion, `Int`-only).

    Identical in shape to the A0-measured `Spike.checkAlt` (green under `decide`/`rfl`):
    verify every box is sign-definite and consecutive signs differ. -/

/-- **The reflected-band sign-chain checker.**  Returns `true` iff every box in the list has a
    DEFINITE sign (`sign? = some _`, i.e. the interval excludes 0) and consecutive boxes have
    OPPOSITE signs.  Pure `Bool`, structural recursion, `Int` comparisons only -- no `Rat`, no
    WF recursion, no `ByteArray`; the kernel reduces it in `whnf`. -/
def checkLine : List DIntvProd.DIntv → Bool
  | [] => true
  | [b] => (DIntv.sign? b).isSome
  | b :: c :: rest =>
    match DIntv.sign? b, DIntv.sign? c with
    | some sb, some sc => (sb != sc) && checkLine (c :: rest)
    | _, _ => false

/-- Convenience: run the checker on a `BandData`. -/
@[inline] def BandData.check (d : BandData) : Bool := checkLine d.boxes

/-! ## 3.  Soundness: `checkLine` + enclosure-membership ⇒ the T5 `hLine` chain.

    We build up from a single sign-change pair to the full chain, mirroring
    `SignChain.alternating_signs_chain` but sourcing the per-point sign facts from the
    KERNEL-CHECKED `checkLine` result rather than from rational-bound hypotheses. -/

/-- A sign-definite box that contains a real pins that real's sign as a nonzero real of the
    matching sign.  (`some true` → positive, `some false` → negative.) -/
theorem sign_of_box {x : ℝ} {b : DIntvProd.DIntv} {s : Bool}
    (hsign : DIntv.sign? b = some s) (hmem : DIntv.memR x b) :
    if s then 0 < x else x < 0 := by
  cases s with
  | true  => simpa using DIntv.sign?_pos hsign hmem
  | false => simpa using DIntv.sign?_neg hsign hmem

/-- **Opposite-sign boxes ⇒ a `gLine` product sign change.**  If two boxes have opposite
    definite signs and each contains the corresponding `gLine` value, then
    `gLine a * gLine b < 0` -- exactly `SignChain.exists_zero_of_sign_change`'s hypothesis. -/
theorem gLine_mul_neg_of_boxes {a b : ℝ} {Ia Ib : DIntvProd.DIntv} {sa sb : Bool}
    (hsa : DIntv.sign? Ia = some sa) (hsb : DIntv.sign? Ib = some sb)
    (hne : sa ≠ sb)
    (hma : DIntv.memR (gLine a) Ia) (hmb : DIntv.memR (gLine b) Ib) :
    gLine a * gLine b < 0 := by
  have ha := sign_of_box hsa hma
  have hb := sign_of_box hsb hmb
  -- `sa ≠ sb` with `Bool` means one is `true` and the other `false`.
  cases sa with
  | true =>
    cases sb with
    | true => exact absurd rfl hne
    | false =>
      simp only [if_true] at ha hb
      exact mul_neg_of_pos_of_neg ha hb
  | false =>
    cases sb with
    | true =>
      simp only [if_true] at ha hb
      exact mul_neg_of_neg_of_pos ha hb
    | false => exact absurd rfl hne

/-- One interior on-line zero from a checked, membership-backed sign-change pair.  Thin
    wrapper over `SignChain.exists_zero_of_sign_change`. -/
theorem zero_of_checked_pair {a b : ℝ} (hab : a < b)
    {Ia Ib : DIntvProd.DIntv} {sa sb : Bool}
    (hsa : DIntv.sign? Ia = some sa) (hsb : DIntv.sign? Ib = some sb) (hne : sa ≠ sb)
    (hma : DIntv.memR (gLine a) Ia) (hmb : DIntv.memR (gLine b) Ib) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
  have hsign : gLine a * gLine b < 0 := gLine_mul_neg_of_boxes hsa hsb hne hma hmb
  have hcont : ContinuousOn gLine (Set.Icc a b) := gLine_continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) hcont ⟨le_of_lt hnb, le_of_lt hpa⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpa)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hnb)
    exact ⟨r, hlo, hhi, by rw [lambda_eq_gLine, hz]; simp⟩
  · have hmem : (0 : ℝ) ∈ gLine '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) hcont ⟨le_of_lt hna, le_of_lt hpb⟩
    obtain ⟨r, hIcc, hz⟩ := hmem
    have hlo : a < r := by
      rcases lt_or_eq_of_le hIcc.1 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_lt hna)
    have hhi : r < b := by
      rcases lt_or_eq_of_le hIcc.2 with h | h
      · exact h
      · exact absurd (h ▸ hz) (ne_of_gt hpb)
    exact ⟨r, hlo, hhi, by rw [lambda_eq_gLine, hz]; simp⟩

/-! ### The chain assembly.

    We phrase the grid + membership over `Fin (n+1)` (as `SignChain.alternating_signs_chain`
    does) and DERIVE the per-pair sign facts from `checkLine (List.ofFn boxes) = true`.  This
    keeps the KERNEL-CHECKED object a plain `List` while the soundness statement quantifies over
    an indexed grid. -/

/-- `checkLine` on a nonempty list gives each element a definite sign. -/
theorem checkLine_sign_isSome :
    ∀ {l : List DIntvProd.DIntv}, checkLine l = true → ∀ b ∈ l, (DIntv.sign? b).isSome = true
  | [], _, _, hb => by simp at hb
  | [b], h, x, hx => by
      simp only [List.mem_singleton] at hx; subst hx
      simpa [checkLine] using h
  | b :: c :: rest, h, x, hx => by
      simp only [checkLine] at h
      -- destructure the leading match
      rcases hb : DIntv.sign? b with _ | sb
      · rw [hb] at h; simp at h
      rcases hc : DIntv.sign? c with _ | sc
      · rw [hb, hc] at h; simp at h
      rw [hb, hc] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨_, hrest⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hb]; rfl
      · exact checkLine_sign_isSome hrest x hx'

/-- **Consecutive boxes carry opposite definite signs** when `checkLine` passes.  Stated as:
    for adjacent list positions `i, i+1`, the signs are both `some` and differ. -/
theorem checkLine_adjacent_opposite :
    ∀ {l : List DIntvProd.DIntv}, checkLine l = true →
      ∀ i : ℕ, (hi : i + 1 < l.length) →
        ∃ sa sb : Bool, DIntv.sign? (l.get ⟨i, Nat.lt_of_succ_lt hi⟩) = some sa ∧
          DIntv.sign? (l.get ⟨i + 1, hi⟩) = some sb ∧ sa ≠ sb
  | [], _, i, hi => by simp at hi
  | [_b], _, i, hi => by simp at hi
  | b :: c :: rest, h, i, hi => by
      simp only [checkLine] at h
      rcases hb : DIntv.sign? b with _ | sb
      · rw [hb] at h; simp at h
      rcases hc : DIntv.sign? c with _ | sc
      · rw [hb, hc] at h; simp at h
      rw [hb, hc] at h
      simp only [Bool.and_eq_true, bne_iff_ne] at h
      obtain ⟨hne, hrest⟩ := h
      cases i with
      | zero =>
          refine ⟨sb, sc, ?_, ?_, hne⟩
          · simpa using hb
          · simpa using hc
      | succ j =>
          have hi' : j + 1 < (c :: rest).length := by
            simpa [List.length] using Nat.lt_of_succ_lt_succ hi
          obtain ⟨sa', sb', h1, h2, hne'⟩ := checkLine_adjacent_opposite hrest j hi'
          exact ⟨sa', sb', by simpa using h1, by simpa using h2, hne'⟩

/-- **A4 pilot soundness (the once-proven theorem that shrinks the trust boundary).**

    Inputs:
      * `d : BandData` with `d.boxes` of length `n+1`;
      * a strictly increasing grid `p : Fin (n+1) → ℝ` inside `[T0, T1]`;
      * the enclosure-membership facts `gLine (p i) ∈ d.boxes.get i` (the honest residual
        hypotheses at this rung -- the untrusted-candidate obligation);
      * the KERNEL-CHECKED fact `d.check = true`.

    Output: the VERBATIM T5 `hLine` chain -- `n` strictly increasing on-line zeros of
    `completedRiemannZeta` inside `[T0, T1]`.  Compare `SignChain.alternating_signs_chain`:
    here the per-point sign hypotheses are replaced by the single computed `d.check = true`. -/
theorem checkLine_correct
    (d : BandData) (T0 T1 : ℝ) (n : ℕ)
    (hlen : d.boxes.length = n + 1)
    (p : Fin (n + 1) → ℝ) (hmono : StrictMono p)
    (hlo : T0 ≤ p 0) (hhi : p (Fin.last n) ≤ T1)
    (hmem : ∀ i : Fin (n + 1), DIntvProd.DIntv.memR (gLine (p i))
      (d.boxes.get (Fin.cast hlen.symm i)))
    (hchk : d.check = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  have hcheck : checkLine d.boxes = true := hchk
  -- per-pair interior zero, indexed by `Fin n`
  have hroot : ∀ i : Fin n, ∃ r : ℝ, p i.castSucc < r ∧ r < p i.succ ∧
      completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by
    intro i
    -- adjacency at list positions i, i+1
    have hi1 : (i : ℕ) + 1 < d.boxes.length := by
      rw [hlen]; exact Nat.succ_lt_succ i.isLt
    obtain ⟨sa, sb, hsa, hsb, hne⟩ := checkLine_adjacent_opposite hcheck i hi1
    -- rewrite the `List.get` indices to the `Fin (n+1)` membership indices
    have hidxa : (⟨(i : ℕ), Nat.lt_of_succ_lt hi1⟩ : Fin d.boxes.length)
        = Fin.cast hlen.symm i.castSucc := by
      apply Fin.ext; simp
    have hidxb : (⟨(i : ℕ) + 1, hi1⟩ : Fin d.boxes.length)
        = Fin.cast hlen.symm i.succ := by
      apply Fin.ext; simp
    have hma : DIntvProd.DIntv.memR (gLine (p i.castSucc))
        (d.boxes.get ⟨(i : ℕ), Nat.lt_of_succ_lt hi1⟩) := by
      rw [hidxa]; exact hmem i.castSucc
    have hmb : DIntvProd.DIntv.memR (gLine (p i.succ))
        (d.boxes.get ⟨(i : ℕ) + 1, hi1⟩) := by
      rw [hidxb]; exact hmem i.succ
    exact zero_of_checked_pair (hmono (Fin.castSucc_lt_succ (i := i))) hsa hsb hne hma hmb
  choose root hroot_lo hroot_hi hroot_zero using hroot
  refine ⟨List.ofFn root, ?_, ?_, ?_, ?_⟩
  · rw [List.length_ofFn]
  · rw [List.isChain_ofFn]
    intro i hi
    have h1 : root ⟨i, Nat.lt_of_succ_lt hi⟩ < p (Fin.succ ⟨i, Nat.lt_of_succ_lt hi⟩) :=
      hroot_hi _
    have h2 : p (Fin.castSucc ⟨i + 1, hi⟩) < root ⟨i + 1, hi⟩ := hroot_lo _
    have hcast : (Fin.succ ⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (n + 1))
        = Fin.castSucc ⟨i + 1, hi⟩ := by
      apply Fin.ext; simp
    rw [hcast] at h1
    exact lt_trans h1 h2
  · intro t ht
    rw [List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    constructor
    · have hmono0 : p 0 ≤ p i.castSucc := by
        rcases Nat.eq_zero_or_pos i.1 with h0 | hpos
        · have : (i.castSucc : Fin (n+1)) = 0 := by apply Fin.ext; simp [h0]
          rw [this]
        · exact le_of_lt (hmono (by rw [Fin.lt_def]; simpa using hpos))
      linarith [hlo, hmono0, hroot_lo i]
    · have hmonoL : p i.succ ≤ p (Fin.last n) := by
        rcases eq_or_lt_of_le (Fin.le_last i.succ) with h | h
        · rw [h]
        · exact le_of_lt (hmono h)
      linarith [hhi, hmonoL, hroot_hi i]
  · intro t ht
    rw [List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    exact hroot_zero i

end ZetaReflection
