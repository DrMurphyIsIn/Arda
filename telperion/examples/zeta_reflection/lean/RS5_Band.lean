/-  RS5_Band.lean -- lane B5: the IVT corollary on Mathlib's `riemannZeta`, and the BAND certificate:
    K certified sign changes along a list of dyadic sample heights give K DISTINCT zeros of
    `riemannZeta` on the critical line, strictly inside the band.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `zeta_zero_of_completed_zero` : `Lambda(1/2+it) = 0 -> riemannZeta(1/2+it) = 0`
        (Mathlib's `riemannZeta_def_of_ne_zero`; `1/2+it ≠ 0`).
      * `exists_zeta_zero_of_signs` (IVT) : `t1 < t2` and opposite certified signs of
        `Re Lambda(1/2+it)` at `t1`, `t2` give `t in (t1, t2)` with `riemannZeta(1/2+it) = 0`
        (continuity of `t -> Re Lambda(1/2+it)` is `XiLineZeros.gLine_continuous`; `Lambda` is real
        on the line, `XiLineZeros.lambda_eq_gLine`; the IVT step is `ZetaReflection.exists_zero_of_sign_change`).
      * `chain_zeros` (generic) : along a `<`-chain of heights with known signs of `gLine`, the number of
        adjacent sign changes `chgBy` is EXACTLY the length of a strictly increasing list of on-line
        zeros strictly inside `(first, last)`.
      * `band_sound` : `bandOK (s0 :: rest) = true` gives a list `xs` with
            xs.length = chgBy Sample.pos (s0 :: rest),  xs strictly increasing,
            every x in xs in (s0.t, (lastOf s0 rest).t),
            completedRiemannZeta(1/2+ix) = 0  and  riemannZeta(1/2+ix) = 0.
        This is (with strict bounds) the on-line half `hLine` of `TuringBand.BandStatement`.
      * `band_sound_finset` : the same as a `Finset ℝ` of card = K.

    ## What this does NOT give (the remaining obligation, stated precisely)

    A band certificate is a LOWER count: at least K zeros of `riemannZeta` with real part 1/2 and
    ordinate in (t_0, t_k).  To conclude that ALL zeros with ordinate in the band lie on the line one
    needs the matching UPPER count -- the number N(t_k) - N(t_0) of zeros of `riemannZeta` in the
    rectangle {0 < Re s < 1, t_0 < Im s < t_k} (with multiplicity) is <= K -- which is the
    argument-principle / Riemann-von Mangoldt (Turing) count.  On this branch that count is NOT
    available; it lives on branch cl/arb3-h1000 (PR #613: ArgChange*, H1000*, AllZerosKernel_h1000)
    and cl/arb4 (PR #620), whose `TuringBand.BandStatement` consumes exactly the `hLine` list produced
    here.  Precisely, the remaining obligation for a band [T0, T1] certified here with K changes is:
        (edge non-vanishing of riemannZeta on the rectangle boundary)
      ∧ (enclosures of the five RvM edge argument-changes pinning the box count to K)
    i.e. the second antecedent of `TuringBand.BandStatement` with n = K.

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_Z

open Complex

namespace RS5

open XiLineZeros

noncomputable section

/-! ## 1. Lambda zeros on the line are riemannZeta zeros -/

theorem line_ne_zero' (t : ℝ) : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- `Lambda(1/2+it) = 0` implies `riemannZeta(1/2+it) = 0`. -/
theorem zeta_zero_of_completed_zero {t : ℝ} (h : completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0) :
    riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [riemannZeta_def_of_ne_zero (line_ne_zero' t), h, zero_div]

/-! ## 2. the IVT corollary -/

/-- One on-line zero of `riemannZeta` strictly inside `(a, b)` from a sign change of `gLine`. -/
theorem exists_zeta_zero_of_sign_change {a b : ℝ} (hab : a < b) (hsign : gLine a * gLine b < 0) :
    ∃ r : ℝ, a < r ∧ r < b ∧ completedRiemannZeta (1 / 2 + (r : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (r : ℂ) * I) = 0 := by
  obtain ⟨r, h1, h2, h3⟩ := ZetaReflection.exists_zero_of_sign_change hab hsign
  exact ⟨r, h1, h2, h3, zeta_zero_of_completed_zero h3⟩

/-- **IVT corollary.**  Opposite signs of `Re completedRiemannZeta(1/2+it)` at `t1 < t2` give a zero
    of Mathlib's `riemannZeta` on the critical line with ordinate in `(t1, t2)`. -/
theorem exists_zeta_zero_of_signs {t1 t2 : ℝ} (h12 : t1 < t2)
    (hs : (0 < (completedRiemannZeta ((1 / 2 : ℂ) + t1 * I)).re ∧
            (completedRiemannZeta ((1 / 2 : ℂ) + t2 * I)).re < 0) ∨
          ((completedRiemannZeta ((1 / 2 : ℂ) + t1 * I)).re < 0 ∧
            0 < (completedRiemannZeta ((1 / 2 : ℂ) + t2 * I)).re)) :
    ∃ t ∈ Set.Ioo t1 t2, riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hsign : gLine t1 * gLine t2 < 0 := by
    unfold gLine
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_neg_of_pos_of_neg h1 h2
    · exact mul_neg_of_neg_of_pos h1 h2
  obtain ⟨r, h1, h2, _, h4⟩ := exists_zeta_zero_of_sign_change h12 hsign
  exact ⟨r, ⟨h1, h2⟩, h4⟩

/-! ## 3. the generic chain lemma -/

section Generic

variable {α : Type} (tt : α → ℝ) (sg : α → Bool)

theorem le_lastOf : ∀ (a : α) (l : List α), List.IsChain (fun x y => tt x < tt y) (a :: l) →
    tt a ≤ tt (lastOf a l)
  | a, [], _ => le_refl _
  | a, b :: l, h => by
    rw [List.isChain_cons_cons] at h
    exact le_trans h.1.le (le_lastOf b l h.2)

theorem sign_mul_neg {x y : ℝ} {bx b2 : Bool} (hne : (bx == b2) = false)
    (hx : (bx = true → 0 < x) ∧ (bx = false → x < 0))
    (hy : (b2 = true → 0 < y) ∧ (b2 = false → y < 0)) : x * y < 0 := by
  cases bx <;> cases b2 <;> simp at hne
  · exact mul_neg_of_neg_of_pos (hx.2 rfl) (hy.1 rfl)
  · exact mul_neg_of_pos_of_neg (hx.1 rfl) (hy.2 rfl)

/-- **The chain lemma.**  Along a strictly increasing chain of heights with certified signs of
    `gLine`, the number of adjacent sign changes is the length of a strictly increasing list of
    on-line zeros (of `Lambda` and of `riemannZeta`) strictly inside `(first, last)`. -/
theorem chain_zeros : ∀ (a : α) (l : List α),
    List.IsChain (fun x y => tt x < tt y) (a :: l) →
    (∀ p ∈ a :: l, (sg p = true → 0 < gLine (tt p)) ∧ (sg p = false → gLine (tt p) < 0)) →
    ∃ xs : List ℝ, xs.length = chgBy sg (a :: l) ∧ xs.IsChain (· < ·) ∧
      (∀ x ∈ xs, tt a < x ∧ x < tt (lastOf a l)) ∧
      (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
        riemannZeta (1 / 2 + (x : ℂ) * I) = 0)
  | a, [], _, _ => ⟨[], rfl, List.isChain_nil, by simp, by simp⟩
  | a, b :: l, hc, hs => by
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hab, hc'⟩ := hc
    obtain ⟨xs, hlen, hch, hb, hz⟩ :=
      chain_zeros b l hc' (fun p hp => hs p (List.mem_cons_of_mem a hp))
    have hlast : lastOf a (b :: l) = lastOf b l := rfl
    have hchg : chgBy sg (a :: b :: l) = (if sg a == sg b then 0 else 1) + chgBy sg (b :: l) := rfl
    rw [hlast, hchg]
    by_cases heq : (sg a == sg b) = true
    · refine ⟨xs, by rw [hlen, if_pos heq, zero_add], hch, ?_, hz⟩
      intro x hx
      exact ⟨lt_trans hab (hb x hx).1, (hb x hx).2⟩
    · have hne : (sg a == sg b) = false := by simpa using heq
      have hsg := sign_mul_neg hne (hs a List.mem_cons_self)
        (hs b (List.mem_cons_of_mem a List.mem_cons_self))
      obtain ⟨r, hr1, hr2, hr3, hr4⟩ := exists_zeta_zero_of_sign_change hab hsg
      refine ⟨r :: xs, ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, hlen, if_neg heq]; ring
      · rw [List.isChain_cons]
        refine ⟨?_, hch⟩
        intro y hy
        have hy' : y ∈ xs := List.mem_of_mem_head? hy
        exact lt_trans hr2 (hb y hy').1
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hr1, lt_of_lt_of_le hr2 (le_lastOf tt b l hc')⟩
        · exact ⟨lt_trans hab (hb x hx).1, (hb x hx).2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hr3, hr4⟩
        · exact hz x hx

end Generic

/-! ## 4. the band certificate -/

theorem ltH_real {s s' : Sample} (h : ltH s s' = true) : s.t < s'.t := by
  unfold ltH at h
  rw [decide_eq_true_eq] at h
  have h' : ((s.tn * 2 ^ s'.tq : ℕ) : ℝ) < ((s'.tn * 2 ^ s.tq : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  unfold Sample.t
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact h'

theorem bandOK_facts : ∀ (s : Sample) (rest : List Sample), bandOK (s :: rest) = true →
    List.IsChain (fun x y => Sample.t x < Sample.t y) (s :: rest) ∧
      ∀ p ∈ s :: rest, sampleOK p = true
  | s, [], h => ⟨List.isChain_singleton s, by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact h⟩
  | s, s' :: rest, h => by
    have h' : (sampleOK s && ltH s s' && bandOK (s' :: rest)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := bandOK_facts s' rest h3
    refine ⟨List.isChain_cons_cons.mpr ⟨ltH_real h2, ih1⟩, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h1
    · exact ih2 p hp

/-- **The band certificate (soundness).**  If the kernel accepts the sample list, the number `K` of
    adjacent sign changes yields `K` DISTINCT zeros of `riemannZeta` on the critical line, listed in
    strictly increasing order, with ordinates STRICTLY inside `(t_0, t_k)`. -/
theorem band_sound (s0 : Sample) (rest : List Sample) (h : bandOK (s0 :: rest) = true) :
    ∃ xs : List ℝ, xs.length = chgBy Sample.pos (s0 :: rest) ∧ xs.IsChain (· < ·) ∧
      (∀ x ∈ xs, s0.t < x ∧ x < (lastOf s0 rest).t) ∧
      (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
        riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := by
  obtain ⟨hc, hs⟩ := bandOK_facts s0 rest h
  exact chain_zeros Sample.t Sample.pos s0 rest hc (fun p hp => sampleOK_sign (hs p hp))

/-- **The band certificate as a Finset**: `card = K` distinct on-line zeros of `riemannZeta`. -/
theorem band_sound_finset (s0 : Sample) (rest : List Sample) (h : bandOK (s0 :: rest) = true) :
    ∃ S : Finset ℝ, S.card = chgBy Sample.pos (s0 :: rest) ∧
      ∀ x ∈ S, s0.t < x ∧ x < (lastOf s0 rest).t ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := by
  obtain ⟨xs, hlen, hch, hb, hz⟩ := band_sound s0 rest h
  have hnd : xs.Nodup := (hch.pairwise).imp (fun hxy => ne_of_lt hxy)
  refine ⟨xs.toFinset, by rw [List.toFinset_card_of_nodup hnd, hlen], ?_⟩
  intro x hx
  rw [List.mem_toFinset] at hx
  exact ⟨(hb x hx).1, (hb x hx).2, (hz x hx).2⟩

/-! ## 5. band results as a Prop, gluing, and the three output shapes -/

/-- `K` distinct on-line zeros strictly inside `(T0, T1)`, as a strictly increasing list. -/
def BandZeros (T0 T1 : ℝ) (K : ℕ) : Prop :=
  ∃ xs : List ℝ, xs.length = K ∧ xs.IsChain (· < ·) ∧ (∀ x ∈ xs, T0 < x ∧ x < T1) ∧
    (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (x : ℂ) * I) = 0)

theorem bandZeros_of_ok (s0 : Sample) (rest : List Sample) (h : bandOK (s0 :: rest) = true) :
    BandZeros s0.t (lastOf s0 rest).t (chgBy Sample.pos (s0 :: rest)) :=
  band_sound s0 rest h

/-- **Gluing** two adjacent bands that share the endpoint `b`. -/
theorem BandZeros.glue {a b c : ℝ} {K1 K2 : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : BandZeros a b K1) (h2 : BandZeros b c K2) : BandZeros a c (K1 + K2) := by
  obtain ⟨xs, hl, hc, hb, hz⟩ := h1
  obtain ⟨ys, hl', hc', hb', hz'⟩ := h2
  refine ⟨xs ++ ys, by rw [List.length_append, hl, hl'], ?_, ?_, ?_⟩
  · rw [List.isChain_iff_pairwise] at hc hc' ⊢
    rw [List.pairwise_append]
    exact ⟨hc, hc', fun x hx y hy => lt_trans (hb x hx).2 (hb' y hy).1⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hb x hx).1, lt_of_lt_of_le (hb x hx).2 hbc⟩
    · exact ⟨lt_of_le_of_lt hab (hb' x hx).1, (hb' x hx).2⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hz x hx
    · exact hz' x hx

/-- Widening the band. -/
theorem BandZeros.mono {a b a' b' : ℝ} {K : ℕ} (h : BandZeros a b K) (ha : a' ≤ a) (hb : b ≤ b') :
    BandZeros a' b' K := by
  obtain ⟨xs, hl, hc, hbd, hz⟩ := h
  exact ⟨xs, hl, hc, fun x hx => ⟨lt_of_le_of_lt ha (hbd x hx).1, lt_of_lt_of_le (hbd x hx).2 hb⟩, hz⟩

/-- Output shape 1: a strictly increasing list of `K` zeros of Mathlib's `riemannZeta` on the line. -/
theorem BandZeros.zeta {a b : ℝ} {K : ℕ} (h : BandZeros a b K) :
    ∃ xs : List ℝ, xs.length = K ∧ xs.IsChain (· < ·) ∧ (∀ x ∈ xs, a < x ∧ x < b) ∧
      (∀ x ∈ xs, riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := by
  obtain ⟨xs, hl, hc, hb, hz⟩ := h
  exact ⟨xs, hl, hc, hb, fun x hx => (hz x hx).2⟩

/-- Output shape 2: a `Finset` of card `K` of on-line zero ordinates of `riemannZeta`. -/
theorem BandZeros.finset {a b : ℝ} {K : ℕ} (h : BandZeros a b K) :
    ∃ S : Finset ℝ, S.card = K ∧ ∀ x ∈ S, a < x ∧ x < b ∧ riemannZeta (1 / 2 + (x : ℂ) * I) = 0 := by
  obtain ⟨xs, hlen, hch, hb, hz⟩ := h
  have hnd : xs.Nodup := (hch.pairwise).imp (fun hxy => ne_of_lt hxy)
  refine ⟨xs.toFinset, by rw [List.toFinset_card_of_nodup hnd, hlen], ?_⟩
  intro x hx
  rw [List.mem_toFinset] at hx
  exact ⟨(hb x hx).1, (hb x hx).2, (hz x hx).2⟩

/-- Output shape 3: VERBATIM the `hLine` antecedent of `TuringBand.BandStatement _ _ a b K ...`. -/
theorem BandZeros.hLine {a b : ℝ} {K : ℕ} (h : BandZeros a b K) :
    ∃ xs : List ℝ, xs.length = K ∧ xs.IsChain (· < ·) ∧
      (∀ t ∈ xs, a ≤ t ∧ t ≤ b) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  obtain ⟨xs, hl, hc, hb, hz⟩ := h
  exact ⟨xs, hl, hc, fun x hx => ⟨(hb x hx).1.le, (hb x hx).2.le⟩, fun x hx => (hz x hx).1⟩

end

end RS5
