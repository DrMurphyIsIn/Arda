/-  RS5_BandSharp.lean -- lane B5, RSC0 Phase 3: the band certificate over the SHARPENED predicate
    `RS5.bandOK'` (margin (3/5) t^(-3/4), every sample at t >= 4250).  Theorems BESIDE `RS5_Band`
    (imported read-only; the generic `chain_zeros`, `ltH_real`, `BandZeros` and its gluing are reused).

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `band_sound'` : `bandOK' (s0 :: rest) = true` gives a strictly increasing list of
        `chgBy Sample.pos (s0 :: rest)` on-line zeros of `riemannZeta` strictly inside
        `(s0.t, (lastOf s0 rest).t)` -- the same conclusion as `band_sound`;
      * `bandZeros_of_ok'` : the same as `BandZeros`, so sharpened chunks glue with old ones
        (`BandZeros.glue`).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/
import RS5_ZSharp
import RS5_Band

open Complex

namespace RS5

noncomputable section

theorem bandOK'_facts : ∀ (s : Sample) (rest : List Sample), bandOK' (s :: rest) = true →
    List.IsChain (fun x y => Sample.t x < Sample.t y) (s :: rest) ∧
      ∀ p ∈ s :: rest, sampleOK' p = true
  | s, [], h => ⟨List.isChain_singleton s, by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact h⟩
  | s, s' :: rest, h => by
    have h' : (sampleOK' s && ltH s s' && bandOK' (s' :: rest)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := bandOK'_facts s' rest h3
    refine ⟨List.isChain_cons_cons.mpr ⟨ltH_real h2, ih1⟩, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h1
    · exact ih2 p hp

/-- **The band certificate, sharpened margin (soundness).** -/
theorem band_sound' (s0 : Sample) (rest : List Sample) (h : bandOK' (s0 :: rest) = true) :
    ∃ xs : List ℝ, xs.length = chgBy Sample.pos (s0 :: rest) ∧ xs.IsChain (· < ·) ∧
      (∀ x ∈ xs, s0.t < x ∧ x < (lastOf s0 rest).t) ∧
      (∀ x ∈ xs, completedRiemannZeta (1 / 2 + (x : ℂ) * I) = 0 ∧
        riemannZeta (1 / 2 + (x : ℂ) * I) = 0) := by
  obtain ⟨hc, hs⟩ := bandOK'_facts s0 rest h
  exact chain_zeros Sample.t Sample.pos s0 rest hc (fun p hp => sampleOK'_sign (hs p hp))

theorem bandZeros_of_ok' (s0 : Sample) (rest : List Sample) (h : bandOK' (s0 :: rest) = true) :
    BandZeros s0.t (lastOf s0 rest).t (chgBy Sample.pos (s0 :: rest)) :=
  band_sound' s0 rest h

end

end RS5
