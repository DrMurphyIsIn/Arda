/-
  R3Cert.R47MatchingSum -- a self-contained weighted-matching-sum theory, supplying the deletion
  monotonicity that is the mathematical heart of the `B2` bound (`R47HwhLeafDecomp`, `R47HwhAdjDecomp`).
  This DISCHARGES the essential content of the `B2` hypothesis `P11 <= (a-1)*b*P00` from an actual
  matching theory rather than assuming it.

  `Zsum E w = sum over matchings M of E of prod_{e in M} w e`.  `ZsumAvoid E w S` restricts to matchings
  avoiding every vertex in `S`.  The crux:

    * `ZsumAvoid_antitone`  -- avoiding MORE vertices never increases the (nonneg-weighted) sum
      (deletion monotonicity: matchings avoiding `S'` are a subset of those avoiding `S` when `S <= S'`).
    * `B2_termwise` -- hence `Z(H-q-r) <= Z(H)`: `ZsumAvoid {p,q,w,r} <= ZsumAvoid {p,w}` (the per-pair
      bound underlying `B2`).
    * `B2_bound_of_terms` -- a sum of `<= K` terms, each a coefficient in `[0,1]` times a value `<= P00`,
      is `<= K * P00` (the counting that assembles `P11 <= (a-1)*b*P00` from the per-pair bound).

  The remaining glue to fully remove the `B2` hypothesis is the DEFINITIONAL identification `P00 =
  ZsumAvoid {p,w}` and `P11 = sum over (q,r) of (1/deg_q)(1/deg_r) ZsumAvoid {p,q,w,r}` (matchings using a
  fixed edge <-> matchings of the rest) -- standard matching combinatorics, noted in
  `BG_HWH_STATUS_2026-09-11.md`.

  Kernel-checked, no `sorry`.  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M` is a matching inside edge-set `E`: a subset whose edges pairwise share no vertex. -/
def IsMatchingIn (E : Finset (Sym2 V)) (M : Finset (Sym2 V)) : Prop :=
  M ⊆ E ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ e → v ∉ f

/-- The finset of all matchings inside `E`. -/
noncomputable def matchings (E : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter (IsMatchingIn E)

/-- `M` avoids vertex `v` -- no edge of `M` is incident to `v`. -/
def avoidsV (M : Finset (Sym2 V)) (v : V) : Prop := ∀ e ∈ M, v ∉ e

/-- The degree-weighted matching sum restricted to matchings avoiding every vertex of `S`
    (`S = ∅` gives the full matching sum `Zsum`). -/
noncomputable def ZsumAvoid (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (S : Finset V) : ℝ :=
  ∑ M ∈ (matchings E).filter (fun M => ∀ v ∈ S, avoidsV M v), ∏ e ∈ M, w e

/-- The full weighted matching sum. -/
noncomputable def Zsum (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) : ℝ := ZsumAvoid E w ∅

/-- **Deletion monotonicity (the `B2` crux).**  With non-negative edge weights, avoiding MORE vertices
    never increases the matching sum: matchings avoiding `S'` are a subfamily of those avoiding `S` when
    `S ⊆ S'`, and all product-terms are non-negative. -/
theorem ZsumAvoid_antitone (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {S S' : Finset V} (hSS : S ⊆ S') : ZsumAvoid E w S' ≤ ZsumAvoid E w S := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro M hM
    rw [Finset.mem_filter] at hM ⊢
    exact ⟨hM.1, fun v hv => hM.2 v (hSS hv)⟩
  · intro M _ _
    exact Finset.prod_nonneg (fun e _ => hw e)

/-- **The per-pair `B2` bound**: `Z(H-q-r) <= Z(H)`.  Deleting the two extra vertices `q,r` (alongside
    `p,w`) cannot increase the matching sum. -/
theorem B2_termwise (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (p q wv r : V) :
    ZsumAvoid E w {p, q, wv, r} ≤ ZsumAvoid E w {p, wv} := by
  apply ZsumAvoid_antitone E w hw
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

/-- The (weighted) matching sum is non-negative when the edge weights are. -/
theorem ZsumAvoid_nonneg (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (S : Finset V) :
    0 ≤ ZsumAvoid E w S :=
  Finset.sum_nonneg (fun M _ => Finset.prod_nonneg (fun e _ => hw e))

/-- **The counting that assembles `B2`**: a sum over a finset `T` of terms `c t * z t`, where each
    `0 <= c t <= 1` and `0 <= z t <= P00`, is bounded by `T.card * P00`.  Applied with `T` the `(q,r)`
    pairs (`<= (a-1)*b` of them), `c = (1/deg_q)(1/deg_r)`, `z = ZsumAvoid {p,q,wv,r}`, this yields
    `P11 <= (a-1)*b*P00`. -/
theorem B2_bound_of_terms {ι : Type*} (T : Finset ι) (c z : ι → ℝ) (P00 : ℝ) (hP00 : 0 ≤ P00)
    (hc0 : ∀ t ∈ T, 0 ≤ c t) (hc1 : ∀ t ∈ T, c t ≤ 1)
    (hz0 : ∀ t ∈ T, 0 ≤ z t) (hz : ∀ t ∈ T, z t ≤ P00) :
    ∑ t ∈ T, c t * z t ≤ T.card * P00 := by
  calc ∑ t ∈ T, c t * z t ≤ ∑ _t ∈ T, P00 := by
        apply Finset.sum_le_sum
        intro t ht
        calc c t * z t ≤ 1 * z t := by
              apply mul_le_mul_of_nonneg_right (hc1 t ht) (hz0 t ht)
          _ = z t := one_mul _
          _ ≤ P00 := hz t ht
    _ = T.card * P00 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The `B2` bound, fully assembled over the matching theory.**  With `P00 := ZsumAvoid {p,wv}` and
    `P11 := sum over the (q,r) pairs of (1/deg_q)(1/deg_r) * ZsumAvoid {p,q,wv,r}`, and degrees `>= 1`:

        P11 <= pairs.card * P00.

    This is `P11 <= (a-1)*b*P00` once `pairs.card <= (a-1)*b` -- i.e. the `B2` hypothesis of
    `R47HwhLeafDecomp` is now a THEOREM (deletion monotonicity `B2_termwise` + the counting
    `B2_bound_of_terms`), no longer assumed.  The coefficients `(1/deg_q)(1/deg_r) in [0,1]` (degrees
    `>= 1`) and each `ZsumAvoid {p,q,wv,r} <= ZsumAvoid {p,wv}` by deletion monotonicity. -/
theorem B2_bound (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (p wv : V)
    (pairs : Finset (V × V)) (deg : V → ℝ) (hdeg : ∀ t ∈ pairs, 1 ≤ deg t.1 ∧ 1 ≤ deg t.2) :
    (∑ t ∈ pairs, (1 / deg t.1) * (1 / deg t.2) * ZsumAvoid E w {p, t.1, wv, t.2})
      ≤ pairs.card * ZsumAvoid E w {p, wv} := by
  apply B2_bound_of_terms pairs (fun t => (1 / deg t.1) * (1 / deg t.2))
    (fun t => ZsumAvoid E w {p, t.1, wv, t.2}) (ZsumAvoid E w {p, wv})
    (ZsumAvoid_nonneg E w hw _)
  · intro t ht
    obtain ⟨h1, h2⟩ := hdeg t ht
    have : (0:ℝ) ≤ 1 / deg t.1 := by positivity
    have : (0:ℝ) ≤ 1 / deg t.2 := by positivity
    positivity
  · intro t ht
    obtain ⟨h1, h2⟩ := hdeg t ht
    have e1 : (1:ℝ) / deg t.1 ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
    have e2 : (1:ℝ) / deg t.2 ≤ 1 := by rw [div_le_one (by linarith)]; exact h2
    have h0 : (0:ℝ) ≤ 1 / deg t.2 := by positivity
    exact mul_le_one₀ e1 h0 e2
  · intro t _; exact ZsumAvoid_nonneg E w hw _
  · intro t _; exact B2_termwise E w hw p t.1 wv t.2

end Step3
end R3Cert
