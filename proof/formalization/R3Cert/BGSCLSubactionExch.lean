/-
  Reduce-to-uniform, the MESSAGE half for the deg-3 tail family (2026-09-03).

  Companion to `BGSCLSubactionTail.tail_deg2_sum`.  A deg-`d` hub (`d ≥ 5`, ρwit(node)=0)
  whose `d−1` children are ALL degree-3, with arbitrary messages `μᵢ ∈ [0,1/3]` summing to
  `S`, satisfies `(SUB)`: `log(1+S/d) − F* ≤ Σ ρwit = S/32`.

  Unlike deg-2 (ρ-slope 1/4 dominates 1/(d+S) for all d≥5 ⇒ monotone), the deg-3 slack is
  CONVEX in `S` with an interior minimum for `d ∈ [25,32]`.  Two clean regimes close it:
  * `d ≤ 24`: `d + S0 = (4d−1)/3 ≤ 32`, so the tangent-at-tie slope `1/(d+S0) ≥ 1/32` and the
    slack is monotone down to the tie `S0 = (d−1)/3` — reduce to `tail_all_deg3`.
  * `d ≥ 25`: the crude `log(1+x) ≤ x` gives `log(1+S/d) − F* ≤ S/d − F*`, and
    `S·(1/d − 1/32) ≤ 7/100 ≤ F*` (tight at d=25, S=S0) closes it — no interior extremum needed.

  Kernel-checked vs `R3Cert.BGSCLInduction`.  No `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLSubactionTail

namespace R3Cert
namespace BGSCL

open Real

/-- A clean rational lower bound on `F* = log(621/64)/11`: `7/100 ≤ F*` (actual ≈ 0.2066).
    Via `log(64/621) ≤ 64/621 − 1` ⟹ `log(621/64) ≥ 557/621` ⟹ `F* ≥ 557/6831 ≥ 7/100`. -/
theorem fstar_ge_7_100 : (7 : ℝ) / 100 ≤ FSTAR := by
  rw [FSTAR]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 / 621 by norm_num)
  rw [show (64 : ℝ) / 621 = (621 / 64 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  -- h : -log(621/64) ≤ 64/621 - 1
  linarith

/-- **`tail_deg3_sum`** — reduce-to-uniform, message half for the all-deg-3 tail family.
    For a deg-`d` hub (`d ≥ 5`) whose `d−1` children are all degree-3 with messages summing
    to `S ∈ [0,(d−1)/3]`, `(SUB)` holds: `log(1+S/d) − F* ≤ S/32 = Σ ρwit`.  The worst message
    config is the tie (`S = (d−1)/3`, all `μᵢ = 1/3`) for `d ≤ 24`; for `d ≥ 25` the crude
    tangent plus `F* ≥ 7/100` closes it. -/
theorem tail_deg3_sum (d : ℕ) (hd : 5 ≤ d) (S : ℝ)
    (hSlo : 0 ≤ S) (hShi : S ≤ ((d : ℝ) - 1) / 3) :
    Real.log (1 + S / (d : ℝ)) - FSTAR ≤ S / 32 := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hposS : (0 : ℝ) < 1 + S / (d : ℝ) := by positivity
  rcases Nat.lt_or_ge d 25 with hdle | hdgt
  · -- d ≤ 24: tangent at the tie, monotone reduction to tail_all_deg3.
    have hdle24 : d ≤ 24 := by omega
    have hdleR : (d : ℝ) ≤ 24 := by exact_mod_cast hdle24
    set S0 := ((d : ℝ) - 1) / 3 with hS0def
    have hS0nn : (0 : ℝ) ≤ S0 := by rw [hS0def]; apply div_nonneg (by linarith) (by norm_num)
    have hdS0_pos : (0 : ℝ) < (d : ℝ) + S0 := by linarith
    have hpos0 : (0 : ℝ) < 1 + S0 / (d : ℝ) := by
      have := div_nonneg hS0nn (le_of_lt hd0); linarith
    -- tangent of the concave log at S0
    have hratio : (1 + S / (d : ℝ)) / (1 + S0 / (d : ℝ)) - 1 = (S - S0) / ((d : ℝ) + S0) := by
      field_simp; ring
    have hlogr : Real.log ((1 + S / (d : ℝ)) / (1 + S0 / (d : ℝ))) ≤ (S - S0) / ((d : ℝ) + S0) := by
      rw [← hratio]; exact Real.log_le_sub_one_of_pos (div_pos hposS hpos0)
    rw [Real.log_div (ne_of_gt hposS) (ne_of_gt hpos0)] at hlogr
    have hS0val : (1 : ℝ) + S0 / (d : ℝ) = (4 * (d : ℝ) - 1) / (3 * (d : ℝ)) := by
      rw [hS0def]; field_simp; ring
    rw [hS0val] at hlogr
    have htail := tail_all_deg3 (d : ℝ) (by linarith)
    -- slope: (S−S0)/(d+S0) ≤ (S−S0)/32  (S−S0 ≤ 0, d+S0 ≤ 32)
    have hdS0_le : (d : ℝ) + S0 ≤ 32 := by rw [hS0def]; linarith
    have h1 : (S0 - S) / 32 ≤ (S0 - S) / ((d : ℝ) + S0) :=
      div_le_div_of_nonneg_left (by linarith) hdS0_pos hdS0_le
    have hslope : (S - S0) / ((d : ℝ) + S0) ≤ (S - S0) / 32 := by
      have e1 : (S - S0) / ((d : ℝ) + S0) = -((S0 - S) / ((d : ℝ) + S0)) := by ring
      have e2 : (S - S0) / 32 = -((S0 - S) / 32) := by ring
      rw [e1, e2]; linarith
    have hkey : ((d : ℝ) - 1) / 96 = S0 / 32 := by rw [hS0def]; ring
    -- assemble
    linarith [hlogr, htail, hslope, hkey]
  · -- d ≥ 25: crude tangent log(1+x) ≤ x, then S·(1/d − 1/32) ≤ 7/100 ≤ F*.
    have hdgtR : (25 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdgt
    have hlog : Real.log (1 + S / (d : ℝ)) ≤ S / (d : ℝ) := by
      have := Real.log_le_sub_one_of_pos hposS; linarith
    have hfs := fstar_ge_7_100
    -- S·(1/d − 1/32) ≤ 7/100, i.e. S·(32−d) ≤ (7/100)·32d  after clearing.
    have hbound : S / (d : ℝ) - S / 32 ≤ (7 : ℝ) / 100 := by
      rw [div_sub_div _ _ (ne_of_gt hd0) (by norm_num), div_le_iff₀ (by positivity)]
      -- goal: S*32 - S*d ≤ 7/100 * (d*32)
      rcases lt_or_ge (d : ℝ) 32 with hc | hc
      · -- 24 < d < 32: S ≤ (d−1)/3, and 100(d−1)(32−d) ≤ 672d  (= 100(d−25)(d−1.28) ≥ 0)
        nlinarith [hShi, hSlo, hdgtR, hc, mul_nonneg (by linarith : (0:ℝ) ≤ 32 - (d:ℝ)) hSlo,
          mul_nonneg (by linarith : (0:ℝ) ≤ (d:ℝ) - 25) (by linarith : (0:ℝ) ≤ (d:ℝ) - 1)]
      · -- d ≥ 32: 32 − d ≤ 0, S ≥ 0 ⇒ S(32−d) ≤ 0 ≤ (7/100)·32d
        nlinarith [mul_nonneg hSlo (by linarith : (0:ℝ) ≤ (d:ℝ) - 32), hd0, hSlo]
    linarith [hlog, hbound, hfs]

/-- **`tail_deg4_sum`** — reduce-to-uniform, message half for the all-deg-4 tail family.
    For a deg-`d` hub (`d ≥ 5`) whose `d−1` children are all degree-4 with messages summing to
    `S ∈ [0,(d−1)/4]`, `(SUB)` holds: `log(1+S/d) − F* ≤ S/384 = Σ ρwit`.  Same two regimes as
    `tail_deg3_sum` with the deg-4 ρ-slope `1/384`: tie-tangent for `d ≤ 307`
    (`d+S0 = (5d−1)/4 ≤ 384`), crude tangent + `F* ≥ 7/100` for `d ≥ 308` (worst ≈0.0493 at d=308). -/
theorem tail_deg4_sum (d : ℕ) (hd : 5 ≤ d) (S : ℝ)
    (hSlo : 0 ≤ S) (hShi : S ≤ ((d : ℝ) - 1) / 4) :
    Real.log (1 + S / (d : ℝ)) - FSTAR ≤ S / 384 := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hposS : (0 : ℝ) < 1 + S / (d : ℝ) := by positivity
  rcases Nat.lt_or_ge d 308 with hdle | hdgt
  · -- d ≤ 307: tangent at the tie, monotone reduction to tail_all_deg4.
    have hdle307 : d ≤ 307 := by omega
    have hdleR : (d : ℝ) ≤ 307 := by exact_mod_cast hdle307
    set S0 := ((d : ℝ) - 1) / 4 with hS0def
    have hS0nn : (0 : ℝ) ≤ S0 := by rw [hS0def]; apply div_nonneg (by linarith) (by norm_num)
    have hdS0_pos : (0 : ℝ) < (d : ℝ) + S0 := by linarith
    have hpos0 : (0 : ℝ) < 1 + S0 / (d : ℝ) := by
      have := div_nonneg hS0nn (le_of_lt hd0); linarith
    have hratio : (1 + S / (d : ℝ)) / (1 + S0 / (d : ℝ)) - 1 = (S - S0) / ((d : ℝ) + S0) := by
      field_simp; ring
    have hlogr : Real.log ((1 + S / (d : ℝ)) / (1 + S0 / (d : ℝ))) ≤ (S - S0) / ((d : ℝ) + S0) := by
      rw [← hratio]; exact Real.log_le_sub_one_of_pos (div_pos hposS hpos0)
    rw [Real.log_div (ne_of_gt hposS) (ne_of_gt hpos0)] at hlogr
    have hS0val : (1 : ℝ) + S0 / (d : ℝ) = (5 * (d : ℝ) - 1) / (4 * (d : ℝ)) := by
      rw [hS0def]; field_simp; ring
    rw [hS0val] at hlogr
    have htail := tail_all_deg4 (d : ℝ) (by linarith)
    have hdS0_le : (d : ℝ) + S0 ≤ 384 := by rw [hS0def]; linarith
    have h1 : (S0 - S) / 384 ≤ (S0 - S) / ((d : ℝ) + S0) :=
      div_le_div_of_nonneg_left (by linarith) hdS0_pos hdS0_le
    have hslope : (S - S0) / ((d : ℝ) + S0) ≤ (S - S0) / 384 := by
      have e1 : (S - S0) / ((d : ℝ) + S0) = -((S0 - S) / ((d : ℝ) + S0)) := by ring
      have e2 : (S - S0) / 384 = -((S0 - S) / 384) := by ring
      rw [e1, e2]; linarith
    have hkey : ((d : ℝ) - 1) / 1536 = S0 / 384 := by rw [hS0def]; ring
    linarith [hlogr, htail, hslope, hkey]
  · -- d ≥ 308: crude tangent log(1+x) ≤ x, then S·(1/d − 1/384) ≤ 7/100 ≤ F*.
    have hdgtR : (308 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdgt
    have hlog : Real.log (1 + S / (d : ℝ)) ≤ S / (d : ℝ) := by
      have := Real.log_le_sub_one_of_pos hposS; linarith
    have hfs := fstar_ge_7_100
    have hbound : S / (d : ℝ) - S / 384 ≤ (7 : ℝ) / 100 := by
      rw [div_sub_div _ _ (ne_of_gt hd0) (by norm_num), div_le_iff₀ (by positivity)]
      rcases lt_or_ge (d : ℝ) 384 with hc | hc
      · nlinarith [hShi, hSlo, hdgtR, hc, mul_nonneg (by linarith : (0:ℝ) ≤ 384 - (d:ℝ)) hSlo,
          mul_nonneg (by linarith : (0:ℝ) ≤ (d:ℝ) - 308) (by linarith : (0:ℝ) ≤ (d:ℝ) - 1)]
      · nlinarith [mul_nonneg hSlo (by linarith : (0:ℝ) ≤ (d:ℝ) - 384), hd0, hSlo]
    linarith [hlog, hbound, hfs]

/-! ### Reduce-to-uniform: the counts→single-degree exchange, via the tangent decouple.

  The tail SUB for an ARBITRARY child multiset couples the children ONLY through `S = Σ bYᵢ`
  inside the single `−log(1+S/d)` term.  Applying the concave-log tangent at a reference `Sstar`
  makes that coupling CANCEL: what remains is a per-child SEPARATION.  This dissolves the
  "discrete convexity over multisets" crux into (i) the reference/uniform-family bound `C` at
  `Sstar`, (ii) a per-child bound `ρwit(c) ≥ bY(c)/(d+Sstar) + β`, and (iii) a scalar consistency
  `C ≤ Sstar/(d+Sstar) + (#children)·β`.  The worst multiset is uniform BY CONSTRUCTION (each
  child independently minimises its separated term). -/

/-- **Counts-exchange decouple core.**  Given the reference-family bound `C` at `Sstar` and the
    per-child separation packaged as `hsep`, the tail SUB holds.  The `S`-coupling through
    `−log(1+S/d)` is removed by the tangent `log_tangent`. -/
theorem tail_sub_decouple {d S Sstar R C : ℝ} (hd0 : 0 < d) (hSnn : 0 ≤ S) (hSstar : 0 ≤ Sstar)
    (href : Real.log (1 + Sstar / d) - FSTAR ≤ C)
    (hsep : C + (S - Sstar) / (d + Sstar) ≤ R) :
    Real.log (1 + S / d) - FSTAR ≤ R := by
  have htan := log_tangent hd0 hSnn hSstar
  linarith

/-- Per-child separation sums up: if every child `(bYᵢ, ρᵢ)` obeys `ρᵢ ≥ bYᵢ/c + β`, then
    `(Σ bYᵢ)/c + (#children)·β ≤ Σ ρᵢ`.  (`c = d + Sstar` at the use site.) -/
theorem tail_sep_sum {c β : ℝ} : ∀ (L : List (ℝ × ℝ)),
    (∀ p ∈ L, p.1 / c + β ≤ p.2) →
    (L.map Prod.fst).sum / c + (L.length : ℝ) * β ≤ (L.map Prod.snd).sum
  | [], _ => by simp
  | p :: L', h => by
      have hp := h p (by simp)
      have hIH := tail_sep_sum L' (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_div]
      linarith [hp, hIH]

/-- **Counts→single-degree exchange (reduction).**  The tail SUB for an arbitrary child list `L`
    (children as `(bY, ρwit)` pairs) reduces to: a reference bound `C` at `Sstar`, a UNIFORM
    per-child separation `ρᵢ ≥ bYᵢ/(d+Sstar) + β`, and the scalar consistency
    `C ≤ Sstar/(d+Sstar) + (#L)·β`.  No discrete-convexity argument: the tangent cancels the
    coupling and each child is bounded independently, so the worst config is uniform. -/
theorem tail_sub_of_perchild {d Sstar β C : ℝ} (hd0 : 0 < d) (hSstar : 0 ≤ Sstar)
    (L : List (ℝ × ℝ)) (hbY : ∀ p ∈ L, 0 ≤ p.1)
    (href : Real.log (1 + Sstar / d) - FSTAR ≤ C)
    (hchild : ∀ p ∈ L, p.1 / (d + Sstar) + β ≤ p.2)
    (hconsist : C ≤ Sstar / (d + Sstar) + (L.length : ℝ) * β) :
    Real.log (1 + (L.map Prod.fst).sum / d) - FSTAR ≤ (L.map Prod.snd).sum := by
  have hc : (0 : ℝ) < d + Sstar := by linarith
  have hSnn : 0 ≤ (L.map Prod.fst).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hbY p hp
  have hsep0 := tail_sep_sum L hchild
  have hsep : C + ((L.map Prod.fst).sum - Sstar) / (d + Sstar) ≤ (L.map Prod.snd).sum := by
    rw [sub_div]
    linarith [hsep0, hconsist]
  exact tail_sub_decouple hd0 hSnn hSstar href hsep

end BGSCL
end R3Cert
