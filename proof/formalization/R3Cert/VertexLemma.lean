import R3Cert.CappedJointConfig

/-!
  # Vertex-lemma seed: the two-point spreading exchange

  Prototype for the heterogeneous → canonical-family reduction of
  `docs/design/HETERO_REDUCTION_SCOPING_20260821.md` (PR #37).  The reduction
  rests on: maximizing `∏ glemma(μ_i)` over a fixed-sum box slice is attained at a
  vertex, because `log glemma` is convex — so at fixed sum, SPREADING two children
  never decreases the glemma product.

  The engine of that vertex lemma is the two-point exchange below, and it reduces
  to the pure-algebra fact `lo·hi ≤ ((lo+hi)/2)²` (= `sq_nonneg (lo−hi)`): no
  convexity library, one `nlinarith` + power monotonicity.  `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore

/-- The base of `glemma` is strictly positive: `0 < 1 + μ/3` for `0 ≤ μ`. -/
theorem one_add_third_pos {μ : ℚ} (hμ : 0 ≤ μ) : 0 < 1 + μ / 3 := by linarith

/-- **Two-point spread (the vertex-lemma engine).**  At fixed sum, spreading two
    children never decreases the `glemma` product:
    `glemma ((lo+hi)/2)² ≤ glemma lo · glemma hi` for `lo, hi ≥ 0`.
    Equivalently: `log glemma` is convex.  Proof: `(1+lo/3)(1+hi/3) ≤ (1+m/3)²`
    from `lo·hi ≤ m²`, then 11th-power monotonicity + the decreasing `a ↦ 1/a`. -/
theorem glemma_two_point_spread (lo hi : ℚ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    glemma ((lo + hi) / 2) ^ 2 ≤ glemma lo * glemma hi := by
  set m := (lo + hi) / 2 with hm
  have hmnn : 0 ≤ m := by rw [hm]; linarith
  have plo : (0 : ℚ) < 1 + lo / 3 := one_add_third_pos hlo
  have phi : (0 : ℚ) < 1 + hi / 3 := one_add_third_pos hhi
  have pm : (0 : ℚ) < 1 + m / 3 := one_add_third_pos hmnn
  -- the algebraic heart: (1+lo/3)(1+hi/3) ≤ (1+m/3)²  (⇐ lo·hi ≤ m²)
  have key : (1 + lo / 3) * (1 + hi / 3) ≤ (1 + m / 3) ^ 2 := by
    rw [hm]; nlinarith [sq_nonneg (lo - hi)]
  -- denominators: (1+lo/3)^11 (1+hi/3)^11 ≤ ((1+m/3)^11)^2
  have hden : (1 + lo / 3) ^ 11 * (1 + hi / 3) ^ 11 ≤ ((1 + m / 3) ^ 11) ^ 2 := by
    calc (1 + lo / 3) ^ 11 * (1 + hi / 3) ^ 11
        = ((1 + lo / 3) * (1 + hi / 3)) ^ 11 := by rw [mul_pow]
      _ ≤ ((1 + m / 3) ^ 2) ^ 11 := by gcongr
      _ = ((1 + m / 3) ^ 11) ^ 2 := by ring
  -- unfold glemma; both sides are `G²` over a positive power (normalize `G*G → G²`),
  -- so `gcongr` reduces to the denominator bound `hden`.
  unfold glemma
  rw [div_pow, div_mul_div_comm, ← pow_two (W ^ 2 * (5 / 3) ^ 11)]
  gcongr

end R3Cert.CappedJointConfig
