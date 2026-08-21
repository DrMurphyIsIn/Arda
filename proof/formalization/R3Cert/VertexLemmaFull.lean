import R3Cert.VertexLemma

/-!
  # The full vertex lemma for the heterogeneous master inequality

  Companion to `docs/design/HETERO_REDUCTION_SCOPING_20260821.md` (the "#37 scoped
  route") and the seed `VertexLemma.lean`.  The route replaces the broken
  "reduce-to-homogeneous" chain by the standard fact:

  > maximizing `∏ glemma(μ_i)` over a fixed-sum box slice `{μ_i ∈ [0, 1/2]}` is
  > attained at a VERTEX (all-but-one coordinate at the bound `1/2`),

  because `log glemma` is convex, so at fixed sum SPREADING two children never
  decreases the `glemma` product.  This file turns the exact-midpoint seed
  `glemma_two_point_spread` into (1) a general two-point spread and (2) the
  list-level vertex bound

  > `glemma a · ∏_{c∈l} glemma c ≤ glemma(1/2)^(|l|) · glemma(a + Σl − |l|/2)`

  when every coordinate lies in `[0, 1/2]` and the residual `a + Σl − |l|/2 ≥ 0`.
  The one free coordinate `a` carries the residual; the `l`-coordinates are pushed
  to the bound `1/2`.  Everything is over `ℚ`.

  This is the "only genuinely new mathematics" the scoping doc names, and it is the
  standard convexity fact used in the CORRECT direction (the same convexity that
  killed the merging/below-average chain).  `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore

/-- Positivity of the `glemma` numerator `γ = W²(5/3)¹¹`. -/
theorem gamma_pos : (0 : ℚ) < W ^ 2 * (5 / 3) ^ 11 := by
  unfold W; norm_num

/-- **General two-point spread (the vertex-lemma engine, sum-preserving form).**
    If `a + b = c + d`, the pair `{c,d}` is at-least-as-spread as `{a,b}` (encoded by
    the product inequality `c·d ≤ a·b`, i.e. more spread ⇒ smaller product), and all
    four arguments keep the `glemma` denominator positive, then
    `glemma a · glemma b ≤ glemma c · glemma d`.

    Proof: with `a+b=c+d`, `(1+c/3)(1+d/3) − (1+a/3)(1+b/3) = (c·d − a·b)/9 ≤ 0`, so
    the `c,d` denominator is smaller; 11th-power monotonicity + `x ↦ 1/x` antitone. -/
theorem glemma_spread (a b c d : ℚ)
    (hsum : a + b = c + d) (hprod : c * d ≤ a * b)
    (ha : -3 < a) (hb : -3 < b) (hc : -3 < c) (hd : -3 < d) :
    glemma a * glemma b ≤ glemma c * glemma d := by
  have Da : (0 : ℚ) < 1 + a / 3 := by linarith
  have Db : (0 : ℚ) < 1 + b / 3 := by linarith
  have Dc : (0 : ℚ) < 1 + c / 3 := by linarith
  have Dd : (0 : ℚ) < 1 + d / 3 := by linarith
  -- denominator factors: the `c,d` product is the smaller one
  have hcd_le_ab : (1 + c / 3) * (1 + d / 3) ≤ (1 + a / 3) * (1 + b / 3) := by
    have : (1 + a / 3) * (1 + b / 3) - (1 + c / 3) * (1 + d / 3)
        = (a * b - c * d) / 9 + (a + b - (c + d)) / 3 := by ring
    nlinarith [hsum, hprod]
  have hcdp : (0 : ℚ) < (1 + c / 3) * (1 + d / 3) := mul_pos Dc Dd
  have habp : (0 : ℚ) < (1 + a / 3) * (1 + b / 3) := mul_pos Da Db
  -- 11th-power monotonicity on the denominators
  have hden : ((1 + c / 3) * (1 + d / 3)) ^ 11 ≤ ((1 + a / 3) * (1 + b / 3)) ^ 11 := by
    gcongr
  have hdenc : (0 : ℚ) < ((1 + c / 3) * (1 + d / 3)) ^ 11 := by positivity
  -- rewrite both glemma products as `γ² / denom¹¹`
  have hG : (0 : ℚ) < W ^ 2 * (5 / 3) ^ 11 := gamma_pos
  unfold glemma
  rw [div_mul_div_comm, div_mul_div_comm, ← pow_two (W ^ 2 * (5 / 3) ^ 11),
      ← mul_pow, ← mul_pow]
  apply div_le_div_of_nonneg_left (by positivity) hdenc hden

/-- **Push-to-bound exchange.**  For `a, b ∈ [0, 1/2]`, replacing the pair `(a,b)`
    by `(1/2, a+b−1/2)` (push `b` up to the bound, transfer the excess to the other
    coordinate) never decreases the `glemma` product:
    `glemma a · glemma b ≤ glemma (1/2) · glemma (a + b − 1/2)`.

    The product inequality feeding `glemma_spread` is
    `(1/2)(a+b−1/2) ≤ a·b ⇔ (1/2−a)(1/2−b) ≥ 0`, automatic on `[0,1/2]`. -/
theorem glemma_push_to_bound (a b : ℚ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1/2) :
    glemma a * glemma b ≤ glemma (1/2) * glemma (a + b - 1/2) := by
  apply glemma_spread a b (1/2) (a + b - 1/2)
  · ring
  · nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ 1/2 - a) (by linarith : (0:ℚ) ≤ 1/2 - b)]
  · linarith
  · linarith
  · norm_num
  · linarith

/-- Auxiliary: for a list of children each `≤ 1/2`, the sum is `≤ |l|/2`. -/
theorem sum_le_half_length (l : List ℚ) (hl : ∀ c ∈ l, c ≤ 1/2) :
    l.sum ≤ (l.length : ℚ) / 2 := by
  induction l with
  | nil => simp
  | cons x s ihs =>
    have hx : x ≤ 1/2 := hl x (by simp)
    have hs : ∀ c ∈ s, c ≤ 1/2 := fun c hc => hl c (List.mem_cons_of_mem _ hc)
    have hrec := ihs hs
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- **The vertex bound (accumulator form).**  With one free coordinate `a` and a list
    `l` of children, all in `[0, 1/2]`, and a nonnegative residual
    `a + Σl − |l|/2 ≥ 0`, the `glemma` product is bounded by the vertex configuration
    (every `l`-coordinate pushed to `1/2`, the free coordinate carrying the residual):

    `glemma a · ∏_{c∈l} glemma c ≤ glemma(1/2)^|l| · glemma (a + Σl − |l|/2)`.

    Proof: list induction on `l`, each step the push-to-bound exchange
    `glemma_push_to_bound`, with the invariant that the running free coordinate
    stays in `[0, 1/2]` (`≤ 1/2` since a pair of `[0,1/2]` values gives `a+b−1/2 ≤ 1/2`;
    `≥ 0` because it dominates the constant residual `≥ 0`). -/
theorem vertex_bound (a : ℚ) (l : List ℚ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hl : ∀ c ∈ l, 0 ≤ c ∧ c ≤ 1/2)
    (hres : 0 ≤ a + l.sum - (l.length : ℚ) / 2) :
    glemma a * (l.map glemma).prod
      ≤ glemma (1/2) ^ l.length * glemma (a + l.sum - (l.length : ℚ) / 2) := by
  induction l generalizing a with
  | nil =>
    simp only [List.map_nil, List.prod_nil, mul_one, List.length_nil, pow_zero,
               one_mul, List.sum_nil, Nat.cast_zero]
    norm_num
  | cons b t ih =>
    -- unpack hypotheses on the head `b`
    have hb : 0 ≤ b ∧ b ≤ 1/2 := hl b (by simp)
    have hb0 : 0 ≤ b := hb.1
    have hb1 : b ≤ 1/2 := hb.2
    have htl : ∀ c ∈ t, 0 ≤ c ∧ c ≤ 1/2 := fun c hc => hl c (List.mem_cons_of_mem _ hc)
    have htl2 : ∀ c ∈ t, c ≤ 1/2 := fun c hc => (htl c hc).2
    -- the new free coordinate after pushing `b` to the bound
    set a' := a + b - 1/2 with ha'def
    -- new free coordinate stays in [0,1/2]
    have ha'1 : a' ≤ 1/2 := by rw [ha'def]; linarith
    -- residual is invariant: (a') + Σt − |t|/2 = a + Σ(b::t) − |b::t|/2
    have hsum_cons : (b :: t).sum = b + t.sum := by simp [List.sum_cons]
    have hlen_cons : ((b :: t).length : ℚ) = (t.length : ℚ) + 1 := by
      push_cast [List.length_cons]; ring
    have hres_eq : a' + t.sum - (t.length : ℚ) / 2
        = a + (b :: t).sum - ((b :: t).length : ℚ) / 2 := by
      rw [ha'def, hsum_cons, hlen_cons]; ring
    -- the running free coordinate dominates the residual: a' ≥ residual ≥ 0
    have hsum_t_le : t.sum ≤ (t.length : ℚ) / 2 := sum_le_half_length t htl2
    have hres0' : 0 ≤ a' + t.sum - (t.length : ℚ) / 2 := by rw [hres_eq]; exact hres
    have ha'0 : 0 ≤ a' := by
      have hrw : a' = (a' + t.sum - (t.length : ℚ) / 2) + ((t.length : ℚ) / 2 - t.sum) := by
        ring
      rw [hrw]; linarith [hres0', hsum_t_le]
    -- push-to-bound on the pair (a, b): glemma a · glemma b ≤ glemma(1/2) · glemma a'
    have hpush : glemma a * glemma b ≤ glemma (1/2) * glemma a' :=
      glemma_push_to_bound a b ha0 ha1 hb0 hb1
    -- apply IH to the new free coordinate a' and the tail t
    have hIH := ih a' ha'0 ha'1 htl hres0'
    -- glemma nonnegativities for the multiplicative combination
    have hg12 : 0 ≤ glemma (1/2) := glemma_nonneg (by norm_num)
    have hgb : 0 ≤ glemma b := glemma_nonneg hb0
    have hprodt : 0 ≤ (t.map glemma).prod :=
      R3Cert.ProdBounds.map_prod_nonneg t glemma (fun c hc => glemma_nonneg (htl c hc).1)
    -- assemble: glemma a · (glemma b · ∏t)
    --   = (glemma a · glemma b) · ∏t
    --   ≤ (glemma(1/2) · glemma a') · ∏t          [push]
    --   = glemma(1/2) · (glemma a' · ∏t)
    --   ≤ glemma(1/2) · (glemma(1/2)^|t| · glemma(res))   [IH]
    calc glemma a * ((b :: t).map glemma).prod
        = (glemma a * glemma b) * (t.map glemma).prod := by
          simp only [List.map_cons, List.prod_cons]; ring
      _ ≤ (glemma (1/2) * glemma a') * (t.map glemma).prod := by
          apply mul_le_mul_of_nonneg_right hpush hprodt
      _ = glemma (1/2) * (glemma a' * (t.map glemma).prod) := by ring
      _ ≤ glemma (1/2) * (glemma (1/2) ^ t.length * glemma (a' + t.sum - (t.length : ℚ) / 2)) := by
          apply mul_le_mul_of_nonneg_left hIH hg12
      _ = glemma (1/2) ^ (b :: t).length
            * glemma (a + (b :: t).sum - ((b :: t).length : ℚ) / 2) := by
          rw [hres_eq]
          simp only [List.length_cons]
          rw [pow_succ]
          ring

/-- **Vertex bound, cons form (the scoping doc's stated target).**  For a nonempty
    list `a :: l` of above-knee children, all in `[0, 1/2]`, with nonnegative residual,
    the `glemma` product over all `|l|+1` children is bounded by the vertex config with
    the `|l|` tail children pushed to `1/2` and the head carrying the residual:

    `∏_{c ∈ a::l} glemma c ≤ glemma(1/2)^|l| · glemma(a + Σl − |l|/2)`.

    This is `∏ glemma ≤ glemma(1/2)^(n−1) · glemma(sum − (n−1)/2)` with `n = |l|+1`,
    i.e. exactly the "clean formalization" target of
    `docs/design/HETERO_REDUCTION_SCOPING_20260821.md` (empirically validated by
    `hetero_family_scan.VertexReport`). -/
theorem vertex_bound_cons (a : ℚ) (l : List ℚ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hl : ∀ c ∈ l, 0 ≤ c ∧ c ≤ 1/2)
    (hres : 0 ≤ a + l.sum - (l.length : ℚ) / 2) :
    ((a :: l).map glemma).prod
      ≤ glemma (1/2) ^ l.length * glemma (a + l.sum - (l.length : ℚ) / 2) := by
  have := vertex_bound a l ha0 ha1 hl hres
  simpa [List.map_cons, List.prod_cons] using this

end R3Cert.CappedJointConfig
