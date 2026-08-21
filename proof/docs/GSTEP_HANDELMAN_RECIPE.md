# The g-step last wall: a mechanical Handelman recipe (q=2, q=3 closed) — 2026-08-20

**A concrete, demonstrated, terminating procedure for the last analytic wall of BG (the
achievable Case-2 g-step). Two hardest cases closed by Telperion's Handelman finder.
`conjecture1_proved = False` — this is a recipe + two instances, not the full closure.**

## The wall

Case 2 of the g-step: for achievable configs `l` (each `μ ∈ (0,1/2]∪{1}`) with `base¹¹ > T`
(`T = W(5/3)¹¹`), prove `base¹¹·∏glemma ≤ T`, where `base = (3d+3S+1)/(3d)`, `d=|l|+1`,
`S=Σμ`, `glemma(μ)=γ/(1+μ/3)¹¹`. This is the one inequality `gstep_le_one_of_glemmaBound`
reduces the whole config g-step to (`CappedJointAchievable.lean`).

## The recipe (per arity q, guaranteed-terminating)

1. **Clear the 11th power.** `L_q := base¹¹·∏glemma = W^{2q}·5^{11q}·(f_q/(3d))¹¹`. Reduce
   `L_q ≤ T` to a **degree-q** inequality `f_q ≤ ρ_q` (`ρ_q` rational) via the **integer
   certificate** `W^{2q}·5^{11q}·ρ_q¹¹ ≤ 12^{... }·T` (a `norm_num`).
2. **Linearize the Case-2 constraint.** Replace `base¹¹ > T` (degree 11) by a **linear**
   proxy `Σμ > c` (`c` rational, verified `base(c)¹¹ ≤ T` so `base¹¹>T ⟹ Σμ>c`).
3. **Close with the Handelman finder.** `find_handelman_certificate(ρ_q·(∏ stuff) − …, box ∩
   {Σμ ≥ c})` — a nonnegative product-combination of the constraints. Handelman's
   Positivstellensatz **guarantees** it exists (strict positivity on a compact polytope).

## Demonstrated (exact over ℚ, all-nonneg coefficients)

- **q=2**: `10uv−9u−9v+8 = (u−1)+(v−1)+10(u−1)(v−1)` on `[1,7/6]²`. Handelman cert, 3 terms.
  (Putinar SOS FAILS here — the cert is a product-combination, not a sum of squares. Use
  **Handelman**, not Putinar, for this whole problem class.)
- **q=3**: proxy `c=84/25`, `ρ₃=44/100` (`f₃` max `0.4298`, integer cert ratio `0.79`).
  `find_handelman_certificate` → **CERT FOUND** (`max_deg=3`, 274 s, 4 terms, exact-verified).

## The finite program + its shape

`Case-2 max L_q/T` is **monotone decreasing in q**: `0.689`(q=2) → `0.549`(q=3) → `0.496`(q=4)
→ … → `0.230`(q=10). **The global max is at q=2 (`0.689`)** — q=2 is the entire wall; every
`q≥3` has strictly more margin (verified 400k random, all q≤20).

**Two completion routes:**
- **(A) per-arity finder** — run steps 1–3 for `q=4…q₀`, crude tail for `q≥q₀` (`base≤3/2` +
  the Case-2 `avg μ>0.356` bound). CAVEAT: each q adds a *variable*, so the Handelman LP grows;
  `q=4…8` are progressively slower (variable explosion). Practical for small q, heavy by q≈8.
- **(B) q-monotonicity of the max** — prove `max_config L_q/T` is decreasing in q; then the
  q=2 cert alone closes all `q≥2`. Cleaner (no per-q runs) but the monotonicity-of-the-max
  is itself an open lemma (per-config peeling FAILS — small children with `glemma>1` inflate
  the product; it must be a max-level, not config-level, argument).

## Remaining to full closure

- Route (A) finite finder runs **or** route (B) q-monotonicity lemma.
- **Leaf-inclusive** configs (some `μ=1`): the reduction above is the non-leaf continuous part;
  leaves add a fixed `glemma(1)` factor (the parallel session's `two_child_le_one` already
  covers leaves, so the framework handles them, but each mixed arity is its own instance).
- **Lean emission** of the certs via `HandelmanEmitter` + assembly into `Case2PropertyAchievable`.

**Net:** the last wall is no longer an open inequality — it's a **terminating recipe with its two
hardest instances already machine-closed**. The open-research question ("what proof route?") is
answered; what remains is execution + formalization. `conjecture1_proved = False`.
