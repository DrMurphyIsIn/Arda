# SONC circuit-polynomial certificate — status & Lean-emit design (2026-08-21)

From [COVERAGE_GAPS_2026-08-21](COVERAGE_GAPS_2026-08-21.md) rank #3: sparse
positivity INDEPENDENT of SOS. Reaches nonneg-not-SOS polynomials (Motzkin) as a
single circuit, no SDP, sparsity-preserving.

## Shipped (this PR) — exact finder + verifier, fully tested

`telperion/sonc.py` (Iliman–de Wolff circuit polynomials):
- `find_circuit_certificate(p, syms)` — detect a single circuit polynomial
  (even-exponent positive-coeff simplex vertices + one interior term), solve the
  exact rational barycentric λ, and rationalize the AM-GM: with λⱼ = pⱼ/q,
  `|c_β|^q ≤ Πⱼ (cⱼ/λⱼ)^{pⱼ}` — an EXACT rational inequality (the irrational
  circuit number Θ is cleared by the q-th power). Returns None if not a single
  circuit or if `|c_β|^q > Θ^q` (not nonnegative).
- `verify_circuit_certificate` — independent exact re-check: vertex evenness +
  coeffs, barycentric identity, integer rationalization, and the load-bearing
  inequality.
- CLI `telperion sonc "x**4*y**2 + x**2*y**4 + 1 - 3*x**2*y**2"`.

Tested (`tests/test_sonc.py`): Motzkin (tight, 27≤27), a strict circuit (8≤27),
a non-nonnegative circuit (rejected, |c_β|=4>Θ=3), tampered-bound rejection.
All exact rationals — no SDP, no Lean needed for this layer.

## Follow-up (CI-gated) — the Lean emitter

The certificate reduces nonnegativity to (a) each vertex term `cⱼ x^{α(j)} ≥ 0`
(monomial square: `positivity`), and (b) the weighted AM-GM tying the interior
term to the vertices. Emission shape:

```lean
theorem p_nonneg : ∀ x y : ℝ, 0 ≤ <p> := by
  intro x y
  -- weighted AM-GM: for the circuit exponents/weights,
  --   |c_β| · (x^β)  ≤  Σⱼ (λⱼ·⟨rationalized⟩) · x^{α(j)}
  -- instantiated at the exact λⱼ = pⱼ/q, cleared to the polynomial identity
  -- |c_β|^q ≤ Πⱼ (cⱼ/λⱼ)^{pⱼ} (a norm_num rational fact), then positivity.
  nlinarith [sq_nonneg ..., <AM-GM instance>, <the exact rational bound>]
```

The open question (why CI-gated): the clean Lean form of the **weighted AM-GM
step** at rational weights. Options to settle in CI:
1. A reusable `telperion` lemma: weighted AM-GM for k nonnegative reals at
   rational weights (prove once, instantiate per circuit). Mathlib has
   `inner_le_nnorm`/`Real.inner_le_weight_mul_Lp_of_norm_le`-style and
   `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` / `Real.geom_mean_le_arith_mean3_weighted`
   — the 3-weight arithmetic-geometric-mean lemma directly covers 3-vertex
   circuits (Motzkin). Check the general-k form.
2. Failing a general lemma, emit the cleared polynomial identity + `nlinarith`
   with the monomial-square hints (works for small circuits; may not scale).

Pick the first that compiles green. This machine cannot build Lean (see memory
"System crashes = SoC watchdog panics"), so no SONC Lean is claimed to compile
until CI proves it; the finder/verifier ship now.

Future: a general SONC *decomposition* finder (sum of circuits via an LP over the
Newton polytope) to handle polynomials that are sums of several circuits, not a
single one.
