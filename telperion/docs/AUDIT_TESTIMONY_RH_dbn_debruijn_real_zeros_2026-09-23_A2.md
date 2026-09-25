# Audit testimony: RH_dbn_debruijn_real_zeros (blind auditor A2, 2026-09-23)

- node: `RH_dbn_debruijn_real_zeros` (rh campaign, Route C / C3, de Bruijn 1950)
- artifact: `telperion/examples/dbn/lean/DBNHadamardApprox.lean`, theorem `dbn_debruijn_real_zeros` (root namespace)
- pass: true
- axioms_clean: true
- statement_byte_identical: true (identical modulo whitespace; canonical gate `statement_matches` = True)
- conjecture1_proved = False

## 1. Read-back of the registry statement (written before reading the artifact)

`DBN.H t z = ∫_{u>0} e^{t u²} Φ(u) cos(z u) du`, with
`Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})`: the Polymath15 / Rodgers-Tao
heat-flow family, for which `H_0(z) = ξ(1/2 + iz/2)/8`. The statement says: for every real
`t ≥ 1/2` and every complex `z`, if `H_t(z) = 0` then `Im z = 0`. That is exactly de Bruijn's
theorem (1950), i.e. the de Bruijn-Newman constant satisfies `Λ ≤ 1/2`. It carries no
hypotheses. It is NOT RH-strength: RH is `Λ ≤ 0` (all zeros of `H_0` real), and this statement
says nothing about `t < 1/2`. The `Φ`/`HIntegrand`/`H` definitions in `Statements/RHDefs.lean`
are character-identical to `DBNDefs.lean`; `#print` shows the same definitions on the island.

## 2. Gate (canonical path)

- `V.statement_matches(artifact, V._normalized_statement(node, root))` = **True**; normalized
  statement `theorem dbn_debruijn_real_zeros : ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0`.
  An independent whitespace-collapsed substring check also gave True.
- `V.artifact_incompleteness_markers` = `[]` on each of DBNHadamardApprox, DBNHadamard, DBNStep,
  DBNHadamardCount, DBNHadamardProduct, DBNHadamardMean, DBNHadamardLinear,
  DBNDeBruijnReduction, DBNHeatApprox, DBNHurwitz, DBNStrip, DBNDefs (the full import closure).
- A manual grep of the closure found no `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`,
  `native_decide` or `ofReduceBool`, and no `sorry`/`admit` tokens.

## 3. Build and axioms

- `leanlock.sh lake build --no-build`: "All targets up-to-date (8759 jobs)".
- Own probe `Probes/AuditProbe_C3_A2.lean` (deleted afterwards): `#check` matches the registry
  type, and an `example` with the verbatim registry type is closed by `dbn_debruijn_real_zeros`.
  `#print axioms dbn_debruijn_real_zeros`, `DBN.approxHadamard` and `DBN.H0ZeroFreeOffStrip_holds`
  each give `[propext, Classical.choice, Quot.sound]`.

## 4. Semantic checks

- Faithful: this is exactly de Bruijn's theorem (`t ≥ 1/2`, ALL complex zeros of `H_t` real) for
  the island `DBN.H` (the Polymath15 kernel). It is not weaker (no restriction on `z`, on `t`
  beyond `≥ 1/2`, or on multiplicities) and not vacuous. The Bochner integral is the genuine one,
  because `Φ` decays doubly exponentially.
- Not RH-strength, and nothing smuggled in: the final theorem has no hypotheses. Its proof term is
  `by_contra` on `H_ne_zero_of_half_le`, which instantiates the conditional
  `H_ne_zero_of_obligations` at two proved theorems:
  - `H0ZeroFreeOffStrip_holds`: the zeros of `H_0` lie in `(Im z)² ≤ 1`, from `H0_zero_strip`, the
    trivial Re s > 1 strip. It is not RH and not `Λ ≤ 0`.
  - `approxHadamard`: this discharges `ApproxHadamard`.
- Hadamard proved, not assumed: `approxHadamard` is derived from
  `evenHadamardData_of_order_lt_two` (differentiable + even + not identically zero + growth
  `A·exp(B‖z‖^ρ)` with `ρ < 2`, here `ρ = 3/2`). `EvenHadamardData` is a real structure: `f` is the
  pointwise limit of `c z^{2m} Π(1 − z²τ_k²)`. `ApproxHadamard` and `H0ZeroFreeOffStrip` appear
  only as discharged `def ... : Prop` obligations, never as hypotheses of the final theorem.
  The axiom output confirms that no extra axioms are involved.

## 5. Numerics (mpmath, 40 digits; composite Gauss-Legendre with 1536 nodes on [0, 1.6])

- Quadrature validation against adaptive `mp.quad`: relative error ≤ 6e-37.
- `H_0(z) = ξ(1/2 + iz/2)/8` checked at 4 complex points: relative error ≤ 1e-35.
- Real zeros of `H_0` in [0, 62]: 28.2694502835, 42.0440792775, 50.0217151603, 60.8497522517.
  These equal `2·γ_n` for n = 1..4, with maximum difference 7e-34.
- Real zeros of `H_{1/2}`: 27.980, 41.668, 49.728, 60.379.
- Argument-principle winding for `t = 1/2` (phase step < π/8):
  - box [0,60]×[0.1,1]: 0
  - box [0,60]×[−1,−0.1]: 0
  - box [0,60]×[0.02,3]: 0
- Positive controls:
  - `H_0` on [27,29.5]×[−0.5,0.5]: 1
  - `H_0` on [0,60]×[−1,1]: 3
  - `H_{1/2}` on [0,60]×[−1,1]: 3 (all three are real zeros)

## 6. Establishes / does not establish

- Establishes: de Bruijn's theorem `Λ ≤ 1/2` for the Polymath15 `H_t`. It is kernel-checked, has
  no hypotheses, stays within the standard three axioms, and has no `sorry` in its closure.
- Does not establish: anything about the zeros of `H_0` inside the strip `|Im z| ≤ 1`, `Λ ≤ 0`,
  or RH. conjecture1_proved = False.

Notes (not failures):
- The TOML node still says `status = "draft"` and "STATED ONLY, not proved". The registry update
  is out of scope for this audit.
- `Probes/AuditProbe_C3_A1.lean` (the other auditor's probe) is present and was left untouched.
