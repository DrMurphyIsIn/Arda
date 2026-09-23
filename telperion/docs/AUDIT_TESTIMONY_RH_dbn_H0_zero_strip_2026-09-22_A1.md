# Audit testimony: RH_dbn_H0_zero_strip (rh campaign), blind auditor A1, 2026-09-22

- pass: true
- axioms_clean: true
- statement_byte_identical: true
- conjecture1_proved = False

Auditor A1 worked blind. It had no author context and did not look for any. Inputs read:
`missions/rh/nodes/RH_dbn_H0_zero_strip.toml`,
`missions/rh/lean/Statements/RH_dbn_H0_zero_strip.lean`, `missions/rh/lean/Statements/RHDefs.lean`
(the `namespace DBN` block), `examples/dbn/lean/DBNStrip.lean` and `examples/dbn/lean/DBNDefs.lean`.
DBNDefs is the only island module in DBNStrip's import closure. No git operations were run and
nothing in the registry was edited. The only file written besides this testimony was the probe
`examples/dbn/lean/Probes/AuditProbe_RH_dbn_H0_zero_strip_A1.lean`, which has been deleted. The
`AuditProbe_*_A2.lean` files in that directory belong to other auditors and were not touched.

## 1. Read-back of the registry statement (written before reading the artifact)

```
theorem dbn_H0_zero_strip :
    ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1
```

The definitions come from RHDefs, which mirrors DBNDefs verbatim:

- `Φ(u) = Σ_{n ∈ ℕ+} (2π²n⁴e^{9u} − 3πn²e^{5u}) · exp(−πn²e^{4u})`. This is a `tsum` over the
  positive integers. The series is summable for every real `u`, so this is the true Polymath15 /
  Rodgers-Tao Φ and not a junk value.
- `H t z = ∫_{u ∈ (0,∞)} e^{t u²} Φ(u) cos(z u) du`. This is a Bochner integral. For `t = 0` the
  weight is `e^0 = 1`. Φ decays like `exp(−(π/2)e^{4u})`, which beats `|cos(zu)| ≤ e^{|z|u}`, so
  the integrand is integrable for every complex `z`. `H 0` is therefore the genuine de
  Bruijn-Newman `H_0` for every `z`, and a non-integrable integrand never collapses it to 0.

In words, the statement says: every complex zero `z` of `H_0` satisfies `(Im z)² ≤ 1`, so
`-1 ≤ Im z ≤ 1`. The zeros of `H_0` lie in the closed horizontal strip `|Im z| ≤ 1`.

Classically `H_0(z) = ξ(1/2 + iz/2)/8`. Under `s = 1/2 + iz/2` we have `Re s = 1/2 − Im z/2`, so
the strip `|Im z| ≤ 1` is the closed critical strip `0 ≤ Re s ≤ 1`. The statement is the classical
fact that ξ has no zeros with `Re s > 1` or `Re s < 0`. It is far weaker than RH and does not
even need the zero-free line `Re s = 1`, because the boundary `|Im z| = 1` is allowed.

The statement is not vacuous. If `H 0` were identically zero, as a junk value would make it, the
conclusion would fail at `z = −2i`. The artifact proves `H0_ne_zero` at that point, and the probe
re-checked it.

## 2. Statement comparison and the hardened gate

- The theorem text of the registry statement and of the artifact, with whitespace normalized, is
  `∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1` in both. They are byte-identical, and they are also
  equal under `V.normalize_lean`. Both theorems are declared at the root namespace: the artifact's
  theorem comes after `end DBN`.
- `V._normalized_statement(node, root)` returns
  `'theorem dbn_H0_zero_strip : ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1'`.
- `V.statement_matches(DBNStrip.lean text, normalized)` returns **True**. The match is followed
  by the proof body `:=`.
- `V.artifact_incompleteness_markers` returns `[]` on DBNStrip.lean and `[]` on DBNDefs.lean.
  Those two files are the island's entire import closure. It also returns `[]` on the upstream
  `Lc/LiCriterion/Basic.lean`, which DBNDefs imports.
- The mirrored vocabulary was checked separately. The `namespace DBN` block of RHDefs
  (thetaMoment, Φ, HIntegrand, H) is identical to DBNDefs.lean at lines 40-41, 211-214, 408-409
  and 413 (`diff` reports no differences). The probe also checked the island `Φ` and `H` against
  the registry text by `rfl`.
- A plain word scan of DBNStrip and DBNDefs finds no `sorry` or `admit` token anywhere, including
  in comments.
- `telperion mission verify rh` reports `verify [rh]: OK`. The dbn island is not in the list of
  islands that CI does not build. `mission status rh` shows the node as `(lemma, draft)`.
- `lake build --no-build`, run under leanlock, reports `All targets up-to-date (8747 jobs)`. No
  build was run.

## 3. Axioms (own probe)

Run with `lake env lean Probes/AuditProbe_RH_dbn_H0_zero_strip_A1.lean`:

```
'dbn_H0_zero_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'DBN.H_zero_eq_of_im_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That is exactly the permitted set. The probe also closed
`example : ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1 := dbn_H0_zero_strip` and
`example : ∃ z, DBN.H 0 z ≠ 0 := DBN.H0_ne_zero`.

To confirm the proof is free of the representation theorem and of anything RH-strength, the
probe walked every constant reachable from the type and value of `dbn_H0_zero_strip` with a
small metaprogram:

- total constants reached: 55354
- constants outside Mathlib and core: 68, all from the modules `DBNStrip` and `DBNDefs`
- constants whose names match `eq_xi`, `riemannXi`, `LiCriterion`, `Hadamard`,
  `RiemannHypothesis` or `sorryAx`: **none**

So the proof does not use C2 (`dbn_H0_eq_xi`, DBNXi), any LiCriterion or Hadamard material, or
any RH-strength statement. DBNStrip imports only DBNDefs. DBNDefs imports Mathlib and
`Lc.LiCriterion.Basic`, but no LiCriterion constant is reached by this proof.

## 4. The mathematics, re-derived by hand

Throughout, `s = 1/2 + iz/2`, so `iz = 2s − 1` and `Re s = 1/2 − Im z/2`. Then `Im z < −1` if
and only if `Re s > 1`.

- **L1a, the fold.** `cos w = (e^{iw} + e^{−iw})/2`. Substitute `u ↦ −u` in the `e^{−izu}` half
  and use that Φ is even. This gives `H_0(z) = (1/2)∫_ℝ Φ(u)e^{izu} du`. Evenness of Φ is the
  DBNDefs theorem `Φ_neg`. It follows from Mathlib's `jacobiTheta₂_functional_equation`,
  differentiated twice, so it is the theta functional equation and not C2. A numerical check gave
  `Φ(0.3) − Φ(−0.3) = 2.4e-31`. Integrability on `(−∞,0]` is obtained by reflecting to `(0,∞)`
  with `−z`. Correct.
- **L1b, the Gamma integral on the line.** Substitute `x = e^{4u}`, so `du = dx/(4x)` and
  `e^{wu} = x^{w/4}`. Then `∫_ℝ e^{wu}exp(−ce^{4u}) du = (1/4)c^{−w/4}Γ(w/4)` for `Re w > 0` and
  `c > 0`. Correct.
- **The termwise value.** Split the n-th term as `2π²n⁴e^{(9+iz)u}e^{−πn²e^{4u}}` minus
  `3πn²e^{(5+iz)u}e^{−πn²e^{4u}}`. We have `(9+iz)/4 = s/2 + 2` and `(5+iz)/4 = s/2 + 1`, and we
  take `c = πn²`. The integral is
  `(1/4)(πn²)^{−s/2}[2Γ(s/2+2) − 3Γ(s/2+1)]`
  `= (1/4)(πn²)^{−s/2}Γ(s/2)·(s/2)(s+2−3)`
  `= (1/8)s(s−1)π^{−s/2}Γ(s/2)n^{−s}`.
  This matches `integral_expTerm`. Both real parts, `9 − Im z` and `5 − Im z`, are positive
  because `Im z < −1`. Correct.
- **L1c, Tonelli and Fubini.** The n-th norm integral is bounded by a constant times `n^p`. The
  exponent is `p = 4 − (9−Im z)/2 = 2 − (5−Im z)/2 = (Im z − 1)/2`, and `p < −1` exactly when
  `Im z < −1`. So the norm integrals are summable, and Mathlib's
  `hasSum_integral_of_summable_integral_norm` lets the sum and the integral be swapped. With
  `ζ(s) = Σ n^{−s}` for `Re s > 1`, this gives
  `H_0(z) = (1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s)` for `Im z < −1`.
  That is `ξ(s)/8`, the correct classical normalization. Correct.
- **L1d, nonvanishing and the strip.** When `Re s > 1`: `s ≠ 0`, `s ≠ 1`, `π^{−s/2} ≠ 0`,
  `Γ(s/2) ≠ 0` because `Re(s/2) > 0`, and `ζ(s) ≠ 0` by Mathlib's
  `riemannZeta_ne_zero_of_one_lt_re` (the Euler product). So `H_0 ≠ 0` when `Im z < −1`. Evenness
  in z (`H_neg`) gives the same when `Im z > 1`. Every zero therefore has `−1 ≤ Im z ≤ 1`, which
  is `Im z² ≤ 1`. Correct.

Nothing in this chain looks wrong. It uses the functional equation only through the evenness of
Φ. It uses no analytic continuation of ζ, no Hadamard product, and no C2.

## 5. Numerical check of the half-plane identity

Both sides were computed with mpmath at 30 digits. The left side evaluates the Lean definitions
directly: the `ℕ+` series for Φ, truncated at terms below 1e-40, and the integral over `Ioi 0` of
`Φ(u)cos(zu)`. The right side is `(1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s)` with `s = 1/2 + iz/2`.

| z | Im z | H_0(z) from the Lean definitions | right side | relative difference |
|---|---|---|---|---|
| −2i | −2 | 0.063591379840790494753 | 0.063591379840790494753 | 0 |
| 3 − 1.5i | −1.5 | 0.059685236920961376204 + 0.0031140779441424473041i | same | 7.7e-32 |
| −7.25 − 3.1i | −3.1 | 0.046819993645076658141 − 0.012668195303118142673i | same | 2.2e-31 |

As a cross-check outside the half-plane, `H_0(i) = 0.0625 = 1/16`, which agrees with the classical
`ξ(0)/8`.

## 6. Establishes / does not establish

**Establishes.** The following holds, kernel-checked with only the axioms
`[propext, Classical.choice, Quot.sound]` and with no `sorry`: every complex zero of the Polymath15
function `H_0(z) = ∫_0^∞ Φ(u)cos(zu) du` lies in the closed strip `|Im z| ≤ 1`. The proof uses
only:
- the evenness of Φ, from the Jacobi theta functional equation;
- the Dirichlet series and Euler product of ζ on `Re s > 1`;
- the Gamma integral.

It does not use C2 (`H_0 = ξ/8`). As by-products, it also proves the half-plane identity
`H_0 = (1/16)s(s−1)π^{−s/2}Γ(s/2)ζ(s)` on `Im z < −1` and that `H_0` is not identically zero. The
registry statement is byte-identical to the artifact's theorem and passes the hardened
containment and proof-body gate.

**Does not establish.**
- Anything about zeros inside the strip, which is where RH lives.
- Strictness `|Im z| < 1`, which would need `ζ(1+it) ≠ 0`.
- C2 (`dbn_H0_eq_xi`) or C4.
- de Bruijn's `t ≥ 1/2` theorem (C3), for which this node is only one input.
- Any bound on the de Bruijn-Newman constant Λ.
- RH.

conjecture1_proved = False.

## Issues (none blocking)

1. The node metadata is stale. The node TOML title still reads "STATED ONLY, not proved
   (obligation L1, ~950 lines)" and `status = "draft"`. The artifact in fact proves the statement
   in about 500 lines. The title should be updated when the node is promoted and granted. This
   does not affect the statement or the verdict.
2. The closed strip `≤ 1` is weaker than the classical strict strip. That is fine, because
   downstream use needs only the closed form, but readers should not mistake it for `< 1`.
