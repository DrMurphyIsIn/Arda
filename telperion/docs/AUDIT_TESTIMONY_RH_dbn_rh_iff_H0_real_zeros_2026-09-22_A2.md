# Blind audit testimony: RH_dbn_rh_iff_H0_real_zeros (auditor A2, 2026-09-22)

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace; the gate's normalized forms are also identical)
- conjecture1_proved = False

Auditor A2 had no author context. The read-back in section 1 was written from the registry node,
the statement file and `RHDefs.lean` before the artifact was opened.

Inputs:
- Node: `telperion/missions/rh/nodes/RH_dbn_rh_iff_H0_real_zeros.toml` (kind milestone, status
  draft, depends_on `RH_dbn_H0_eq_xi`)
- Statement: `telperion/missions/rh/lean/Statements/RH_dbn_rh_iff_H0_real_zeros.lean`
  (sha256 header b89ad0154569e665)
- Artifact: `telperion/examples/dbn/lean/DBNRealZerosIffFinal.lean`, theorem `dbn_rh_iff_H0_real_zeros`

## 1. Read-back of the registry statement (written before reading the artifact)

```
theorem dbn_rh_iff_H0_real_zeros :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2)
      ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0
```

In prose, the statement says two things are equivalent:

- **Left side.** Every complex zero ρ of Mathlib's `riemannZeta` that lies in the open critical
  strip 0 < Re ρ < 1 has Re ρ = 1/2. This is the Riemann Hypothesis, written in the AND_ladder
  curried grammar `∀ ρ, riemannZeta ρ = 0 → A → B → ρ.re = 1 / 2` with the strip bounds as the two
  hypotheses.
- **Right side.** Every complex zero z of H_0 is real.

The definitions behind H_0, from `RHDefs.lean` (namespace `DBN`):

- The integral is H_t(z) = ∫_{u ∈ (0,∞)} e^{t u²} Φ(u) cos(z u) du, so at t = 0 it is
  H_0(z) = ∫_0^∞ Φ(u) cos(zu) du.
- The kernel is Φ(u) = Σ_{n ≥ 1} (2π² n⁴ e^{9u} − 3π n² e^{5u}) exp(−π n² e^{4u}), summed over
  `ℕ+`.

This is the Polymath15 / Rodgers–Tao normalisation of the de Bruijn–Newman kernel. The classical
fact is that H_0(z) = (1/8) ξ(1/2 + iz/2), so the zeros of H_0 correspond exactly to the nontrivial
zeros of ζ through s = 1/2 + iz/2. Under that map Re s = (1 − Im z)/2, so the right side restates
RH. The node claims the equivalence only. It does not claim either side.

The DBN block in `RHDefs.lean` (thetaMoment, Φ, HIntegrand, H) was compared by eye with
`examples/dbn/lean/DBNDefs.lean` lines 40-41, 211-214, 408-409 and 413. The two are verbatim
identical.

## 2. Statement comparison and the hardened gate

- **Artifact theorem text.** The text of `dbn_rh_iff_H0_real_zeros`, from `theorem` up to `:=`,
  is identical to the registry statement after collapsing runs of whitespace (Python check: equal
  = True).
- **Hardened gate.** `V._normalized_statement(node, root)` returns
  `theorem dbn_rh_iff_H0_real_zeros : (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2) ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0`.
  `V.statement_matches(artifact_text, that)` returns True.
- **Incompleteness markers.** `V.artifact_incompleteness_markers` returns `[]` for the artifact and
  for every island module in its import closure: DBNRealZerosIffFinal, DBNRealZerosIff, DBNXi,
  DBNXiIBP, DBNXiCos, DBNXiRiemann, DBNGKernel and DBNDefs. The one external import is the pinned
  upstream `Lc.LiCriterion.Basic` at rev 35df682f. Its axioms are covered by the probe in
  section 3.
- **Extra grep over the same closure.** Declarations starting with `opaque`, `axiom`, `unsafe`,
  `@[implemented_by`, `@[extern`, `macro`, `syntax`, `elab`, `set_option`, `notation` or `instance`
  gave no hits.
- **Elaboration check.** In the probe, `set_option pp.fullNames true` with
  `#check @dbn_rh_iff_H0_real_zeros` shows that `riemannZeta` is Mathlib's root constant and `H` is
  `DBN.H`, so no shadowing is involved. An independently typed copy of the registry proposition is
  accepted with the artifact term as its proof.
- **Build and CLI.** `leanlock.sh lake build --no-build` reports "All targets up-to-date (8747
  jobs)". `telperion.cli mission verify rh` reports `verify [rh]: OK`.

## 3. Axiom probe

Probe file: `Probes/AuditProbe_RH_dbn_rh_iff_H0_real_zeros_A2.lean`, run with `lake env lean`
and deleted after the run.

```
'dbn_rh_iff_H0_real_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'dbn_H0_eq_xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'LiCriterion.xi_zeros_are_nontrivial_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The axiom list is exactly the required set. There is no `sorryAx` and no custom axiom.

## 4. The mathematics, re-derived by hand

The proof has three layers.

**(a) Change of variables, s = 1/2 + iz/2.** For z = x + iy, Re s = 1/2 − y/2, so Re s = 1/2
holds exactly when Im z = 0. The inverse is z = −2i(s − 1/2), and its imaginary part is
−2(Re s − 1/2). All of this checks out. It matches the island lemmas `xiArg_re`,
`xiArg_re_eq_half_iff`, `xiArg_surj` and `xiArgInv_im`.

**(b) Zeros of ξ are exactly the strip zeros of ζ.** Here ξ(s) = (1/2) s(s−1) Λ₀(s) + 1/2, where
Λ₀ is Mathlib's `completedRiemannZeta₀`. This ξ is entire. It equals 1/2 at s = 0 and s = 1. The
Γ poles cancel the trivial zeros, and there are no zeros with Re s ≥ 1 or Re s ≤ 0. So ξ(s) = 0
holds exactly when ζ(s) = 0 and 0 < Re s < 1. The island takes this from the upstream
`LiCriterion.xi_zeros_are_nontrivial_zeros`, which the probe shows is axiom-clean, by unpacking the
subtype.

**(c) The C2 identity H_0(z) = ξ(1/2 + iz/2)/8.** I re-derived each of its parts.

- **Riemann's integral.** Λ₀(s) = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{(1−s)/2−1}) dx, with
  ψ(x) = Σ_{n≥1} e^{−πn²x}. This is consistent with Λ₀ = Λ + 1/s + 1/(1−s) = Λ − 1/(s(s−1)).
- **Substituting x = e^{4u}.** At s = 1/2 + iz/2 we get x^{s/2−1} dx = 4 e^{u(1+iz)} du and
  x^{(1−s)/2−1} dx = 4 e^{u(1−iz)} du. So Λ₀(s) = 8 ∫_0^∞ g(u) cos(zu) du = 8J, with
  g(u) = e^u ψ(e^{4u}).
- **Kernel identity.** Take one term g_n = e^u exp(−a e^{4u}) with a = πn². Then
  g_n'' − g_n = e^u e^{−a e^{4u}} (16a² e^{8u} − 24a e^{4u}) = 8(2π²n⁴ e^{9u} − 3πn² e^{5u}) e^{−πn² e^{4u}}.
  Summing over n gives g'' − g = 8Φ. Also g'(0) = ψ(1) + 4ψ'(1) = −1/2. This follows from
  differentiating the theta relation 2ψ(x) + 1 = x^{−1/2}(2ψ(1/x) + 1) at x = 1.
- **Two integrations by parts.** The boundary terms vanish at infinity because of the decay of g
  and g'. This gives z² J = −g'(0) − ∫ g'' cos = 1/2 − J − 8H_0, that is,
  (z² + 1) J = 1/2 − 8 H_0(z).
- **Assembly.** s(s−1) = (iz/2)² − 1/4 = −(z²+1)/4. So
  ξ(s) = (1/2)(−(z²+1)/4)(8J) + 1/2 = −(z²+1)J + 1/2 = 8 H_0(z).
  This is what the `linear_combination` in `DBNXi.dbn_H0_eq_xi` closes.

**Assembly of the equivalence.** Because 1/8 ≠ 0, H_0(z) = 0 exactly when ξ(1/2 + iz/2) = 0.

- **Forward.** Suppose H_0(z) = 0. Then ρ = 1/2 + iz/2 is a strip zero of ζ. Strip-RH gives
  Re ρ = 1/2, and so Im z = 0.
- **Backward.** Take a strip zero ρ of ζ. Then ξ(ρ) = 0, so z = −2i(ρ − 1/2) is a zero of H_0.
  That z is real, and so Re ρ = 1/2.

The artifact's proof follows exactly this argument. Nothing in the mathematics looks wrong. The
normalisation (the factor 1/8, the argument 1/2 + iz/2, and Φ with the e^{9u}/e^{5u} exponents)
matches Polymath15 eq. (3) and Rodgers–Tao.

## 5. Grammar, and whether this is a genuine equivalence

**RH-side grammar.** The left side is exactly
`∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2`. That is the curried AND_ladder
shape, the same form as `AND_ladder_1e6` and `AND_ladder_h280000`, with the strip bounds in place
of the height bounds. As a sanity check, the probe derives this strip form from Mathlib's
`RiemannHypothesis`. The converse also holds classically, because every zero outside the strip is
trivial.

**Neither side is proved.**
- A grep over the island finds no hypothesis-free theorem concluding either side, except inside
  this biconditional and its conditional twin, `_of_H0_eq_xi`.
- `DBNStep.lean:448` proves `z.im = 0` only for a shift average, and only under a reality
  hypothesis on f.
- The registry lists `RH_conjecture` as a draft goal.
- The axiom list contains no `sorryAx`, so nothing could be hiding an unproved RH in the closure.

**Neither side is vacuous.**
- H_0 is not identically zero. The probe proves `DBN.H 0 Complex.I ≠ 0` from `DBN.H_zero_I`
  (H_0(i) = 1/16). So the right side is not trivially true through a degenerate H that is zero
  everywhere (which would make it false) or has no zeros for a definitional reason.
- `dbn_H0_eq_xi` pins H_0 to ξ/8, and ξ is built from Mathlib's `completedRiemannZeta₀`, which is
  independent of the island. So the zero set of H_0 is exactly the image of the nontrivial ζ zeros
  under z = −2i(ρ − 1/2).
- That set is nonempty by classical theory (infinitely many zeros), and it is not known to be real,
  because that is RH.
- The left side is RH itself, which is open.
- So neither side is decidable by definition, and the equivalence is genuine.

## 6. Establishes / does not establish

**Establishes** (kernel-checked; axioms exactly propext, Classical.choice and Quot.sound; no
`sorry` in the closure):
- Strip-grammar RH is equivalent to "every zero of H_0 is real", unconditionally, where H_0 is the
  island's de Bruijn–Newman H_t at t = 0.
- Along the way, the island proves the C2 representation H_0(z) = (1/8) ξ(1/2 + iz/2) for every
  complex z (`dbn_H0_eq_xi`) and H_0(i) = 1/16.
- The artifact matches the registry statement exactly under the hardened gate.

**Does not establish:**
- RH, or any zero of ζ on the critical line.
- That any zero of H_0 is real.
- Any bound on the de Bruijn–Newman constant Λ, which is not even defined on this island.
- De Bruijn's theorem that H_t has only real zeros for t ≥ 1/2 (node `RH_dbn_debruijn_real_zeros`,
  still draft).
- Anything about the goal `RH_conjecture`.

**Process notes.**
- The node is still `status = "draft"` with no artifact link in its TOML. This audit does not
  change the registry. Linking or promoting the node is a separate step for the registry owner.
- The equivalence to Mathlib's `RiemannHypothesis` form is not part of this node. I checked only
  one direction, in the probe, as a sanity check.

conjecture1_proved = False
