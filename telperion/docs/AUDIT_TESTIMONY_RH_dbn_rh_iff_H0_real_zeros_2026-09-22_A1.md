# Audit testimony: RH_dbn_rh_iff_H0_real_zeros (rh campaign), blind auditor A1, 2026-09-22

- node: `RH.dbn_rh_iff_H0_real_zeros` (telperion/missions/rh/nodes/RH_dbn_rh_iff_H0_real_zeros.toml, status draft, depends_on RH_dbn_H0_eq_xi)
- artifact: telperion/examples/dbn/lean/DBNRealZerosIffFinal.lean, theorem `dbn_rh_iff_H0_real_zeros`
- pass: true
- axioms_clean: true
- statement_byte_identical: true
- conjecture1_proved = False

## 1. Read-back (written before the artifact was opened)

The registry statement (Statements/RH_dbn_rh_iff_H0_real_zeros.lean, against Statements/RHDefs.lean) asserts a
biconditional between two propositions, and nothing more:

- Left side (the registry's AND-ladder strip grammar of RH): for every complex rho, if Mathlib's `riemannZeta rho = 0`
  and `0 < Re rho` and `Re rho < 1`, then `Re rho = 1/2`. Every zeta zero in the open critical strip lies on the
  critical line. Using `Re rho < 1` means Mathlib's junk value of `riemannZeta` at `s = 1` never enters.
- Right side: for every complex z, if `DBN.H 0 z = 0` then `Im z = 0`. Here `DBN.H t z` is the Bochner integral over
  `(0, oo)` of `exp(t u^2) * Phi(u) * cos(z u)`, and `Phi(u)` is the sum over n >= 1 of
  `(2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})`. This is the Polymath15 / Rodgers-Tao convention. At
  `t = 0` the weight is `exp 0 = 1`, so `H_0(z)` is the cosine transform of Phi. In words: every zero of H_0 is real.

The statement claims only that the two are equivalent. It does not assert either side. Classically both sides are RH
(de Bruijn 1950; Titchmarsh 10.1; Polymath15 eq. (3)), because `H_0(z) = (1/8) xi(1/2 + iz/2)`.

## 2. Statement comparison and hardened gate

- Registry declaration versus artifact declaration, with whitespace collapsed:
  `theorem dbn_rh_iff_H0_real_zeros : (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2) ↔ ∀ z : ℂ, DBN.H 0 z = 0 → z.im = 0`.
  The two are identical. The raw bytes up to `:=` are also identical.
- `V.statement_matches(artifact_text, V._normalized_statement(node, root))` returns True. The text that follows the
  matched statement is the proof body `:= dbn_rh_iff_H0_real_zeros_of_H0_eq_xi dbn_H0_eq_xi`.
- `V.artifact_incompleteness_markers` returns [] for every island module in the import closure:
  DBNRealZerosIffFinal, DBNXi, DBNXiCos, DBNXiIBP, DBNXiRiemann, DBNGKernel, DBNRealZerosIff and DBNDefs. The only
  external dependency in the closure is the pinned upstream LiCriterion @ 35df682f, plus Mathlib.
- I also searched the closure for `notation`, `macro`, `syntax`, `elab`, `set_option`, `instance`, `implemented_by`,
  `extern`, `opaque`, `axiom` and `unsafe` in declaration position. There were no hits.
- The vocabulary mirror matches. RHDefs.lean's DBN block (thetaMoment, Phi, HIntegrand, H) is byte-identical to the
  cited DBNDefs.lean lines 40-41, 211-214, 408-409 and 413 (checked with diff). So the registry's `DBN.H` is the
  artifact's `DBN.H`.
- `telperion.cli mission verify rh` reports OK. The dbn island is not in the list of islands that no CI workflow builds.
- `lake build --no-build` in examples/dbn/lean reports "All targets up-to-date (8747 jobs)". I did not run lake build.

## 3. Axiom probe

I wrote a probe, Probes/AuditProbe_RH_dbn_rh_iff_H0_real_zeros_A1.lean, ran it with `lake env lean`, and deleted it
afterwards:

- `dbn_rh_iff_H0_real_zeros` depends on axioms: [propext, Classical.choice, Quot.sound]
- `dbn_H0_eq_xi` depends on axioms: [propext, Classical.choice, Quot.sound]
- `LiCriterion.xi_zeros_are_nontrivial_zeros` depends on axioms: [propext, Classical.choice, Quot.sound]

The probe also re-typed the registry proposition independently and closed it with `dbn_rh_iff_H0_real_zeros`, which
elaborated. `#print` of `DBN.H`, `DBN.HIntegrand`, `DBN.Phi` and `LiCriterion.riemannXi` shows the expected
definitions, with `riemannXi s = 1/2 * s * (s - 1) * completedRiemannZeta0 s + 1/2`, which is entire. AxiomGuardDBN.lean
also prints the axioms of `dbn_rh_iff_H0_real_zeros`, `DBN.H0EqXi_holds` and `dbn_H0_eq_xi`.

## 4. Re-deriving the mathematics by hand

1. Representation (C2, `dbn_H0_eq_xi`). The claim is `H_0(z) = (1/8) xi(1/2 + iz/2)` for every z.
   - Convention check: Titchmarsh's Phi_T(u) = 2 sum(2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}
     satisfies Xi(z) = 2 int_0^oo Phi_T(u) cos(zu) du. The island's Phi is Phi_T(2u)/2. Substituting v = 2u gives
     int Phi cos(zu) du = (1/4) int Phi_T(v) cos(zv/2) dv = (1/8) Xi(z/2) = (1/8) xi(1/2 + iz/2). This agrees.
   - Assembly check: put s = 1/2 + iz/2. Then s(s - 1) = (iz/2)^2 - 1/4 = -(z^2 + 1)/4. With Lambda0(s) = 8J and
     (z^2 + 1)J = 1/2 - 8H_0, we get xi(s) = (1/2)(-(z^2 + 1)/4)(8J) + 1/2 = -(z^2 + 1)J + 1/2 = 8H_0. This agrees.
   - Integration by parts: int g'' cos(z.) = -g'(0) - z^2 J, so int (g'' - g) cos(z.) = -g'(0) - (z^2 + 1)J. With
     g'' - g = 8 Phi and g'(0) = psi(1) + 4 psi'(1) = -1/2 (the classical theta identity), this gives
     (z^2 + 1)J = 1/2 - 8H_0. This agrees.
   - Sanity check: at z = i, 1/2 + i*i/2 = 0 and xi(0) = 1/2, so H_0(i) = 1/16. The island proves this as `DBN.H_zero_I`.
2. Zeros of xi. xi(s) = 0 exactly when zeta(s) = 0 and 0 < Re s < 1. This comes from the upstream
   `xi_zeros_are_nontrivial_zeros`, whose NontrivialZero subtype is exactly the AND-ladder triple. The probe shows it
   is axiom-clean. Classically, xi has no zeros at 0 or 1, and zeta has no zeros outside the strip other than the
   trivial ones, which the Gamma factor cancels.
3. Change of variables. Re(1/2 + iz/2) = 1/2 - Im(z)/2, so this equals 1/2 exactly when Im z = 0. The inverse is
   z = -2i(s - 1/2), since 1/2 + i(-2i(s - 1/2))/2 = s, and Im(-2i(s - 1/2)) = -2(Re s - 1/2). These are correct.
4. Forward direction: a zero z of H_0 gives a zero of xi at 1/2 + iz/2, which is a strip zero of zeta. Strip-RH puts
   it on the line, so Im z = 0. Backward direction: a strip zero rho of zeta gives a zero of xi, so
   z = -2i(rho - 1/2) is a zero of H_0 and is therefore real, so Re rho = 1/2. The factor 1/8 is nonzero. Both
   directions are correct.

I found nothing wrong.

## 5. RH-side predicate and non-vacuity

- The left side is exactly the registry's AND-ladder strip predicate, character for character
  (`∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2`). It is not Mathlib's `RiemannHypothesis`, and no
  weakened variant is used.
- Neither side is proved anywhere on the island. No theorem in examples/dbn/lean concludes either side on its own.
  Every occurrence is inside the biconditional (DBNRealZerosIff: `_of_H0_eq_xi` and `_of_obligation`;
  DBNRealZerosIffFinal). `RiemannHypothesis` does not appear. The registry shows RH_conjecture as a draft goal.
- The H_0 side is not trivially true or false by definition:
  - `dbn_H0_eq_xi` fixes the zero set of `DBN.H 0` to be exactly the image of the nontrivial zeta zeros under
    s -> -2i(s - 1/2). So the right side is RH itself, not a quirk of the definition.
  - The Bochner integral's junk-zero default does not apply, because DBNDefs proves the integrand integrable for every
    t and z.
  - `DBN.H 0 i = 1/16`, which is not 0, so H_0 is not identically zero. If it were, the right side would be false for
    trivial reasons.
  - The left side uses the real Mathlib `riemannZeta`, and whether it holds is open.

## 6. What this establishes and what it does not

Establishes:
- An unconditional, kernel-checked, axiom-clean ([propext, Classical.choice, Quot.sound]) proof that strip-RH, in the
  registry's AND-ladder grammar, is equivalent to "every zero of H_0 is real". H_0 is the island's Polymath15 H_0,
  whose definitions are mirrored byte-for-byte in RHDefs.
- That the artifact's declaration is identical to the registry statement, passes the hardened containment gate
  (statement followed by a proof body), and that no island module in its closure carries incompleteness or assumption
  markers.

Does not establish:
- RH, or either side of the equivalence. This is a bridge between two formulations of the same open conjecture.
- Anything about the de Bruijn-Newman constant (not defined on the island), de Bruijn's t >= 1/2 theorem
  (RH.dbn_debruijn_real_zeros, a separate draft node), or H_t for t != 0.
- conjecture1 (conjecture1_proved = False).

## Non-blocking issues

- The node title still says "STATED ONLY, not proved". The island now proves it unconditionally, so the title is out
  of date. Only whoever owns the registry should change it; this audit did not edit it.
- The registry dependency RH_dbn_H0_eq_xi is itself still draft. The artifact consumes the island theorem
  `dbn_H0_eq_xi` directly, and I checked that theorem's axioms myself. But the registry grant closure requires
  RH_dbn_H0_eq_xi to be granted before this node can be granted.

conjecture1_proved = False
