# MIRRORMERE memo — the torus-section ladder (W3c Part 2 companion)

*2026-09-14. Operator-directed: "envision a higher-dimensional (2-D) quasicrystal
serving an analogous pattern, more accessible mathematically, then collapse it back
to 1-D." `conjecture1_proved = False` — this memo frames instruments and one
certified negative control; nothing here is a route to RH, and the one place the
ladder touches RH-hardness is named (§4, §6-T3).*

## 1. The precedent: the tame classification IS a section theory

Cut-and-project is the operator's proposal, solved once already. Every model set
(Fibonacci chain from a sliced ℤ², Penrose from ℤ⁵) is a higher-dimensional
lattice cut by an irrationally-sloped subspace and collapsed; pure-point
diffraction downstairs is inherited from periodicity upstairs. The collapse
direction is safe and classical (Hof; Baake–Grimm, *Aperiodic Order*).

The Kurasov–Sarnak 2020 construction — the start of the KS20 → OU20 → ACV24
chain that closed Mirrormere's Pillar 2 — is exactly this with the lattice
replaced by a **Lee–Yang hypersurface**: take P(z₁,…,z_d) Lee–Yang on the
d-torus, restrict along the line x ↦ (e^{iλ₁x},…,e^{iλ_dx}) with rationally
independent λ, and the restriction's zero set is a 1-D Fourier quasicrystal.
ACV24 is the converse: *every* real-rooted exponential polynomial is such a
restriction. The tame 1-D quasicrystals are precisely the shadows of
higher-dimensional Lee–Yang geometry.

**The corpus already holds the d = 2 case as a kernel theorem.**
`twoFreq_realRooted_iff` (TwoFreqRigidity.lean:92, registry node
`MM_twofreq_realrooted_iff`) is, read through this dictionary: the section of
the linear form c₁z₁ + c₂z₂ along the T² line of slope λ₂/λ₁ is real-rooted
iff ‖c₁‖ = ‖c₂‖ — 2-D parent, 1-D collapse, rigidity governed upstairs.
`KSConstruction.lean` is the section theory itself; `RationalFreqReduction.lean`
is the rational-slope degeneration.

## 2. Why the zeta parent cannot be finite-dimensional

A cut-and-project from T^d yields a diffraction spectrum finitely generated
over ℚ. The zeta comb's Bragg peaks sit at {m log p} with the log-primes
ℚ-linearly independent — infinitely many independent frequencies at once.
This is kernel-checked in-corpus (`primeLogSpectrum_dense`, node
`MM_primelog_spectrum_dense`): the "rational → irrational frequency
transition" of the difficulty map is, in section language, *the slope of the
cutting line*, and zeta's line is irrational in infinitely many directions.

Hence the true parent is the **infinite torus ∏_p S¹** cut by the Kronecker
flow t ↦ (p^{-it})_p — which is verbatim W3c ("restriction-from-∏_p S¹"),
with W3d the same torus read dynamically (Poincaré section of the flow).
Context, not staffing: Connes' adele-class-space spectral realization and
Berry–Keating are the deepest external incarnations of the same lift.

## 3. Conservation of difficulty, stated for sections

The lift is free; the property is not. A "Lee–Yang hypersurface" on ∏_p S¹
whose Kronecker section is ξ(½ + ix) would collapse to RH — i.e. stability
of the infinite-dimensional parent IS RH relocated. The gain is strictly a
toolkit asymmetry: higher-dimensional stability owns machinery 1-D reality
lacks (Lee–Yang theory, Grace, Borcea–Brändén stable-polynomial calculus,
strong Rayleigh) — the machinery that made KS20/ACV24 possible.

## 4. THE CENTRAL CORRECTION — the naive ladder is FALSE, provably

The obvious program — "truncate to the first N primes, prove each finite
section Lee–Yang / real-rooted, pass to the limit" — **fails at every rung**,
and the corpus can certify the failure:

- **(a) Truncated Euler products have no zeros at all.** Each factor
  (1 − p^{−s})^{−1} is zero-free; finite products are zero-free on Re s > 0.
  There is nothing to put on a line.
- **(b) Inverted single factors put their zeros UNIFORMLY OFF the critical
  line.** The p-factor 1 − p^{−s} on s = ½ + ix is the two-frequency section
  twoFreq(1, −p^{−1/2}; 0, −log p)(x); by our own kernel theorem
  `twoFreq_realRooted_iff` it is real-rooted iff ‖1‖ = p^{−1/2} — false for
  every prime. Its zeros sit at Im x = ½ exactly (the Re s = 0 line): a
  uniform off-line displacement of ½, at every rung, for every p. This is
  registered as the ladder's certified negative control
  (`MM_euler_factor_section_offline`).
- **(c) Partial sums fail classically.** Turán's 1948 program hoped
  zero-freeness of Σ_{n≤N} n^{−s} near the 1-line would yield RH-adjacent
  conclusions; Montgomery (1983, *Zeros of approximations to the zeta
  function*) showed the partial sums have zeros with real part > 1 for all
  large N. Off-line zeros of natural finite approximants are not a defect of
  our framing — they are a theorem.

**Conclusion: critical-line membership is an infinite-N / analytic-continuation
phenomenon.** No finite rung owns it. The difficulty map survives contact with
the section framing, sharpened: the temperedness clause re-enters exactly as
"which completion sequences move the section zeros line-ward in the limit."

## 5. The honest reformulated ladder — three tracks

- **T1 — dictionary (registered, draft).** Formal section vocabulary:
  `torusOrbit`, `linearTorusForm`, `expSum` (AUTHORED in MMDefs, flagged),
  the section identity `MM_torus_section_dictionary`, and the N = 2 rigidity
  restated in ladder vocabulary (`MM_torus_section_n2_rigidity`, discharge =
  short bridge from `twoFreq_realRooted_iff`). Future milestone (queue): KS
  forward theorem at small N — genuine formalization content, tame class,
  decoupled from zeta.
- **T2 — negative control (registered, draft).** `MM_euler_factor_section_offline`
  (§4b): house discipline says build the control before the instrument; this
  rung is also immediately dischargeable, making it the ladder's first grant.
- **T3 — defect instrumentation (NOT registered; the research direction).**
  The rungs do not claim line membership; they MEASURE displacement. The
  W2b defect instrument (`offline_pairs_le_defect` + BraggDefect pipeline)
  applied to finite-section zero configurations gives a certified,
  computable "defect of the N-th section" — §4b says rung 1 has a clean
  nonzero value to certify. The research questions: how does certified
  defect behave in N; which completion sequences (AFE-symmetrized,
  mollified, hybrid ξ-truncations) provably reduce it; and what survives
  N → ∞ — the last being where temperedness re-enters (named, not claimed).
  Statements are the work → statement-authoring queue, per the migration
  doc's rule against inventing formal statements ahead of audit.

## 6. Registered nodes (this commit)

| Node | Kind | Status | Content |
|---|---|---|---|
| `MM_torus_section_dictionary` | lemma | draft | expSum = linearTorusForm ∘ torusOrbit (the section identity; vocabulary anchor) |
| `MM_torus_section_n2_rigidity` | milestone | draft | N=2 rigidity in ladder vocabulary; discharge via `MM_twofreq_realrooted_iff` bridge |
| `MM_euler_factor_section_offline` | lemma | draft | §4b certified negative control at p = 2; discharge via `twoFreq_realRooted_iff` + norm arithmetic |

All three carry AUTHORED statements (not verbatim island extracts) and enter
as **draft** pending the blind read-back audit cycle — deliberately stricter
than the open+linked migration nodes, because authored statements are exactly
what the audit exists to catch.

## 7. References

KS20 Kurasov–Sarnak (J. Math. Phys. 61); OU20 Olevskii–Ulanovskii; ACV24
Alon–Cohen–Vinzant; Turán (1948); Montgomery (1983), *Zeros of approximations
to the zeta function* (Erdős volume); Baake–Grimm, *Aperiodic Order* vol. 1;
context only: Connes (Selecta 1999), Berry–Keating (SIAM Rev 1999). In-corpus:
QC_PROGRAM.md, QC_RIGIDITY_MEMO.md, ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md,
KSConstruction.lean, TwoFreqRigidity.lean, BoundaryLemmas.lean.
