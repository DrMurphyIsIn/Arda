# Audit testimony: RH_dbn_H0_eq_xi (rh campaign), blind auditor A1, 2026-09-22

- pass: true
- axioms_clean: true
- statement_byte_identical: true
- conjecture1_proved = False

Auditor A1 worked blind: no author context was consulted, and the design memo's normalisation was
not relied on. The worktree was `/Users/peterwmurphy/arda-closure`. I ran no git operations and made
no registry edits. My probe file was deleted after use.

## Inputs read

- `telperion/missions/rh/nodes/RH_dbn_H0_eq_xi.toml` (status `draft`, kind `lemma`, no dependencies)
- `telperion/missions/rh/lean/Statements/RH_dbn_H0_eq_xi.lean` (generated, sha256 prefix `000e927caef49a0a`)
- `telperion/missions/rh/lean/Statements/RHDefs.lean` (namespaces `DBN` and `LiCriterion`)
- The artifact `telperion/examples/dbn/lean/DBNXi.lean` and its island import closure: `DBNXiCos`,
  `DBNXiIBP`, `DBNXiRiemann`, `DBNGKernel`, `DBNDefs`. Outside the island, the closure also includes
  the upstream `Lc.LiCriterion.Basic` at rev `35df682f` and Mathlib.

## (1) Read-back of the registry statement (written before I read the artifact)

The registry statement is

    theorem dbn_H0_eq_xi (z : ℂ) :
        DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)

It says that for every complex number z, the t = 0 member of the de Bruijn-Newman heat-flow family
equals one eighth of the Riemann xi function at s = 1/2 + iz/2. The heat-flow value is

    H_0(z) = ∫_{(0,∞)} Φ(u) cos(zu) du        (Bochner integral, complex-valued)

where Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u}). The factor e^{tu²} equals 1 at t = 0.

The xi function is the upstream entire form

    ξ(s) = (1/2) s (s − 1) Λ₀(s) + 1/2,    with Λ₀ = Mathlib `completedRiemannZeta₀`.

Mathlib has Λ = Λ₀ − 1/s − 1/(1 − s). So for s ∉ {0, 1}, ξ(s) = (1/2) s(s−1) Λ₀ − (s−1)/2 + s/2,
which equals the textbook (1/2) s(s−1) π^{−s/2} Γ(s/2) ζ(s). At the points s = 0 and s = 1,
ξ = 1/2. This is the classical Riemann identity (Titchmarsh 10.1; Polymath15 eq. (3)) in the
standard normalisation.

The statement is not junk:

- Φ decays like exp(−(π/2)e^{4u}), so the integrand is integrable for every complex z, and the
  Bochner integral does not fall back to its value 0 on non-integrable functions. DBNDefs proves
  `integrableOn_HIntegrand` for this.
- ξ has no side conditions.

The identity involves no zero locations and is not RH-equivalent. At z = i it gives
H_0(i) = ξ(0)/8 = 1/16.

## (2) Statement comparison and hardened gate

**Text comparison.** The registry theorem text (up to `:= by sorry`) and the artifact theorem text
(up to `:= by`) are identical after whitespace normalisation. They also agree line by line after
stripping trailing whitespace. The normalised text is:

    theorem dbn_H0_eq_xi (z : ℂ) : DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)

**Hardened gate** (`PYTHONPATH=telperion/src`):

- `V.statement_matches(DBNXi.lean text, V._normalized_statement(node, root))` returned **True**.
- `V.artifact_incompleteness_markers` returned `[]` for every file checked: DBNXi, DBNXiCos,
  DBNXiIBP, DBNXiRiemann, DBNGKernel and DBNDefs.
- A grep for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `opaque`,
  `unsafe` and `set_option` in these six files found only docstring prose.

**Vocabulary mirror check.** The registry statement elaborates against RHDefs, and the artifact
elaborates against the island. I checked that the RHDefs `DBN` block contains the following as
exact substrings:

- DBNDefs lines 40-41 (`thetaMoment`), 211-214 (`Φ`), 408-409 (`HIntegrand`) and 413 (`H`)
- the upstream `LiCriterion.riemannXi` (Basic.lean 1236-1237, in `namespace LiCriterion`)

All of them matched. Every name in these definitions is fully qualified (`Real.exp`, `Real.pi`,
`Complex.cos`, `Set.Ioi`), so the different `open` lines in the two files do not change how names
resolve. The artifact theorem is declared in the root namespace, as the registry statement is.

**CLI.**

- `telperion.cli mission verify rh` returned `verify [rh]: OK`. The only warning concerned 10
  unrelated islands with no CI build, and the dbn island was not among them.
- `mission status rh` lists `RH_dbn_H0_eq_xi (lemma, draft)`.

**Build.** `leanlock.sh lake build --no-build` in `telperion/examples/dbn/lean` reported
`All targets up-to-date (8747 jobs)`.

## (3) Axiom probe

I wrote `Probes/AuditProbe_RH_dbn_H0_eq_xi_A1.lean` (it imports `DBNXi`), ran it with
`leanlock.sh lake env lean`, and then deleted it. Output:

    dbn_H0_eq_xi : ∀ (z : ℂ), DBN.H 0 z = 1 / 8 * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)
    'dbn_H0_eq_xi' depends on axioms: [propext, Classical.choice, Quot.sound]
    'DBN.H_zero_I' depends on axioms: [propext, Classical.choice, Quot.sound]

The axiom set is exactly [propext, Classical.choice, Quot.sound]. The probe also printed the
elaborated definitions of `DBN.H`, `DBN.HIntegrand`, `DBN.Φ` and `LiCriterion.riemannXi`, and they
match the read-back in (1). Two `example` terms elaborated without error:

- the registry proposition restated independently, closed by `dbn_H0_eq_xi z`
- `DBN.H 0 Complex.I = 1 / 16`, closed by `DBN.H_zero_I`

## (4) Re-derivation of the main steps by hand

Notation: ψ(x) = Σ_{n≥1} e^{−πn²x}, θ = 1 + 2ψ, and g(u) = e^u ψ(e^{4u}).

- **A: Riemann's symmetric integral (DBNXiRiemann).** For all s,
  Λ₀(s) = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{(1−s)/2−1}) dx.
  - I checked this against the classical form Λ(s) = −1/s − 1/(1−s) + ∫_1^∞ ψ(…).
    Mathlib has Λ₀ = Λ + 1/s + 1/(1−s), so the two agree.
  - The proof splits Mathlib's `f_modif` (the Mellin definition of Λ₀, with a halving factor
    because Λ₀(s) = P.Λ₀(s/2)/2) at x = 1.
  - It then inverts the `Ioo 0 1` piece with the functional equation θ(1/x) = √x θ(x).
  - The hurwitzEvenFEPair data (k = 1/2, ε = 1, f = g, f₀ = g₀ = 1) match Mathlib's definitions.
- **B: substitution x = e^{4u} (DBNXiCos).**
  - The Jacobian is 4e^{4u}. The exponent 4u + 4u(s/2 − 1) equals u + izu at s = 1/2 + iz/2, and
    the conjugate exponent gives u − izu.
  - e^{izu} + e^{−izu} = 2cos(zu), so the integrand becomes 4 · 2 · g · cos = 8 g cos. Hence
    Λ₀(1/2 + iz/2) = 8J with J = ∫_0^∞ g cos(z·).
  - The change-of-variables lemma is stated without an integrability hypothesis. That is correct:
    Mathlib's `integral_image_eq_integral_abs_deriv_smul` is an identity of Bochner integrals.
- **C: kernel identity and boundary value (DBNGKernel).**
  - With x = e^{4u}: g'' = e^u(ψ + 24xψ' + 16x²ψ'').
  - Since ψ' = −Σπn²e^{−πn²x} and ψ'' = Σπ²n⁴e^{−πn²x}, this gives
    g'' − g = e^u Σ(16π²n⁴x² − 24πn²x) e^{−πn²x} = 8Φ(u). This matches `g''_sub_g_eq`.
  - Differentiating θ(x) = x^{−1/2} θ(1/x) at x = 1 gives g'(0) = ψ(1) + 4ψ'(1) = −1/2.
    This matches `g'_zero`, which uses `thetaMoment_fe_deriv1` at u = 0.
- **D: two integrations by parts (DBNXiIBP).**
  - First, with v = −z sin(z·): −z²J = g'(0) + ∫ g'' cos.
  - Second, with v = cos(z·): ∫ g'(−z sin) = −g'(0) − ∫ g'' cos.
  - Together: (z² + 1)J = −g'(0) − ∫(g'' − g)cos = 1/2 − 8H_0(z).
  - The boundary terms are sin 0 = 0 at 0⁺ and g'(0)·cos 0 at 0⁺. At +∞ they vanish because
    super-exponential decay beats e^{|z|u}. The hypotheses are discharged by DBNGKernel lemmas and
    checked by the kernel.
- **E: assembly (DBNXi).**
  - At s = 1/2 + iz/2: s(s − 1) = (iz/2)² − 1/4 = −(z² + 1)/4.
  - So ξ(s) = (1/2)(−(z² + 1)/4)(8J) + 1/2 = −(z² + 1)J + 1/2 = 8H_0(z).
  - The `linear_combination` in the proof is exactly this computation.

Nothing looks wrong. The signs, the factor 8, and the normalisation of ξ all check out, and they
agree with the numerics in (5).

## (5) Numerical check from the Lean definitions

I reimplemented the definitions in mpmath at 30 digits. The script is in the scratchpad as
`a1_num.py`.

- **Φ:** the ℕ+ series of DBNDefs:211-214.
- **H_0(z):** ∫_0^∞ Φ(u) cos(zu) du by quadrature.
- **ξ:** `LiCriterion.riemannXi` = (1/2)s(s−1)Λ₀(s) + 1/2, with Λ₀ computed two independent ways:
  - (M) directly from Mathlib's definition, (1/2)·mellin f_modif(s/2), where f_modif(x) is
    θ(x) − 1 on (1, ∞) and θ(x) − x^{−1/2} on (0, 1), and θ is the full ℤ-sum;
  - (C) as π^{−s/2}Γ(s/2)ζ(s) + 1/s + 1/(1 − s).

| z | s = 1/2 + iz/2 | H_0(z) | ξ(s)/8 via (M) | abs diff (M) | abs diff (C) |
|---|---|---|---|---|---|
| i | 0 | 0.0625 | 0.0625 | 0 | 0 (ξ(0)=1/2 by definition) |
| 2 + i | i | 0.061056725280903196 − 0.001412671446286185i | same | 8.7e-29 | 6.5e-33 |
| 10 − 0.7i | 0.85 + 5i | 0.034432260977713066 + 0.002914879003556733i | same | 5.7e-29 | 4.8e-32 |
| 3.5 + 0.25i | 0.375 + 1.75i | 0.057903137358370411 − 0.000588233629935540i | same | 5.8e-29 | 2.4e-33 |
| 28.2694 | 0.5 + 14.1347i | 4.3455578889606e-9 | same | 5.3e-28 | 4.9e-33 |

The last row is next to the first zeta zero. The quadrature of H_0(i) gives H_0(i) − 1/16 = 0 to
30 digits. The identity holds numerically at every point tested, in the registry's normalisation.

## (6) What this establishes and what it does not

**This establishes:**

- A kernel-checked, axiom-clean proof ([propext, Classical.choice, Quot.sound]) of the exact
  registry statement: H_0(z) = (1/8) ξ(1/2 + iz/2) for every complex z.
  - H_0 is the island's Bochner integral of Φ(u)cos(zu) over (0, ∞).
  - ξ is the upstream entire xi on Mathlib's `completedRiemannZeta₀`.
- The artifact text matches the registry statement after whitespace normalisation.
- The hardened gate matches, and there are no incompleteness markers anywhere in the island import
  closure.
- The registry vocabulary mirror of DBN.H, HIntegrand, Φ, thetaMoment and riemannXi is verbatim.
- The corollary H_0(i) = 1/16 is also kernel-checked.

**This does not establish:**

- Anything about the location of zeros of ξ, ζ, H_0 or H_t. The identity is between two entire
  functions and is not RH-equivalent.
- Anything about the de Bruijn-Newman constant, which is not defined on the island.
- De Bruijn's t ≥ 1/2 reality theorem, i.e. node RH_dbn_debruijn_real_zeros.
- The strip-zero node RH_dbn_H0_zero_strip.
- The Riemann Hypothesis.
- Any change to conjecture1.

**Non-blocking observations for the registry owner:**

- The node's `title` still says "STATED ONLY, not proved" and its status is `draft`. Both are stale
  now that the artifact exists. Updating them is a registry action outside this audit.
- The docstrings in DBNDefs (lines 10-12 and 411-412) say the representation theorem is "NOT proved
  here". That is accurate for that module, since the proof is in DBNXi, but a reader could misread
  it.
- `Probes/` contains other auditors' probe files. This auditor's A1 probe was removed.

conjecture1_proved = False
