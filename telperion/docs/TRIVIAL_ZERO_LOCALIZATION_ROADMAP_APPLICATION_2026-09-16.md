# The Trivial-Zero Localization, applied to the RH closure map

*2026-09-16. Applies the kernel-verified archimedean-localization theory
(`TRIVIAL_ZERO_LOCALIZATION_2026-09-16.md`; `trivial_zero_is_archimedean`,
3-axiom clean) to `RH_ROUTES_ROADMAP_2026-09-16.md`. It **refines the map** —
carving the archimedean half off every route and formally locating the wall in the
companion — and it **reaches RH nowhere**. `conjecture1_proved = False`.*

## One split, four routes
The verified theorem says: ζ's zero set decomposes into an **archimedean part**
(the trivial zeros = the pole of `Γℝ`, carrying no arithmetic) and the **companion**
(the nontrivial zeros of the completed `Λ`, where all arithmetic lives). At the level
of the RH-equivalent Li coefficients this is exactly the corpus split
`λₙ = 1 + taylorCoeff(companion)ₙ + taylorCoeff(Γℝ)ₙ` (#463), with the archimedean
term **already bounded** `|Re taylorCoeff(Γℝ)ₙ − (n/2)log n| ≤ 8n` (#519).

The map's four routes all terminate at the **same wall** (the Selberg-dictionary
temperedness/growth clause). The localization says, kernel-checked: **that wall is
the companion, not the archimedean part** — every route can carve off its archimedean
half as *solved*, and must, to see the wall clearly.

## Per-route application

**Route A (reverse-Dyson).** A0 (the regularized membership statement) subtracts the
archimedean density `Γ′/Γ`. The localization is the formal justification: that density
is exactly the trivial-zero / `Γℝ` contribution — a fully-known, non-arithmetic
quantity, so the subtraction is well-defined, not a fudge. It also supplies a **negative
control** for the AFQ class definition (`ARITHMETIC_FQ_MEMBERSHIP_SPEC §2`): the trivial
zeros are *known off-line witnesses*, so the class must regularize them away — joining
`MM_euler_factor_section_offline` as a refutation test the definition must pass.

**Route B (positivity / Li).** Direct hit, and a concrete map refinement.
Node **B8** ("unconditional archimedean trend: the λₙ floor as an all-n theorem") should
be **re-graded and split**: its *archimedean* half is **already a kernel theorem**
(#519, `taylorCoeff_Gammaℝ_re_growth`, `(n/2)log n ± 8n`, 3-axiom clean). B8's open
content is *purely the companion floor*. So B8 = [archimedean: DONE] + [companion: the
wall-adjacent open part]. The Li criterion correctly excludes the trivial zeros (they are
not zeros of Λ/ξ), which the split confirms — a positivity argument that included them
would be wrong.

**Route C (de Bruijn–Newman).** The localization confirms C is **well-posed**: the flow
acts on the completed `H₀ = Ξ/8`, from which the trivial zeros are *already removed*, so
the heat flow sees only the arithmetic zeros. And the H_t evaluator (**C6**, "Γ-factor +
finite Dirichlet sum") has its **Γ-factor part = the solved archimedean piece** (the
same `RvMArch`/EM machinery as #519); the open content is the Dirichlet (arithmetic) sum.

**Route D (spectral).** The roadmap's **D2** correction — "the bridge has NO archimedean
Γ term; it must be added from the RvMArch machinery" — is precisely identified by the
localization: that missing term **is** the `Γℝ` / trivial-zero contribution, and the
machinery for it already exists (#519). It also matches Connes–Consani's "conceptual
reason for positivity at the *single archimedean place*": the archimedean place is the
tractable one *because* it is fully known (trivial zeros exact); the mystery is the finite
places (the companion).

## The wall, formally located
Every route's `rh-hard-wall` node (A5, B10, C10, D11) is the **companion** clause. The
localization is a kernel-checked statement of where the wall is **not**: not the
archimedean part. It does not move the wall closer; it removes the archimedean
underbrush in front of it, on all four routes at once, so the companion stands alone as
the sole, well-posed target.

## A uniform negative control (formalizable next brick)
The trivial zeros are *known off-line zeros* — a cross-route refutation test: any
reality-forcing / positivity argument must be consistent with them being off Re = ½.
The verified `gammaℝ_zero_at_trivial` gives their exact location; the companion theorem
`trivial_zero_off_critical_line` (`(-2(n+1)).re ≠ ½`, formalizable) would make this a
kernel-checked negative control usable by A2/B/D, in the program's forge-the-witness
discipline.

## Honest limit
This sharpens the target — it splits every route into [archimedean: solved] +
[companion: the wall], re-grades B8, justifies A0's regularization, and identifies D2's
missing term — but it crosses nothing. The companion clause is still RH, still
`rh-hard-wall`, still open. The trivial-zero localization is the clearest map yet of the
ground *around* the wall, kernel-checked. `conjecture1_proved = False`.
