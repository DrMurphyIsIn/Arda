<!-- Precise spec for Route P Brick D2b: the finite Bragg identity for the companion coefficient
`taylorCoeff zetaPoleCompanion n = explicit log-prime sum`. First target pinned = the weight
reconciliation lemma (liWeight ↔ liPairedSummand). Depends on D1 (#471) + D2a (#472).
conjecture1_proved = False -- D2b is category-(b) finite / category-(c) at the uniform limit. -->

# Route P Brick D2b — the finite Bragg identity for the companion coefficient (spec)

**Goal.** Express Route P's arithmetic carrier as an explicit log-prime (von Mangoldt / Bragg) sum:

> `taylorCoeff zetaPoleCompanion n = (explicit-formula boundary) − (finite log-prime Bragg sum)`

completing the diffraction reading — with `rh_iff_companion_ge` (#465) this makes RH read as
*log-prime Bragg amplitudes ≥ archimedean floor* per `n`.  D2a (#472) supplies the edge integrand;
D2b assembles it into the coefficient identity.  `conjecture1_proved = False`.

## The obstacle, precisely (why D2b is not a clean specialization of #430)

Two zero-sum representations are in play, and **they use different weights**:

| ingredient | statement | weight |
|---|---|---|
| **Stratum 2** `liCoeff_isLimit_partialSums` (#430) | `taylorCoeff riemannXi n = ½ Σ'_ρ liPairedSummand n ρ` *(conditional on `hgenus`, `hhad`)* | `liPairedSummand` |
| **Finite explicit formula** `li_finite_explicit_formula` (#430) | `Σ_ρ divisor(ρ)·liWeight n ρ = (boundary) − (Σ' vonMangoldt)` *(edge `hnz*`)* | `liWeight` |
| **The split** `taylorCoeff_riemannXi_split_explicit` (#463) | `taylorCoeff riemannXi n = 1 + taylorCoeff companion n + taylorCoeff Γℝ n` | — |

The exact forms (all on main):
- `liWeight n ρ = 1 − (1 − 1/ρ)ⁿ`               (`RvMLiCountBridge.liWeight_at_zero`)
- `liSummand n ρ = 1 − (1 − 1/ρ)^{−(n+1)}`        (`RvMOnLinePositivity`)
- `liPairedSummand n ρ = 2 − v − v⁻¹`,  `v := (1 − 1/ρ)^{n+1}`  (`liPairedSummand_eq_two_sub_v_sub_inv`, #468)

So the coefficient's zero-sum runs over **paired** zeros with the **negative** power `(1−1/ρ)^{−(n+1)}`,
while the finite explicit formula weights ζ's divisor by the **positive** power `(1−1/ρ)ⁿ`.  Bridging
them is the real content of D2b — not a reuse of #430 but a reconciliation *between* its two halves.

## ★ First target — the weight-reconciliation lemma ★

Pin this as the first buildable obligation (name it `liPairedSummand_eq_divisor_liWeight_combo` or
`liWeight_paired_reconcile`):

> **Reconcile the paired coefficient weight with the divisor·liWeight sum.**  Over the FE-symmetric
> pairing `ρ ↔ 1 − ρ` (which sends `w := 1 − 1/ρ` to `w⁻¹`, and on which `divisor riemannZeta` is
> constant `= 1` for simple zeros), express the paired coefficient summand `liPairedSummand n ρ`
> as an explicit ℚ-combination of the finite-explicit-formula weight `liWeight m ρ` (and its paired
> value `liWeight m (1−ρ)`) for the relevant `m`.

Concretely, the algebra to discharge: with `v = (1−1/ρ)^{n+1}` and `pairedZero ρ = 1−ρ` giving the
paired base `w⁻¹`,
```
liPairedSummand n ρ = 2 − v − v⁻¹
                    = (1 − v) + (1 − v⁻¹)
                    = liSummand n ρ + liSummand n (1−ρ)
```
and `liWeight` at shifted index relates by `liWeight (n+1) ρ = 1 − w^{n+1} = 1 − v` and
`liSummand n ρ = 1 − w^{−(n+1)} = 1 − v⁻¹`.  So the reconciliation is the **index-and-inversion
identity**
```
liPairedSummand n ρ = liWeight (n+1) ρ + (1 − ((1 − 1/ρ)^{n+1})⁻¹),
```
whose second term is `liSummand n ρ`, and — using `w⁻¹ = 1 − 1/(1−ρ)` (already proved as `hpair` in
`RvMOnLinePositivity`) — equals `liWeight (n+1) (1−ρ)`.  Hence the crisp target:

> **`liPairedSummand n ρ = liWeight (n+1) ρ + liWeight (n+1) (pairedZero ρ)`.**

This is elementary (reuses the `hpair : 1 − 1/(1−ρ) = w⁻¹` identity + `liWeight_at_zero`), unconditional,
and it is the hinge that lets the finite explicit formula speak the coefficient's language.  **Build
this first.**

## Full D2b chain (dependency-ordered)

1. **D2b-1 (the weight-reconciliation lemma above).** `liPairedSummand n ρ = liWeight (n+1) ρ +
   liWeight (n+1) (pairedZero ρ)`.  Elementary, unconditional, kernel-clean.  *First target.*
2. **D2b-2 — paired coefficient sum as a divisor·liWeight sum.**  Combine D2b-1 with Stratum 2:
   `taylorCoeff riemannXi n = ½ Σ'_ρ (liWeight (n+1) ρ + liWeight (n+1) (1−ρ))`; fold the FE pairing so
   the sum runs over ζ's divisor with weight `liWeight (n+1)` — matching `li_finite_explicit_formula`'s
   left side (at index `n+1`).  Inherits Stratum 2's `hgenus`/`hhad` (documented, undischarged).
3. **D2b-3 — insert the finite explicit formula + the split.**  Apply `li_finite_explicit_formula`
   (index `n+1`) to rewrite the divisor·liWeight sum as `(boundary) − (Bragg sum)`; subtract the
   explicit `1 + taylorCoeff Γℝ n` (the split, #463) to isolate `taylorCoeff companion n`.  Use D2a
   (#472) to render the boundary's right edge as the companion Bragg integrand.  Result: the FINITE
   Bragg identity for the companion coefficient (over a contour/box), with Arb-enclosed edges.
4. **D2b-4 — the emitter (D3).**  Feed the finite Bragg identity into the `bragg_floor` emitter
   (`ROUTEP_DIFFRACTION_SCOPE_2026-09-11.md`): certify `Σ_{p^k≤N} amplitude − enclosed tail ≥ floor`.

## Honest ceiling

- **D2b-1** is unconditional and category-(b) buildable now (given D1/D2a).  It is the crisp reduced
  obligation this spec pins.
- **D2b-2/3** carry Stratum 2's `hgenus`/`hhad` (genus-1 summability + Hadamard product) as documented
  undischarged analytic hypotheses, and the finite explicit formula's edge zero-avoidance (Arb trust
  seam) — the same seams as #430.  Finite, kernel-checkable.
- **The uniform limit** — a *convergent* companion = log-prime sum at the Li base point, uniformly in
  `n` — is category-(c) **RH-hard**: the von Mangoldt series diverges at `s = 1` and the contour shift
  to `Re = 1/2` with controlled archimedean residual *is* the analytic core of RH (assessment §2.1/2.3,
  Freitas Cor. 4.2).  Never crossed by finite certificates.

`conjecture1_proved = False`.  D2b relocates/finitely-certifies; it does not close RH.
