# Wall seam C: the ladder-certified region of the two-parameter Wall (2026-09-21)

Status: kernel-checked on the rvm_bridge island (Lean v4.33.0-rc2, Mathlib via the Zeta23 pin).
Every delivered theorem has axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
no named sub-obligation. The certification is carried as a HYPOTHESIS (`WindowOnLine c D`); it is
what the Turing ladder supplies and nothing else supplies.

Nothing here proves RH. This is an instrument: it says, for the part of the (c, lam) quadrant the
ladder certifies, that the Wall inequality F(c, lam) >= 0 holds, with explicit constants.
The uncertified residual is the Wall. conjecture1_proved = False.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge12.lean` (namespace `RvMBridge12`, imports
  `E6Bridge6` and `E6Bridge7`, 476 lines).
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge12_probe.lean` (axiom audit of 19
  declarations + 2 probe theorems, signatures, non-triviality of the hypothesis, two load-bearing
  probes).
- This memo.

Not touched: `lakefile.toml`, `AxiomGuardRvMBridge.lean`, every existing `E6Bridge*.lean`. The
integrator wires `E6Bridge12` as a `lean_lib` in `defaultTargets` and adds the guard lines listed at
the end. For the probe run the olean was emitted by hand
(`lake env lean -o .lake/build/lib/lean/E6Bridge12.olean -i .lake/build/lib/lean/E6Bridge12.ilean E6Bridge12.lean`);
a `lake build` after wiring reproduces it.

## The seam

The Wall (seam A, `RvMBridge10.rh_iff_gaussian_positivity`): RH iff for every real centre c and
every lam > 0

    F(c, lam) := Re zeroSide (gaussTest c lam)
               = Re Sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2) >= 0,

gamma_rho = (rho - 1/2)/i, so rho = beta + i t has gamma_rho = t + i (1/2 - beta): real exactly
when rho is on the line. The Turing ladder certifies finitely many ordinate windows to be on the
line. Seam C turns each certified window into positivity of F on a half-line in lam.

## Deliverables (signatures verbatim from `#check`)

```lean
/-- All nontrivial zeros with ordinate within D of c lie on the line. -/
def WindowOnLine (c D : ℝ) : Prop :=
  ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.im - c| ≤ D → ρ.re = 1 / 2

/-- max 1 (B e^{2 (D^2 - 1/4)} / (2 kappa delta^2)), kappa = D^2 - 1/4 - d^2, B = constB c. -/
def lamThreshold (c D d δ : ℝ) : ℝ :=
  max 1 (constB c * Real.exp (2 * (D ^ 2 - 1 / 4)) / (2 * (D ^ 2 - 1 / 4 - d ^ 2) * δ ^ 2))

theorem gaussian_positivity_of_window : ∀ {c D d δ lam : ℝ},
  0 ≤ D → 0 < δ → d ^ 2 + 1 / 4 < D ^ 2 → WindowOnLine c D →
  (∃ ρ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ d) →
  lamThreshold c D d δ ≤ lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem gaussian_positivity_of_window_two : ∀ {c δ lam : ℝ},
  0 < δ → WindowOnLine c 2 →
  (∃ ρ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ 1) →
  lamThreshold c 2 1 δ ≤ lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem gaussian_positivity_of_all_on_line : (∀ (ρ : ℂ), IsNontrivialZero ρ → ρ.re = 1 / 2) →
  ∀ (c lam : ℝ), 0 < lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
```

### Deliverable 2 (the primary instrument): the DOMINANCE form

The landscape numerics (`docs/WALL_LANDSCAPE_2026-09-21.md`, section 2) show the single-near-term
criterion above essentially never holds at real heights (a zero just inside D against one just
outside), while the WHOLE window sum beats the tail at every centre tested, for lam >= 0.27 at
D = 2. So the honest hypothesis is a computable finite inequality on the certified zeros:

```lean
/-- The nontrivial zeros with |Im rho - c| <= D, finite by the local zero count. -/
def zeroWindow (c D : ℝ) : Finset ℂ            -- mem_zeroWindow : ρ ∈ zeroWindow c D ↔ IsNontrivialZero ρ ∧ |ρ.im - c| ≤ D

/-- The FINITE certified window sum. -/
def windowSum (c D lam : ℝ) : ℝ :=
  ∑ ρ ∈ zeroWindow c D,
    (WeilExplicit.zeroMult ρ : ℝ) * ((ρ.im - c) ^ 2 * Real.exp (-(2 * lam) * (ρ.im - c) ^ 2))

/-- The certified tail envelope (tail_bound_window, lam >= 1). -/
def tailEnvelope (c D lam : ℝ) : ℝ := Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * constB c

theorem gaussian_positivity_of_window_dominance : ∀ {c D lam : ℝ},
  0 ≤ D → 1 ≤ lam → WindowOnLine c D →
  tailEnvelope c D lam ≤ windowSum c D lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem re_zeroSide_ge_windowSum_sub : ∀ {c D lam : ℝ},
  0 ≤ D → 1 ≤ lam → WindowOnLine c D →
  windowSum c D lam - tailEnvelope c D lam ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re
```

The key lemma is `re_window_eq_windowSum`: under `WindowOnLine c D` the window part of the zero
side is EXACTLY `windowSum c D lam` (the tsum over the window index set collapses to the finite
Finset sum via `tsum_subtype` + `tsum_eq_sum`, every summand being real by `re_term_of_on_line`).
So the second theorem says: F(c, lam) is the certified window sum plus a tail of modulus at most
`tailEnvelope`, and the certificate margin `windowSum - tailEnvelope` is itself a lower bound for
F. The single-near-zero form (Deliverable 1) is the special case `near_term_le_windowSum` in which
the window sum is bounded below by one of its terms; it is kept because it needs no evaluation, but
the numerics say it is the wrong instrument at real heights.

How a consumer instantiates `hdom`. `windowSum` is a Finset sum over the certified zeros with
their multiplicities (all 1 on the ladder) and ordinates (rational enclosures from the band
modules); `tailEnvelope` needs a numeric UPPER bound on `constB c`, which is an infinite sum over
all zeros and is bounded from the unconditional zero count N(T) (E6Bridge2's Riemann-von Mangoldt),
not from the finite certificate. Both are registry-level certificates, cross-island. The
restriction lam >= 1 comes from the lam = 1 majorant behind `tailEnvelope` (the tail is bounded by
its lam = 1 value times the decay e^{2 (lam - 1)(1/4 - D^2)}); the numerics' validity down to
lam = 0.27 at D = 2 uses the sharper strip bound e^{lam/2} Sum ((t-c)^2 + 1/4) e^{-2 lam (t-c)^2},
which this file does not formalise (it would need a lam-dependent majorant sum; below lam = 1 the
present envelope is still a valid bound but not the numerics' one).

`constB c` is E6Bridge7's lam-independent majorant constant
`Sum_rho m(rho) e^{1/2} (2 c^2 + 13/4) / (1 + |gamma_rho|^2)` (finite by the local zero count,
`Zeta23.WeilEF.zero_sum_inv_sq`). The threshold is explicit and log-free; for the instance
D = 2, d = 1 it is `max 1 (constB c e^{15/2} / (11 delta^2 / 2))`.

Why the near-zero hypothesis has a lower bound delta > 0: a certified zero exactly at ordinate c
contributes 0 (its term is (t - c)^2 e^{...} = 0), so it gives no floor. The honest hypothesis is
a certified zero at distance in [delta, d] from c. Any window of width >= 1 around a real height
above 14 contains such a zero in practice (zero density (1/2 pi) log(t/2 pi) per unit height), but
the theorem does not assume that; it consumes the zero as a hypothesis too.

## The argument (as formalised)

1. `re_term_of_on_line`: for rho on the line the summand is real,
   Re term = m(rho) (Im rho - c)^2 e^{-2 lam (Im rho - c)^2} >= 0 (`re_term_nonneg_of_on_line`);
   for a non-zero the summand is 0 (`term_eq_zero_of_not_nontrivial`).
2. `zeroSide_split`: the zero sum is (sum over |Im rho - c| <= D) + (sum over the complement),
   both absolutely convergent (`summable_gauss_zeroSide`, `Summable.tsum_add_tsum_compl`).
3. `re_window_ge_term`: under `WindowOnLine c D` every window summand has Re >= 0, so the window
   sum is >= the single near term, and `near_term_ge` bounds that term below by
   delta^2 e^{-2 lam d^2} (multiplicity >= 1 from `Zeta23.zetaSeam.one_le_mult`).
4. `phi_le_of_far`: outside the window phi_c(rho) = (1/2 - Re rho)^2 - (Im rho - c)^2 <= 1/4 - D^2.
   `norm_term_le_tail`: for lam >= 1, |term| <= e^{2 (lam - 1)(1/4 - D^2)} |term at lam = 1|,
   and the lam = 1 term is bounded by E6Bridge6's strip majorant (`norm_gaussTest_mul_le`), so
   `tail_bound_window`: ||tail|| <= e^{2 (lam - 1)(1/4 - D^2)} constB c.
5. `tail_le_near_of_threshold`: for lam >= lamThreshold the tail envelope is below the near floor,
   via e^{-2 lam kappa} (2 lam kappa) <= 1 (from 1 + x <= e^x). Assembly: `linarith`.

The forward half of the Wall (`gaussian_positivity_of_all_on_line`) is the same step 1 applied to
every summand: with all zeros on the line every term is real and >= 0, so Re of the tsum is >= 0
(`Complex.re_tsum`, `tsum_nonneg`). No split, no threshold, every lam > 0.

## Load-bearing probes (the on-line hypothesis cannot be dropped)

- `re_term_neg_of_off_line` (probe file, axiom-clean): an OFF-line nontrivial zero at ordinate c
  contributes a strictly NEGATIVE summand, -m y^2 e^{2 lam y^2} with y = 1/2 - Re rho. So the
  termwise nonnegativity in step 1 fails exactly on the zeros `WindowOnLine` does not cover.
- `some_gauss_negative_of_off_line_zero` (probe file, axiom-clean): if any nontrivial zero is off
  the line then some F(c, lam) < 0 with lam > 0. This is E6Bridge7's `gaussian_dominance` read
  contrapositively: the conclusion of `gaussian_positivity_of_all_on_line` fails somewhere
  whenever its hypothesis fails.
- Elaboration check (scratch, not in repo): the same statement with `hwin` removed does not
  elaborate:
  ```
  error: Application type mismatch: The argument hnear has type
    ∃ ρ, IsNontrivialZero ρ ∧ δ ≤ |ρ.im - c| ∧ |ρ.im - c| ≤ d
  but is expected to have type
    RvMBridge12.WindowOnLine ?m.70 D
  ```
- `#guard_msgs`: `WindowOnLine c D` is neither closed nor refuted by `simp` at any (c, D).

## Hookup: how the ladder supplies `WindowOnLine` (registry-level, NOT a Lean import)

What the ladder proves. The zeta_zero_localization island (a DIFFERENT toolchain, v4.32; it cannot
be imported into the v4.33.0-rc2 rvm_bridge island) carries 642 height-chain modules
`AllZeros_h1000.lean` ... `AllZeros_h640000.lean`. The top rung
`AllZeros_h640000.all_nontrivial_zeros_up_to_height_640000_of_bands` concludes

    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 640000 → ρ.re = 1/2

GIVEN one `BandHyp` binder per 1000-height segment (each `BandHyp` = every zeta zero in the
stretched strip box `[1/4000000, 3999999/4000000] x [bLo i, bHi i]` is on the line; discharged by
the kernel-checked `RHInBoxT_*` band modules with their documented Arb non-kernel inputs: winding
counts, on-line zero lists, boundary non-vanishing bundles) and the height-floor hypothesis
`hγ : ∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → 55/16 ≤ |ρ.im|`. The registry statement is
the hypothesis-free conclusion (ANDÚRIL node `AND.ladder_h280000`, `Statements.AND_ladder_h280000`,
status open until the StripClear two-box capstone glue discharges the binders; the 640000 rung has
no registry node yet). The `hγ` floor and the conjugation symmetry are the two small facts the
ladder's positive-ordinate conclusion needs to reach a two-sided window.

The instantiation. `WindowOnLine c D` asks for every nontrivial zero with |Im rho - c| <= D to be
on the line. For 0 <= D and D <= c <= T - D the window [c - D, c + D] sits inside (0, T], so the
ladder's conclusion (with `IsNontrivialZero ρ → riemannZeta ρ = 0` and `0 < ρ.im` from
`c - D >= 0` plus the height floor) gives it directly. For c in [-(T - D), -D] use the conjugation
symmetry `riemannZeta (conj s) = conj (riemannZeta s)` (Mathlib: `riemannZeta_conj`) to reflect
the window to positive ordinates. For |c| < D the window crosses the real axis and additionally
needs "no nontrivial zero with Im rho = 0" (classical, zeta has no real zeros in (0, 1); not needed
by the ladder, whose conclusion is only for 0 < Im). Concretely, for the memo's instance D = 2:
WindowOnLine c 2 for every 2 <= |c| <= 639998.

This is a registry-level composition: a node `RH_wall_window_positivity` (or similar) would take
the ladder node's hypothesis-free conclusion as a `depends_on` and `WindowOnLine c D` as its
instantiation, with `RvMBridge12.gaussian_positivity_of_window` as the artifact. It cannot be a
Lean import: different toolchains, different Mathlib pins, and the ladder's artifact still carries
its BandHyp binders (the ANDÚRIL node is open for that reason). The near-zero hypothesis
`∃ ρ, IsNontrivialZero ρ ∧ δ ≤ |Im ρ - c| ∧ |Im ρ - c| ≤ d` is supplied by the same ladder: each
band module lists its on-line zeros with rational enclosures, so for any c in the certified range a
listed zero within 1 of c at distance >= delta is read off the enclosure (delta = the enclosure
margin, order 10^-6 in the current bands). `constB c` is a genuine real number for every c
(E6Bridge6 summability) but the theorem does not need its value: the threshold is stated in terms
of it, and any numeric upper bound on constB c (from the explicit zero count N(T) = (T/2 pi)
log(T/2 pi e) + O(log T), E6Bridge2) gives a numeric lam1.

## The certified region of the (c, lam) quadrant, in words

The Wall is the whole closed quadrant Q = {(c, lam) : c real, lam > 0}. Seam C certifies, for
every c with a certified window and a certified near zero,

    {(c, lam) : |c| in [D, T - D], lam >= lamThreshold(c, D, d, delta)},   T = 640000,

i.e. a horizontal strip in c (all certified heights, both signs) above an explicit lam-curve
lamThreshold(c) = max(1, constB(c) e^{2 (D^2 - 1/4)} / (2 kappa delta^2)) that grows like c^2
(through constB's (2 c^2 + 13/4) factor) and like 1/delta^2 in the near-zero margin.

With the dominance form the certified set is instead {|c| in [D, T - D], lam >= 1, hdom(c, lam)
certified}: in lam the region is whatever the finite certificate checks, above lam = 1; the numerics
say the check passes from lam = 0.27 (D = 2) at every c tested, so on the formal side the lam >= 1
floor of `tailEnvelope`, not the certificate, is the binding constraint near the bottom.

Seam B (parallel agent, small lam) covers the complementary region in lam: for each c, an interval
0 < lam <= lam0(c) obtained from the lam -> 0 asymptotics of F. Together the certified region is

    {|c| <= T - D, lam >= lamThreshold(c)}  union  {seam B: lam <= lam0(c)},

and the UNCERTIFIED residual, the Wall proper, is

    (i)  every c with |c| > T - D (beyond the ladder), all lam > 0;
    (ii) for |c| <= T - D, the middle band lam0(c) < lam < lamThreshold(c) unless the two seams
         overlap (whether they do for any c is the question seam B and the numerics agent settle;
         seam C alone says nothing about it).

Region (i) is not a technical gap: shrinking it to nothing is exactly proving RH, since
`gaussian_positivity_of_all_on_line` + `rh_iff_gaussian_positivity` show the family of certified
windows would have to be all of them. Region (ii), if nonempty, is a gap in the instrument (the
threshold constant is crude: log-free 1/(2 lam kappa) in place of e^{-2 lam kappa}, and the tail
uses the lam = 1 majorant rather than the lam-optimal one); it can be narrowed by sharper
constants but not closed by them, since the certified windows are finite.

## Lemma list (all `[propext, Classical.choice, Quot.sound]`)

`WindowOnLine` (def), `windowOnLine_of_all_on_line`, `winSet` (def), `tailWeight` (def),
`tailWeight_nonneg`, `summable_tailWeight`, `tsum_tailWeight`, `lamThreshold` (def),
`one_le_lamThreshold`, `re_term_of_on_line`, `re_term_nonneg_of_on_line`,
`term_eq_zero_of_not_nontrivial`, `re_term_nonneg`, `near_term_ge`,
`gaussian_positivity_of_all_on_line`, `summable_term_subtype`, `zeroSide_split`,
`re_window_ge_term`, `phi_le_of_far`, `norm_term_le_tail`, `tail_bound_window`,
`tail_le_near_of_threshold`, `gaussian_positivity_of_window`, `gaussian_positivity_of_window_two`,
`zeroWindowSet` (def), `zeroWindowSet_finite`, `zeroWindow` (def), `mem_zeroWindow`, `windowSum` (def),
`windowSum_nonneg`, `tailEnvelope` (def), `tailEnvelope_nonneg`, `re_window_eq_windowSum`,
`gaussian_positivity_of_window_dominance`, `re_zeroSide_ge_windowSum_sub`, `near_term_le_windowSum`.
Probe file: `re_term_neg_of_off_line`, `some_gauss_negative_of_off_line_zero`.

## Guard lines for the integrator (AxiomGuardRvMBridge.lean, not edited here)

```lean
import E6Bridge12
#print axioms RvMBridge12.gaussian_positivity_of_window
#print axioms RvMBridge12.gaussian_positivity_of_window_two
#print axioms RvMBridge12.gaussian_positivity_of_window_dominance
#print axioms RvMBridge12.re_zeroSide_ge_windowSum_sub
#print axioms RvMBridge12.gaussian_positivity_of_all_on_line
```
and `"E6Bridge12"` in `defaultTargets` plus a `[[lean_lib]] name = "E6Bridge12"` stanza.

## What stopped me

Nothing in scope. E6Bridge10 (seam A) is now on the island; `gaussian_positivity_of_all_on_line` stays
self-contained rather than citing `RvMBridge10.rh_implies_gaussian_positivity`, so this file does
not depend on E6Bridge10. Not done, by design: the registry node itself (registry agent's call), any
numeric value of `constB c` or of `lamThreshold`, and the two small ladder-side facts (conjugation
reflection for negative c, the real-axis exclusion for |c| < D) that live on the other island.
