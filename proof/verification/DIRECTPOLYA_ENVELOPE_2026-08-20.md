# DirectPolya per-child envelope for the config g-step (Case 2 reframe) — 2026-08-20

`conjecture1_proved = False` (untouched).

Target: the config g-step of `R3Cert.CappedJointConfig` (commit `036fa9e`). For every
achievable child config `l = [μ₁ … μⱼ]` with `μᵢ ∈ (0, ½]`,

```
gstep_factor(l) = baseOf(l)¹¹ · ∏ᵢ Bcap(μᵢ) / DENOM  ≤  1
```

with `W = 64/621`, `GAMMA = W²(5/3)¹¹`, `DENOM = W(5/3)¹¹`,
`glemma(μ) = GAMMA/(1+μ/3)¹¹`, `master_ub(μ) = W(3/(2+μ))¹¹`,
`Bcap(μ) = min(master_ub, glemma, 1)`, `baseOf(l) = (3d+3S+1)/(3d)`, `d = j+1`, `S = Σμᵢ`.

`Case2Property` (the `base > threshold` half) is the genuine analytic wall. The **DirectPolya**
idea: replace the kinked per-child cap `Bcap` by a low-degree per-child **envelope** `φ(μ) ≥
Bcap(μ)` so both remaining obligations become Positivstellensatz-shaped (Handelman / Bernstein).

Everything below is exact rational arithmetic, re-derived and re-verified by
`proof/verification/directpolya_envelope_probe.py` (`run_all()` → ALL EXACT CHECKS PASS).

---

## (a) Bcap structure on (0, ½] and the knee μ_c

**`master_ub` is never the minimum** on (0, ½]. The ratio

```
master_ub/glemma = (1/W)(3/5)¹¹ · ((3+μ)/(2+μ))¹¹
```

is decreasing in μ; its minimum over [0, ½] is at μ = ½, equal to `(1/W)(21/25)¹¹`. Hence
`master_ub ≥ glemma` everywhere on the box, certified by the exact integer inequality

```
621 · 21¹¹  =  217522327836719241   ≥   64 · 25¹¹  =  152587890625000000.
```

So on (0, ½]:  **`Bcap(μ) = min(1, glemma(μ))`.** (Grid cross-check: 240 points, 0 exceptions.)

**Knee μ_c** (where `glemma = 1`): exact algebraic condition `(3+μ_c)¹¹ = 5¹¹ W² =
200000000000/385641`, i.e. `μ_c = 5·(64/621)^(2/11) − 3 ≈ 0.30774`. Rational bracket
`μ_c ∈ (73/240, 74/240)` ≈ (0.30417, 0.30833). (The task-brief figure 0.3055 was an
approximation; the exact condition above governs, and gives 0.30774.)

## (b) The envelope and its E2 slack cost

```
φ(μ) = min(1, 87/50 − 12/5·μ)  =  { 1                on [0, 37/120],
                                   { 87/50 − 12/5·μ   on [37/120, ½] }
```

Clean coefficients: the line hits **1 exactly at μ = 37/120** (`87/50 − 12/5·37/120 = 50/50 = 1`,
continuous, no jump) and `27/50` at μ = ½.

- `φ ≤ 1` everywhere ⇒ **monotone-safe**: within a cell, adding a child multiplies the product
  by `φ ≤ 1`, so it never inflates the box maximum (mirrors the leaf-child handling in Lean).
- `φ ≥ Bcap`:
  - on `[0, 37/120]` by `Bcap ≤ 1` (existing `CappedJointConfig.Bcap_le_one`) — **no finder** needed;
  - on `[37/120, ½]` by `φ ≥ glemma` = the E1-upper certificate below.

I anchor the knee at the rational `37/120` (just above μ_c) rather than at μ_c itself (irrational),
so on `[37/120, ½]` we have `glemma < 1` and the flat piece `φ = 1 ≥ glemma` needs nothing there;
the line dominates `glemma` on the upper interval by convexity of `glemma`.

**E2 slack cost.** At the j = 2 worst point (symmetric, at the knee) the true `gstep_factor` is
`0.72294` (margin 0.27706). With the envelope the worst becomes `0.73998` (margin **0.26002**).
The envelope eats only **0.01704** of margin — comfortably inside the available slack.

(Note: my re-derived j = 2 true margin is 0.277, not the brief's 0.325; the brief's figure and its
`89/240` worst point do not reconcile with the exact kernel definitions. My 0.277 at the knee is
the value the Lean `Bcap = min(1, min(glemma, master_ub))` actually produces. The smaller margin is
the honest, more conservative number and still leaves the envelope feasible.)

## (c) Certificates found (Handelman = nonnegative combination of box-constraint products)

All found via the **Bernstein basis on the box** (a subcone of the Handelman cone: each Bernstein
basis element `C(n,k)(μ−a)ᵏ(b−μ)^{n−k}/(b−a)ⁿ` is a nonnegative multiple of a product of the two
box constraints). Each certificate is **exact-reconstruction-verified** (`p − Σ = 0` in ℚ) with
every coefficient a nonnegative rational.

| obligation | region | degree | terms | min Bernstein coef | recon exact |
|---|---|---|---|---|---|
| **E1-upper** `φ_line·(1+μ/3)¹¹ − GAMMA ≥ 0` | `[37/120, ½]` | 12 | 13 | 0.005770 | yes |
| **E2 j=2 UU** `DENOM − base²¹¹·φ(x)φ(y)` | `[37/120,½]²` | 12×12 | 169 | 7.28437 | yes |
| **E2 j=2 LU** `DENOM − base²¹¹·φ(y)` | `[0,37/120]×[37/120,½]` | 11×12 | 156 | 7.51568 | yes |
| **E2 j=2 LL** `DENOM − base²¹¹` | `[0,37/120]²` | 11×11 | 144 | 7.78953 | yes |

`base2 = (10 + 3x + 3y)/9` is `baseOf([x,y])` (d = 3). The four cells partition `[0,½]²`
at the knee; UU (both children on the line) is the binding cell (smallest margin).

The generic `find_handelman_certificate` subset search does not scale to degree 12 (it enumerates
`combinations` over ~91 constraint products); the Bernstein construction supplies the same
Handelman certificate directly and exactly. Both routes land in the identical certified cone —
Telperion's certifier re-verifies the identity + nonnegativity regardless of how the terms were
found (the finder is untrusted).

**Refusals:** the naive single global secant line (extending `φ_line` onto `[0, 37/120]` without
the `min(1,·)` cap) is **NOT** a valid envelope — it exceeds 1 for small μ, so a config of many
tiny children multiplies many `φ > 1` factors and E2 fails for j ≥ 5 (`gstep_env = 1.125` at
j = 5 all-tiny, `1.66` at j = 6). The `min(1, ·)` cap is load-bearing; this is the documented
"φ can exceed 1 below μ_c" hazard.

## (d) j ≥ 3

There is **no simple j → j+1 induction**: `gstep_factor(l + [μ]) ≤ gstep_factor(l)` is FALSE.
Exact witness: `l = [1/240, 1/80]`, `μ = 79/240` gives ratio ≈ 1.584 > 1 (adding a moderate child
raises the base by more than `φ(μ) < 1` suppresses, because this config's base is far below
saturation).

However the **box maximum decreases with j** (margins grow: j=2 → 0.260, j=3 → 0.287, j≥4 → ≥0.294
for the envelope), so each fixed j is independently certifiable and higher cells are strictly
easier. The j = 3 binding cell (all three children on the line, `[37/120,½]³`) has an
all-nonnegative 3-D tensor-Bernstein certificate (min coef 8.146, verified in `run_all()`).

There is **no structural `j ≤ 2` cap** in the config formalization — `Case2Property` quantifies
over `l : List ℚ` of arbitrary length (the memory's `j ≤ 2` refers to the older single-hub degree
bound, not this config g-step). So: **j = 2 fully certified (all cells)**; a per-j finite emission
closes any bounded j; **unbounded j remains a genuine open item** for the envelope route (needs
either a structural degree cap or a meta-argument that box-max is monotone-decreasing in j, which
I could not reduce to the j = 2 cell).

## (e) Lean port — E1-upper EMITTED + COMPILED; which kernel bricks the cells connect to

**E1-upper is emitted and kernel-checked.** The 13-term Handelman certificate was run through the
real `HandelmanEmitter` (`certify_handelman_point` → 14 checks, then `emit_body`) producing
`telperion/examples/g1_floors/lean/DirectPolyaE1.lean`:
`theorem DirectPolya.directpolya_e1_upper : ∀ mu : ℝ, 0 ≤ (120mu−37)/120 → 0 ≤ (1−2mu)/2 →
0 ≤ p(mu)` where `p` is the cleared-denominator E1-upper polynomial. `lake build DirectPolyaE1`
is **GREEN** (Lean 4.32.0, mathlib v4.32.0 cache), and
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`.
The E2 cell certificates (2-var) emit the same way (not yet run through the emitter/build in this
probe).


The DirectPolya route reshapes `Case2Property` into finder-emittable obligations:

- **E1 (per-child envelope domination).** Prove `φ(μ) ≥ Bcap(μ)` as a lemma feeding the config
  recursion. Lower piece `[0,37/120]`: `φ = 1 ≥ Bcap` is `CappedJointConfig.Bcap_le_one` (already
  kernel-green). Upper piece `[37/120,½]`: `φ_line·(1+μ/3)¹¹ ≥ GAMMA` — emit via the Handelman
  emitter from the 13-term certificate (all products `(μ−37/120)ᵏ(½−μ)^{12−k}`); `ring` + `linarith`.
- **E2 (config bound under the envelope).** With `Bcap` replaced by `φ`, the g-step factor is
  `baseOf¹¹·∏φ / DENOM`. For j = 2, the three cell certificates (UU/LU/LL) discharge
  `DENOM − base²¹¹·φφ ≥ 0` on each cell; emit via the Handelman emitter (2-var, box constraints
  `x−x₀, x₁−x, y−y₀, y₁−y`). Then `gstep_le_one`'s Case-2 branch is discharged for j = 2 by these,
  in place of the abstract `Case2Property` hypothesis.
- Existing bricks the cells sit next to: `GStepCore.cert_j1` (j = 1, done — `64·17¹¹ ≤ 621·14¹¹`,
  do not redo), `GStepCore.cert_q2` / `frac_q2` (the arm q = 2 rational cert),
  `CappedJointConfig.gstep_le_one` (the Case-1/Case-2 split this feeds),
  `GLemma.gstep_lt_gamma` (the single-hub g-step capstone upstream).
- **What remains for a full Lean port:** the E1 domination lemma must be threaded through the
  actual `prodBcap`→`prodφ` substitution in the recursion (an envelope-monotonicity step,
  `∏Bcap ≤ ∏φ`), and the j ≥ 3 cells need per-j emission or the missing monotone-in-j argument.
  The pure-leaf face (equality at the arm) stays split off and is never certified with margin.

## (f) Files

- `proof/verification/directpolya_envelope_probe.py` — exact, self-verifying `run_all()`.
- `proof/verification/DIRECTPOLYA_ENVELOPE_2026-08-20.md` — this note.

## (g) Honest open items

1. **Unbounded j.** j = 2 certified; no j → j+1 induction; no structural `j ≤ 2` cap in this
   formalization. Needs per-j emission (bounded j) or a box-max-monotone-in-j lemma (unbounded).
2. **E2 cells not yet emitted/built.** E1-upper is emitted + `lake build` GREEN + clean axioms
   (see (e)). The three j = 2 E2 cell certificates (2-var Handelman) are exact-verified in ℚ but
   not yet run through the emitter/build; the generic `find_handelman_certificate` does not scale
   to these degrees, so emission uses the supplied Bernstein terms through the checker path.
3. **Envelope-substitution step** `prodBcap ≤ prodφ` (from per-child `Bcap ≤ φ`) is a
   straightforward monotone-product lemma but is not yet in the Lean.
4. `Case2Property` itself remains the stated open hypothesis in `gstep_le_one`; this probe shows a
   concrete, certificate-backed route to discharge its j = 2 instance, not a discharge of the
   whole (all-j) property.
