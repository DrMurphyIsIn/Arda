# dVP Frontier — Session Relay (2026-09-07)

**For:** the parallel RH-in-a-box session.
**Scope:** the classical de la Vallée Poussin (dVP) zero-free-region reduction in
`telperion/examples/zero_free_bridge/lean/`.
**Branch:** `bg/scl-lean` (push here; merge to `main` via `gh pr merge --admin --merge`). HEAD `03f9960`.
**Status invariant:** `conjecture1_proved = False`. This is a *reduction*, NOT a proof of RH. Every
theorem below is kernel-verified (`#print axioms` = `[propext, Classical.choice, Quot.sound]` only).
Never commit a `sorry`.

---

## 1. What this frontier is

Goal: discharge the CONDITIONAL `dlvp_core_estimate` → `Re s > 1 − c/log|t|` (the dVP region, stronger
than the kernel-locked polylog region). Everything reduces to three Borel–Carathéodory (BC) inputs on
`−Re(ζ'/ζ)`: the pole bound (`hpole`), the zero bound at height γ (`hzero`), and the height-2γ bound
(`htwo`). All three descend from the Blaschke BC-SUM `bc_sum_blaschke`.

Full context: `telperion/docs/DLVP_FRONTIER_SPEC_2026-09-04.md`. Memory topic:
`rh_dlvp_frontier_2026-09-04` (has the blow-by-blow of ~40 PRs).

---

## 2. THE key structural finding of this session (read this first)

**The top-layer theorem `dlvp_zeta_region_of_canonical_decomp` is OVER-CONSTRAINED — do not target it.**

It uses ONE centre `c₀` and ONE disk for BOTH the height-γ and height-2γ evaluations (two
`bc_sum_blaschke` calls needing `hz₁` AND `hz₂` in `ball 0 R`, plus `hg_bound₁` AND `hg_bound₂` via
`norm_logDeriv_g_le_strip`, which needs `‖z₀‖ < R`). With the natural `c₀ = 2+iγ` the height-2γ point

    σ + 2iγ − c₀ = (σ−2) + γi,   ‖·‖ ≥ |γ| ≥ R+2   (NOT in the small strip disk, R < 3/2)

so `hz₂`/`hg_bound₂` are impossible. The two heights are ≈|γ| apart; they cannot share one disk.

**Correct target: the LOWER layer `dlvp_zeta_region_of_bc_sums` (`DlvpZetaBcBridge.lean`).** It needs
only the two BC-SUM *inequalities* `hbc₁`, `hbc₂` + `hcz₁₂` (ring) + `hdiff₁₂` + `s₁/s₂ ⊆ disk`
(`s₂ = ∅` is fine — `htwo` drops all zeros, `hs₂_dom` vacuous). It does NOT require the eval points in
the disk. So the assembly splits into two independently-centred pieces:
- `hbc₁` (height γ): `bc_sum_blaschke` on the ρ₀-enclosing disk `c₀ = 2+iγ`.
- `hbc₂` (height 2γ): a SEPARATE `bc_sum_blaschke` on a disk around `c₁ = 2+2iγ` (eval `σ+2iγ` at
  distance `2−σ` from `c₁`), then recentred to the `c₀` form via `neg_logDeriv_zeta_recenter_re`.

---

## 3. What this session built (PRs #279–#289, all merged, all kernel-clean)

### The strip machinery — lets the disk dip BELOW Re = 1 (needed to enclose a nontrivial zero)
The pre-existing sphere/count bounds required `R+1 < c.re` (whole disk in Re>1, no zeros). Replaced by
strip-capable versions using `zeta_strip_bound` (already valid on ALL of `stripDomain = {Re>0}\{1}`).

| PR | File | Delivers |
|----|------|----------|
| #279 | `DlvpZetaStripSum` | `norm_partial_sum_le_of_lt_one` — sharp `σ<1` partial Dirichlet sum bound (integral test). |
| #280 | `ZetaLogBound` (appended) | `zeta_strip_growth`: `‖ζ(σ+it)‖ ≤ 5|t|` for `σ∈[1/2,1)`. *(NOTE: partly redundant — `zeta_strip_bound` already gives O(|t|) on the strip. Kept as a clean explicit form.)* |
| #281 | `DlvpZetaSphereLogStrip` | `zeta_sphere_log_bound_strip` + `g_sphere_log_osc_strip` — ζ/g boundary oscillation valid when the sphere dips to `Re>1/2`. Handles ζ possibly vanishing on the sphere via `Real.log 0 = 0 ≤ log U''`. |
| #282 | (append) + `DlvpHALArith` | `norm_logDeriv_g_le_strip` (interior entire-part O(L) bound below Re=1) + `hAL_arith`/`sum_abs_divisor_eq`. |
| #283 | `DlvpZetaCountStrip` | `zeta_sphere_bound_strip` + `zeta_zero_count_strip` — Jensen zero count O(L) on a disk dipping below Re=1 (`zeta_zero_count_le` takes M as a hyp; only needs `1<c.re` at CENTRE + `1∉closedBall`). |

### The concrete instantiation (c₀ = 2+iγ) + corrected-assembly building blocks
| PR | File | Delivers |
|----|------|----------|
| #284 | `DlvpZetaConcrete` | `concrete_hcz` / `concrete_hz_mem` / `concrete_hzne` / `concrete_center_re` / `concrete_hβσ` — the ring/geometry hyps at `c₀=2+iγ`, eval `σ+iγ`. |
| #286 | `DlvpBcSumConcrete` | `bc_sum_concrete` — produces `hbc₁` for the `c₀=2+iγ` disk; discharges `bc_sum_blaschke`'s geometric hyps via `concrete_*`, takes `D`/`hg_bound`/`hAL` as inputs. |
| #287 | `DlvpZetaContSphere` | `zeta_recenter_cont_sphere` — `hf_cont` (ζ(c₀+·) continuous on sphere). Flagged the g-boundary-regularity subtlety. |
| #289 | `DlvpCanonicalClosedBall` | **Boundary regularity RESOLVED** — `g` analytic up to the sphere (see §4). Gives `hg_cont`, `hg_dcc`. |

---

## 4. Boundary-regularity resolution (the one that mattered)

`norm_logDeriv_g_le_strip` needs, on `sphere 0 R`: `hf_cont`, `hg_cont`, `hg_dcc` (`DiffContOnCl g (ball 0 R)`),
`hfg0` (`‖ζ c₀‖ ≤ ‖g 0‖` = `zeta_norm_le_g_zero`, already built).

`hg_cont`/`hg_dcc` looked hard: `D` only gives `g` `MeromorphicNFOn (closedBall)` + zero-free on the
OPEN ball, and `D.eventuallyEq` is `codiscreteWithin (closedBall)` — NO punctured-nbhd control at a
sphere point, so an order-transfer via `meromorphicOrderAt_congr` fails there.

**Resolution (4 lines):** Mathlib's `CanonicalDecomp.divisor_eq_divisor` already proves
`divisor g (closedBall 0 R) x = divisor f (sphere 0 R) x` (sphere case: canonical factors analytic +
non-vanishing ⟹ orders agree). Then:
```lean
rw [← D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd]  -- MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
intro x
rw [D.divisor_eq_divisor hR]
exact hf_sphere.divisor_nonneg x                            -- f = ζ(c₀+·) analytic on sphere ⟹ divisor ≥ 0
```
⟹ `g AnalyticOnNhd (closedBall)`; `.mono sphere_subset_closedBall |>.continuousOn` gives `hg_cont`;
`⟨(.mono ball_subset_closedBall).differentiableOn, closure_ball 0 hR.ne' ▸ .continuousOn⟩` gives `hg_dcc`.

**Lesson: search Mathlib before building.** The order-transfer I twice scoped as "real work / smaller-radius
reformulation" was already `divisor_eq_divisor`. `hg_bound` is now fully unblocked.

---

## 5. Remaining work (precise, in order)

All inputs below are kernel-clean lemmas that exist; what's left is wiring + two concrete analytic bounds.

1. **`hg_bound₁` for `c₀=2+iγ`** — feed the 4 inputs into `norm_logDeriv_g_le_strip`:
   `zeta_recenter_cont_sphere` (hf_cont), `canonicalDecomp_contOn_sphere` (hg_cont),
   `canonicalDecomp_diffContOnCl` (hg_dcc), `zeta_norm_le_g_zero` (hfg0).
   Needs `f = ζ(c₀+·)` analytic on `sphere 0 R` (`zeta_analyticOnNhd_disk` restricted). Produces
   `Bg₁ = 4·Aζ''·(R+‖z₀‖)/(R−‖z₀‖)²`, `Aζ'' = O(L)`.

2. **`hAL₁`** — via `zeta_zero_count_strip` (gives `∑ᶠ divisor ≤ O(log|c.im|)` on inner radius `r`) →
   `sum_abs_divisor_eq` (|divisor|=divisor since ≥0) → `hAL_arith`. **Reconciliation gotcha:** the count is
   a two-scale Jensen bound on an INNER radius `r < R`, while `hAL` sums over the support in `ball 0 R`.
   Pick `r` so `log(R/r)=1` (r=R/e) and note the Herglotz sum is over the same support; identify
   `Ccount·L` with the log bound, choose `A`.

3. **`hbc₁`** — `bc_sum_concrete (σ γ) hR hσ2 hσR g D hf_ana hg_ana hg_ne hfin heval_ne hg_bound₁ hAL₁`.
   Done once 1+2 are.

4. **`hbc₂`** (height 2γ) — a PARALLEL instantiation on `c₁ = 2+2iγ`. `concrete_*` currently hardcode
   `2+iγ`; either generalise them to centre `2+ciγ` or add `2+2iγ` variants. Eval `σ+2iγ` is at distance
   `2−σ` from `c₁` (small, in the disk). Then recentre `logDeriv(ζ(c₁+·))(σ+2iγ−c₁) = ζ'/ζ(σ+2iγ) =
   logDeriv(ζ(c₀+·))(σ+2iγ−c₀)` via `neg_logDeriv_zeta_recenter_re` to match `hbc₂`'s `c₀` form.

5. **`hpole_pf`** — `−Re(ζ'/ζ(σ)) ≤ Re(1/(σ−1)) + A` for real `σ` near 1. Genuine analysis (Laurent of
   `ζ'/ζ` at `s=1`; relates to `tendsto_riemannZeta_sub_one_div` / the `ζ₀` representation in Mathlib's
   `ZetaAsymp.lean`). `DlvpPole` has a monomial version — check reusability.

6. **Final wiring** — feed `hbc₁`, `hbc₂`, `hpole_pf` (+ `hcz₁₂`, `hdiff₁₂`, `hm/hlt/hother` via
   `zeta_divisor_nonneg`/`zeta_zero_re_lt`, `hρ₀`/`hmρ₀` divisor data for the concrete zero) into
   `dlvp_zeta_region_of_bc_sums` → `β ≤ 1 − 1/(112·A·L) = 1 − c/log|γ|`.

Concrete zero geometry that satisfies every strip hypothesis: `ρ₀ = β+iγ` with `1/2 < β < 1`,
`c₀ = 2+iγ`, `R ∈ (2−β, 3/2)` (nonempty iff `β>1/2`; `R < 3/2 = c.re−1/2` ✓), `|γ| ≥ R+2`.

---

## 6. Lean gotchas collected this session

- `AntitoneOn.sum_le_integral_Ico` has `a b : ℕ`, domain `Set.Icc (↑a) (↑b)` (nat-casts, NOT literal `1`);
  yields `∑_{i∈Ico a b} f ↑(i+1)`.
- `Nat.Ico_succ_right` renamed — use `ext; omega` for `Ioc 1 N = Ico 2 (N+1)`.
- `div_le_div₀` is not a lemma name; use `gcongr` for `a/b ≤ c/d` quotient monotonicity (it finds the
  numerator/denominator facts in context).
- `apply_eq_zero_of_analyticOrderAt_ne_zero` beta-reduces `(fun w => ζ(c₀+w)) u` during unification and
  mis-infers `f=ζ, z=c₀+u`; pin `(f := fun w => ζ(c₀+w)) (z₀ := u)`.
- `‖B z‖ = 1` (`norm_finprod_canonicalFactor_zpow_eq_one`) holds on the SPHERE only.
- `Real.log 0 = 0` (Mathlib) — so `log‖ζ z‖ ≤ log U` survives a zero on the sphere when `U ≥ 1`
  (`by_cases ‖ζ z‖ = 0`).
- `hbc₁`'s `.re` is OUTSIDE the Herglotz sum (matches `bc_sum_blaschke`), not inside.
- `open MeromorphicOn` needed for `divisor`; `norm_sub_rev` not `Complex.norm_sub_rev`.

---

## 7. Cross-pollination note

The strip-capable sphere/count pattern (supply the boundary `M` via `zeta_strip_bound` on the full strip
instead of a `Re>1` bound, handle `log 0`) and the `divisor_eq_divisor` → `divisor_nonneg_iff_analyticOnNhd`
route for boundary analyticity are both reusable Telperion-emitter candidates
(cf. `telperion_build_standing_order`). The `bc_sum_blaschke` → two-disk split is the reusable dVP shape.
