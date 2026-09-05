# de la Vallée Poussin zero-free region — effort spec (opened 2026-09-04)

Goal: discharge the CONDITIONAL `dlvp_core_estimate` (ZeroFreeRegion.lean) to obtain the
dVP region `Re s > 1 − c/log|t|` — strictly stronger rate than the kernel-locked polylog
region `Re s > 1 − c/(γ⁴(1+log2γ))`. This is a genuine multi-session formalization; it is
NOT a proof of RH (`conjecture1_proved = False`). Value is methodological (the dVP region
is duplicative of strongpnt/PrimeNumberTheoremAnd, but a from-scratch kernel-clean route).

## Current state (what's proved)

- `dlvp_core_estimate (σ t β k A L)` — PROVED, but takes the three `-Re(ζ'/ζ)` bounds
  (`hpole`, `hzero`, `htwo`) as HYPOTHESES. Uses `zeta_logDeriv_comb_nonneg` (the 3-4-1
  Mertens positivity, PROVED in ZeroFreeBridge.lean).
- `dlvp_region_gap` — PROVED; turns the core estimate into the cleared region gap
  `(σ-1)(1 - (σ-1)B) ≤ (1-β)(3 + (σ-1)B)`, `B = 3A+5AL`.
- `BorelCaratheodory.lean` — 0-sorry (value form `borel_caratheodory_value`, derivative form
  `borel_caratheodory_deriv`): abstract BC for a holomorphic `f` on `ball 0 R`.
- Mathlib v4.32 HAS `Analysis/Complex/{Hadamard,JensenFormula}` and
  `Analysis/Complex/ValueDistribution/{Cartan,LogCounting,Proximity,FirstMainTheorem}`.

The audit (rh_corpus_audit) flags `dlvp_core_estimate`/`dlvp_region_gap` as DEAD — proved
but unwired, because nothing produces `hpole`/`hzero`/`htwo`. Producing those IS the frontier.

## The ladder (each a discrete, verifiable unit)

The three hypotheses all come from ONE analytic object — the Borel-Carathéodory bound on the
Hadamard zero-sum for `-ζ'/ζ`:

    (BC-SUM)   -Re(ζ'/ζ)(s)  ≤  A·L  −  Σ_ρ Re(k_ρ/(s-ρ)),   L ~ log|t|,

valid for `Re s = σ` slightly `> 1`, the sum over nontrivial zeros ρ (all `Re ρ ≤ 1`).

| Rung | Statement | Status |
|---|---|---|
| **1. Zero-extraction core** | at the zero's height `Re(k/(s-ρ₀)) = k/(σ-β)`; other zeros `Re(1/(s-ρ')) ≥ 0` ⇒ `hzero` reduces to (BC-SUM) | **DONE** — `DlvpZeroSum.lean`, kernel-clean |
| 2. Herglotz/BC sum bound | prove (BC-SUM). COMBINE step DONE (`DlvpBCSum.lean` `bc_sum_of_split`): reduced to two analytic inputs — see below | **COMBINE DONE; two analytic inputs OPEN** |
| **3. Pole bound `hpole`** | `-Re(ζ'/ζ)(σ) ≤ 1/(σ-1) + A`: at real σ the pole term `Re(1/(σ-1)) = 1/(σ-1)` exactly; `hpole_of_partialfraction` reduces it to the partial-fraction bound | **DONE** — `DlvpPole.lean`, kernel-clean |
| **4. Double bound `htwo`** | `-Re(ζ'/ζ)(σ+2iγ) ≤ A·L`: the zero sum is nonneg (`sum_re_inv_sub_nonneg`, via rung 1) so it drops (`htwo_of_bound`) | **DONE** — `DlvpPole.lean`, kernel-clean |
| **5. Assemble** | `dlvp_region_of_bc_inputs`: rungs 1/3/4 → `dlvp_core_estimate` → `dlvp_region_gap` | **DONE** — `DlvpPole.lean`, kernel-clean |

**MILESTONE (rungs 1,3,4,5 done):** the entire dVP region GAP reduces, kernel-clean, to the
three Borel–Carathéodory inputs (`dlvp_region_of_bc_inputs`).

**RUNG 2 COMBINE done (`DlvpBCSum.lean`, kernel-clean):** `bc_sum_of_split` derives BC-SUM
`-Re(ζ'/ζ) ≤ A·L - Re(Z)` from the log-derivative split `ζ'/ζ = Z + E` (Z = Herglotz zero
sum) plus the entire-part bound `‖E‖ ≤ A·L`. `htwo_of_bc_split` composes it with rung 4.
This reduces rung 2 to **two named analytic inputs, each now backed by a located Mathlib API**:

- **(i) the partial-fraction split** `ζ'/ζ = Z + E` on a disk about `2+iγ` — via the Jensen
  divisor machinery `AnalyticOnNhd.circleAverage_log_norm` (`Mathlib.Analysis.Complex.JensenFormula`).
- **(ii) the entire-part bound** `‖E‖ ≤ A·L` — `borel_caratheodory_deriv`
  (`telperion/examples/borel_caratheodory`, 0-sorry) with the zero count from
  `AnalyticOnNhd.sum_divisor_le` (Jensen, Mathlib v4.32) and boundary bound `zeta_strip_bound`.

**ANALYTIC CORE — zero-count DONE UNCONDITIONALLY (`DlvpZetaDisk.lean`, kernel-clean):**
genuinely-analytic ζ facts (not reductions):
- `zeta_ne_zero_of_one_lt_re` — `ζ c ≠ 0` for `Re c > 1` (`sum_divisor_le` hyp 2);
- `zeta_analyticOnNhd_disk` — ζ analytic on a closed disk avoiding `s = 1` (hyp 1);
- `zeta_sphere_bound` — the explicit boundary bound `‖ζ‖ ≤ (‖c‖+R)/(c.re-R-1) + (‖c‖+R)/(c.re-R)`
  on the sphere, from `zeta_strip_bound` (`O(|γ|)`) — discharges hyp 3;
- `zeta_zero_count_le` — the Jensen zero-count applied to ζ (boundary bound as hypothesis);
- `zeta_zero_count_unconditional` — **hypothesis-free** `O(log|γ|)` ζ-zero count: combines the
  three ingredients, discharging the ZERO-COUNT half of obligation (ii).

**OBLIGATION (i) CORE — the partial-fraction split DONE (`DlvpHerglotz.lean`, kernel-clean):**
from the canonical factorization `f = (∏_ρ (·-ρ)^{m(ρ)}) · g` (Mathlib
`MeromorphicOn.extract_zeros_poles`), `logDeriv` additivity gives the split
`f'/f = Σ_ρ m(ρ)/(z-ρ) + g'/g` = Z + E:
- `logDeriv_sub_zpow` — one zero factor `(w-ρ)^n` contributes `n/(z-ρ)`;
- `logDeriv_prod_sub_zpow` — the finite Herglotz sum `Σ_ρ m(ρ)/(z-ρ)` (the `Z`-identification);
- `herglotz_split` — the full `f'/f = Z + logDeriv g`.
Function-agnostic; keyed on `logDeriv_prod`/`logDeriv_mul`/`logDeriv_fun_zpow`.

**OBLIGATION (i) FOUNDATIONS DONE (`DlvpEntire.lean`, kernel-clean):**
- `zeta_extract_zeros_poles` (i-a) — **ζ IS the factorization** `ζ = (∏ᶠ_ρ (·-ρ)^{divisor})·g`
  with `g` analytic + zero-free on the disk. All three `MeromorphicOn.extract_zeros_poles`
  hypotheses discharged for ζ: MeromorphicOn (analytic), order ≠ ⊤ everywhere (ζ c ≠ 0 +
  connected disk via `exists_meromorphicOrderAt_ne_top_iff_forall`), finite divisor (compact).
- `differentiableAt_logDeriv` / `analyticOnNhd_logDeriv` (i-b, first half) — the entire part
  `E = logDeriv g = g'/g` is analytic where `g` is analytic + nonzero.

**OBLIGATION (i-a') TRANSFER MACHINERY DONE (`DlvpTransfer.lean`, kernel-clean):** `logDeriv`
is a germ invariant, so a factorization equality transfers to a pointwise `logDeriv` equality:
- `logDeriv_congr_nhds` — germ (nhds) equality ⟹ equal log-derivatives (via `EventuallyEq.deriv_eq`);
- `logDeriv_congr_eqOn_open` — agreement on an open set ⟹ equal log-derivatives there;
- `logDeriv_congr_of_analytic` — two analytic functions on a preconnected open `U` agreeing on a
  NEIGHBORHOOD of some `z₀ ∈ U` have equal log-derivatives at every `z ∈ U` (identity principle,
  `eqOn_of_preconnected_of_eventuallyEq`).

**(i-a'') CODISCRETE TRANSFER DONE (`DlvpTransfer.logDeriv_congr_of_codiscrete`, kernel-clean):**
two analytic functions on a preconnected open `U` agreeing CODISCRETELY (`=ᶠ[codiscreteWithin U]`,
the `extract_zeros_poles` shape) have equal log-derivatives at every `z ∈ U`. Route: codiscrete
membership (`mem_codiscreteWithin_iff_forall_mem_nhdsNE`) → punctured-nhds agreement (drop `Uᶜ`
since `U ∈ 𝓝 z₀`) → `∃ᶠ` (`𝓝[≠]` NeBot on ℂ) → `EqOn` (`eqOn_of_preconnected_of_frequently_eq`)
→ `logDeriv_congr_eqOn_open`.

**(i-a''') finprod↔Finset BRIDGE DONE (`DlvpBridge`, kernel-clean):** `herglotz_split_finprod`
gives `logDeriv ((∏ᶠ..)·g) z = Σ_ρ D(ρ)/(z-ρ) + logDeriv g z`.

REMAINING (2 pieces): the ζ-factorization zero-part is analytic (divisor ≥ 0 since ζ has no poles;
+ `•`↔`*` reconciliation) so `logDeriv_congr_of_codiscrete` applies to ζ vs `(∏ᶠ..)·g`; and (i-b')
the Borel-Caratheodory BOUND `‖E‖ ≤ A·L` (`borel_caratheodory_deriv` on `log g`). Kernel-clean chain:
reduction skeleton (rungs 1,3,4,5) + rung-2 combine + unconditional Jensen zero-count on ζ +
Herglotz split + obligation (i) foundations + (i-a') transfer + (i-a'') codiscrete transfer +
(i-a''') bridge. Optimizing `σ = 1 + c/L` → `β ≤ 1 - c/log|t|` is the final real-algebra step.

## Rung 1 — DONE (this session)

`DlvpZeroSum.lean` (imports ZeroFreeBridge, kernel-clean, CI `rh-dlvp-zerosum`):
- `re_smul_inv_sub_at_equal_height`: `Re(k/((σ+iγ)-(β+iγ))) = k/(σ-β)` — unconditional (the
  `iγ` cancels, leaving a real denominator). The reason dVP evaluates at the zero's height.
- `re_inv_sub_nonneg_of_re_lt`: `Re ρ' < Re s ⇒ 0 ≤ Re(1/(s-ρ'))` — other zeros are droppable.
- `hzero_of_herglotz`: reduces the conditional `hzero` to a single Herglotz-form bound
  `-Re(ζ'/ζ)(s) ≤ A·L - (Re(k/(s-ρ₀)) + rest)`, `rest ≥ 0` — i.e. to (BC-SUM).

Net effect: the `hzero` leg of the frontier is now reduced to rung 2 (BC-SUM). Next concrete
unit: rung 4 (`htwo` as the zeros-dropped corollary), then rung 2 proper.

conjecture1_proved = False.
