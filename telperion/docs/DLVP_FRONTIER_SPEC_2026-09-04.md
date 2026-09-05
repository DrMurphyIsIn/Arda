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

These two are the genuine multi-session analytic core (setting up the disk, ζ analyticity
away from `s=1`, applying `sum_divisor_le` with `M = C|t|`, connecting `divisor` to the
partial fraction, and `borel_caratheodory_deriv` to `E`). The reduction skeleton and the
combine are complete; what remains is (i)+(ii) against ζ. Optimizing `σ = 1 + c/L` on
`dlvp_region_gap`'s output → `β ≤ 1 - c/log|t|` is the final real-algebra step, gated on (i)+(ii).

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
