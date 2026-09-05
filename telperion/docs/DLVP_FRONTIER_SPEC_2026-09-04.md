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
| 2. Herglotz/BC sum bound | prove (BC-SUM): apply `borel_caratheodory_deriv` to a branch of `log ζ` (or `-ζ'/ζ` via Hadamard) on a disk about `1+iγ`, boundary bound from the crude `zeta_strip_bound` `|ζ| ≤ C|t|` | OPEN — the analytic core |
| 3. Pole bound `hpole` | `-Re(ζ'/ζ)(σ) ≤ 1/(σ-1) + A`: split off the simple pole at `s=1` (`residue_logDeriv` gives the `1/(s-1)`), bound the regular part by BC | OPEN |
| 4. Double bound `htwo` | `-Re(ζ'/ζ)(σ+2iγ) ≤ A·L`: (BC-SUM) at height `2γ` with no forced pole (drop ALL zeros, nonneg) | OPEN — a corollary of rung 2 |
| 5. Assemble | feed 1/3/4 into `dlvp_core_estimate` → `dlvp_region_gap` → optimize `σ = 1 + c/L` → `β ≤ 1 - c'/L` | OPEN — real-algebra, mostly `nlinarith` |

Rung 2 is the genuine hard core (BC applied to ζ with zeros present needs the Hadamard
factorization so `log ζ` is replaced by the entire part). Rungs 4-5 are largely mechanical
once 2 lands; rung 3 is a localized version of 2 at `s=1`.

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
