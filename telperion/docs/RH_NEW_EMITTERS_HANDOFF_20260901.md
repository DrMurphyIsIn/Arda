# Handoff: new Telperion emitters + lemma pack from the RH review (2026-09-01)

`conjecture1_proved = False`. A review of the whole RH zero-free formalization (~2,500 lines Lean, 64+
theorems, `rh-research-artifacts`) mined the recurring, mechanical, certificate-shaped proof patterns and
crystallized them into Telperion. This handoff is the record of what was added and how to use it.

## What landed (branch `feat/rh-emitters` → merged)

Three new `emit_*.py` + one Lean lemma pack, all self-tested (11 pytest) and **dogfooded** (their Lean
output compiles under CI job `ray-power-and-emitted-compiles`):

### 1. `emit_zero_free_region.py` — the region-assembly emitter (STRONGEST; a genuine computed certificate)
Turns the three elementary-route bounds into a zero-free region. Input `ZeroFreeRegionCert(c1, c2, c4,
theta)` (pole / growth / Cauchy coefficients + growth power). Output: the rate `Re s > 1 - c/|t|^{5θ}`
with `c = 1/(16 c1^3 c2 c4^4)`.
- **Certificate / anti-phantom:** `verify_region` re-derives the substitution of the three bounds into
  the 3-4-1 product SYMBOLICALLY and checks it equals `16 c1^3 c2 c4^4 (1-β) γ^{5θ}` exactly; a wrong
  constant, wrong exponent, or nonpositive coefficient is REFUSED.
- **Emits** the `zeta_zero_free_poly_of`-shaped Lean (`gcongr` / `field_simp; ring` / `nlinarith`).
- **The lever:** `theta = 1` is today's crude `|t|^{-5}`. A SHARPER growth bound (smaller `theta`, e.g.
  from an Euler-Maclaurin `log|t|` bound) feeds the SAME assembly and improves the exponent toward the
  de la Vallee Poussin log-region — **without the Hadamard machinery**. This is where the rate-extension
  work (`ZetaLogBound`) plugs in: finish `zeta_log_bound`, drop its growth power into this emitter, get
  the improved region for free.

### 2. `emit_dominated_integrability.py` — integrable-by-rpow-domination
`b(x)/(x:ℂ)^p` on `Ioi c` (‖b‖ ≤ B) is integrable iff `1 < Re p`. The convergence condition is the exact
gate (`verify_convergence`); divergent instances refused. Emits `Integrable.mono'` proofs + the reusable
shape lemma `integrableOn_bounded_div_cpow`. (Recurred in R2, the tail bound, StripReprR1.)

### 3. `emit_dirichlet_repr.py` — the truncated Euler-Maclaurin representation shape
`ζ(s) = Σ_{n≤N} n^{-s} + N^{1-s}/(s-1) - s∫_{x>N}{x}x^{-s-1}`. The correction-term closed forms are
re-verified by SYMBOLIC DIFFERENTIATION (anti-phantom); emits the statement (proof = the Abel-summation
lemma, `StripReprR1.zeta_partial_sum_repr`). A representation TEMPLATE, honestly: the identity is analytic,
so only the closed forms are finitely certified.

### 4. `RayPowerEstimate.lean` — reusable lemma pack (NOT a certificate emitter)
The cpow/rpow-on-positive-reals primitives that recurred 20+× and cost rounds when re-derived by hand:
`norm_cpow_ofReal`, `norm_natCast_cpow_neg`, `norm_natCast_cpow_one_sub_le_one`, `cpow_neg_mul_self`,
`abs_im_le_norm_sub_one`, `norm_ofReal_le_one`, `integrableOn_Ioi_rpow_neg`. Import this in future
zeta/L-function growth-bound work instead of re-proving. It is a Lean support library, explicitly not a
Telperion certificate.

## What was NOT made an emitter (and why)
- **Nonneg-cosine positivity, preconnectedness, rational identities, SOS/Handelman/Putinar** — already
  covered (`zero_free_cosine`, `preconnected_cover`, `rational_identity`/`facts`, `sos`/`handelman`/
  `constrained_sos`).
- **`residue_logDeriv`, Borel-Caratheodory** — genuine one-off analytic lemmas; better as upstream
  Mathlib PRs than Telperion shapes.

## How to use (region emitter, the headline)
```python
from telperion.emit_zero_free_region import ZeroFreeRegionCert, emit_zero_free_region_lean
import sympy as sp
# current crude-growth region (reproduces zeta_zero_free_poly_of):
print(emit_zero_free_region_lean(ZeroFreeRegionCert(sp.Integer(2), sp.Integer(5), sp.Integer(24)), "my_region"))
```

## Open thread this connects to
The RH **rate extension** (`ZetaLogBound.lean`, banked green foundation, PR #183): 5/6 sharp-bound
sub-obligations green + `zeta_partial_sum_repr` foundation green; REMAINING = the collection (fully
planned in `project_rh_zero_free_formalization` memory) + `zeta_trunc` + `zeta_log_bound`. When that
lands, `emit_zero_free_region` turns it into the improved region automatically. Ceiling unchanged: even
completed, this reaches the CLASSICAL region (already externally formalized, Fejer-capped) — NOT a step
toward RH. `conjecture1_proved = False`.
