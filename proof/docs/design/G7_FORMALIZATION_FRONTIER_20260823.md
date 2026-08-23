# G7 to its ultimate conclusion: the exact formal-proof frontier (2026-08-23)

`conjecture1_proved = False`. This is the definitive audit of what formalizing Brualdi–Goldwasser
Conjecture 1 actually requires — the culmination of the session's investigation. It answers, precisely
and verified against the Lean source on `main`: **how far is the *formal* proof, what Lean theorems
remain, what is load-bearing, and is there a hidden mathematical gap.** The prior passes established the
mathematics is assembled at the Python exact-certificate standard and relocated the frontier to G7 (Lean
formalization). This doc chases that to the end.

## The two standards, made exact

- **Mathematical standard** (exact Python certificates): a rung is "proven" if its full argument is an
  exact-rational self-verifying certificate. By this bar the proof is **one crux (R3, tight) + assembly
  away**, and the crux's one arithmetic subtlety (the marginal tie) is now handled by LPRSC.
- **Formal standard** (Lean, no `sorry`, composed to a top theorem): a rung is "proven" only as a
  kernel-checked term wired into a capstone. **By this bar the proof is a large, mostly-unclimbed
  mountain** — detailed below.

## What is FORMALLY proven (Lean, no sorry, unconditional) — verified on `main`

| piece | Lean | content |
|---|---|---|
| **R3 weak** | `PotentialFinal.phi_le_one` | `logPhi b ≤ 0` ∀ Branch (via `deficitNonneg_holds` ← `starBound_holds`) |
| **bridge, all trees** | `R47Tree.pi_utree` | `per(L(T))/∏deg = Aobj t` ∀ rooted tree |
| **bridge, amplitude** | `BridgeStep4j.amplitude_bridge_real'`, `BridgeStep4k.amplitude_limit_le_tie` | unconditional Tendsto + tie bound |
| **marginal-tie primitive** | `R3Cert.LPRSC` (`family_ge_one`, `family_gt_one_off_tie`) | the integrality-aware tie cert (CI-pending fix) |
| **R47 bricks** | ~94 theorems across `R47Tree/Head/Parse/Rate/Backbone/Cert/Dispatch/Step` | merge-cell certs, dispatch, parse, backbone |

## What is FORMALLY PARTIAL — the G7 gap (verified, quoting the source)

1. **R47 merge cells: 1 of 36.** `R47Cert.lean` (own honest scope): *"1 of 36 cells; the other 35 are
   the same pipeline (P4b+, generated)."* Mechanical, but 35 cells unwritten.
2. **The per-step monotonicity SEAM is not started.** `R47Cert.lean`: *"The seam from D ≥ 0 to actual
   `Aobj` monotonicity of a `Step` (the environment factorization `pi(T'')−pi(T) = Penv·FQ·FSr·D`) is a
   LATER phase — nothing here asserts per-step monotonicity."* This is the load-bearing link from the
   cell certs to actual tree-domination.
3. **No top-level capstone.** There is **no** Lean theorem stating conjecture1 (the near-star tie
   maximizes `per(L(T))` over n-vertex trees) or the composed R1–R7. The bridge (`pi_utree`) and the
   crux (`phi_le_one`) exist but are not composed to the maximizer statement.
4. **Conditional theorems awaiting discharge.** e.g. `GLemmaAssembly.glemma_step (h2 : Case2Property)` —
   conditional on `Case2Property` (false on μ∈(½,1); achievable messages satisfy μ≤½, the relocated
   integrality content). Discharge-in-Lean status must be confirmed per theorem.

## What is MATHEMATICAL (Python-cert) but NOT YET FORMAL

- **R1, R2, R4, R6** rung rate/reduction arguments — exact Python certs (`spiders.py`, `legs.py`,
  `psi_close.py`, `distribution.py`), not Lean rung theorems.
- **Amortized hub bound** (the accumulation boundary) — `amortized_hub_bound.py` EXIT 0, not Lean.
- **R7' stage assembly** (I–IV) — `verify_20260814.py` all-green, not Lean.
- **Context-free floors** — partly Lean (floor bricks), partly Python (`g1_endpoint_certificates`).

## The critical path to a FORMAL conjecture1 (the G7 completion plan)

1. Complete the **35 remaining R47 merge cells** (mechanical, generated pipeline).
2. Formalize the **per-step monotonicity seam** (`D≥0 ⟹ Aobj Step-monotone` via the env factorization) —
   *the highest-leverage single gap*; everything downstream needs it.
3. Formalize the **R7' stage assembly I–IV** composing per-step monotonicity + de-loading (G5/G6) + R5/R6.
4. **Lean-ize the rungs** currently Python-only: R1/R2/R4/R6 + the amortized hub bound.
5. **Compose** the bridge (`pi_utree`) + `phi_le_one` + the assembled R7 into a **top-level theorem**.
6. **Discharge** conditional hypotheses (`Case2Property` on achievable messages, etc.).
7. Integrate **LPRSC** as the tie-arithmetic primitive; **independent review**.

## The honest ultimate conclusion

- **There is no hidden mathematical gap in the reduction.** Every reduction piece is assembled at the
  exact-cert level; the accumulation boundary is handled by amortization; the isolated marginal tie by
  LPRSC. The mathematics is, to the best current knowledge, complete-modulo-review.
- **The remaining distance is formalization (G7), and it is large but SCHEDULABLE** — not one theorem,
  but a mountain of mechanical Lean-ization: 35 merge cells + the per-step seam + the stage assembly +
  Lean-izing 4 rungs + the capstone composition + discharging conditionals. Each piece has a known
  shape; none is a research unknown.
- **The single highest-leverage next Lean brick is the per-step monotonicity seam** (`D≥0 ⟹ Step
  monotone`): it is the one identified-but-unstarted link, and the whole R47 cell layer only pays off
  once it exists.
- **Caveat (the one place to stay honest):** the tight/strict R3 (needed for the *unique* maximizer, not
  just `≤`) is where LPRSC lives; its Lean integration + the `Case2Property`-style relocated integrality
  content are the pieces most likely to hide subtlety when formalized. "Mechanical" should be trusted
  cell-by-cell, verified by CI, not assumed wholesale.

**Verdict: BG Conjecture 1 is "one theorem away" mathematically and a substantial-but-mapped
formalization project away formally. The frontier is G7, it is climbable, and this doc is its map.**
`conjecture1_proved = False`.
