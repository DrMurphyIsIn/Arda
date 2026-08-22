# G1 Stage-II audit: the "unproven monotonicity" is three routine single-variable lemmas

2026-08-22. `conjecture1_proved = False`. A source-level audit of the R7' Stage-II residual
(`R7_ARCHITECTURE.md` amendments 1–2: "depth ≥ 3 genericity rests on sampling + an unproven
monotonicity"; the PROVEN-vs-CONJECTURAL status contradiction between `amortized_hub_bound.py` and
`slack_ledger_dichotomy.py`). Read `g34_deep`, `slack_ledger_dichotomy`, `amortized_hub_bound`,
`proof_via_explicit_potential`; verified numerically (exact where noted). Audit, not a closure.

## The ledger and its potential

R7' domination uses the **ledger** `ledger(T) = Σ_v slack(v)`, a telescoping sum of per-node slacks
with the **hinge potential** `phi(y) = C_HINGE·(y − T0)₊` (`T0 = rhoB − 1 ≈ 0.2295`, the *same* folded
hinge as the R3 `phi_le_one` proof), `slack(v) = Σ_children phi(cav_c) − phi(cav_v) − chi_v`. The
rate identity turns `ledger > THETA (≈ 0.2813)` into "dominated"; the sub-THETA region is handled by
finite exact checks, made finite by ledger growth in depth.

## What is proven (not the gap)

**Per-node `slack(v) ≥ 0`** — the super-solution `chi_v + phi(cav_v) ≤ Σ_children phi(cav_c)`,
Lean-checked chain (`proof_via_explicit_potential` / `PotentialAssembly.superSol`, margins > 0.13).
Verified here **0/33735** on deep chains. This is what `amortized_hub_bound.py` calls
PROVEN/UNCONDITIONAL — and it is right about `slack ≥ 0`.

## The three genuinely-open pieces (what `slack_ledger_dichotomy.py` calls conjectural)

| # | lemma | character | evidence |
|---|---|---|---|
| **1** | **ledger monotone in `pL`** (chain depth) | **NOT** a corollary of `slack≥0`: adding depth shifts *ancestors'* cavities (`root_cav 0.2221→0.2189` over `pL=0..7`), so it needs a **cavity-contraction** (net telescoping change ≥ 0) | 0 violations to `pL=8000`; increments positive, shrinking to a positive limit — the ledger *converges* |
| **2** | **context-free floor** (`slack` infimum at equal children → per-class ledger floors) | core is **Jensen on the convex hinge** — and it holds **cleanly through the knee** (unlike the g-step's non-convex `min`); residual is the cavity-recursion coupling `cav_v(children)` | Jensen part **0/20000** incl. 16054 knee-straddling; per-class floors are interval-numeric (the G1 hardening target) |
| **3** | **domination-ratio unimodality** `r(q_i)` | single-crossing of a rational function (one interior minimum) | exact successive-difference checks (`depth3_rigorous.py`) |

## Key finding — a risk downgrade

The ledger's `phi` is a **globally convex hinge**. The R3 g-step's per-child cap `Bcap = min(glemma,1)`
is **non-convex at its knee**, which is exactly what forced the whole push-to-knee majorization
(`gCoreOff_le_replicate`) + rational-enclosure machinery to close it. Here there is **no such
non-convexity**: "infimum at equal children" is clean Jensen straight through the knee. So the
hardest-looking Stage-II piece (the floor) sits in a **structurally easier** setting than an inequality
that is *already closed*. All three lemmas are bounded single-variable/convexity monotonicities with
**wide, widening margins and no tie/μ\* resonance** — none is a collective-cancellation crux.

## Status-contradiction, resolved

Both files are right about different things. `slack ≥ 0` is proven (Lean); the **floors built on it**
(lemmas 1–3, the context-free per-class bounds) are **not yet written**. So the reviewer amendment
("the CONJECTURAL language is correct until G1") holds, and G1 Stage-II is **"routine-but-unwritten,
low-risk, no known obstruction"** — not an open-ended idea. `conjecture1_proved = False` stands until
lemmas 1–3 are theorems (G1 symbolic hardening) and G7 Lean-izes the assembly.

## Most tractable next attack

**Lemma 1 (ledger cavity-contraction).** The converging positive increments (`d_ledger → 0⁺`) suggest a
clean contraction: each added level's realized slack dominates the (shrinking) decrease in ancestor
slacks. This is a single-variable transfer-operator monotonicity — see the companion attack.
