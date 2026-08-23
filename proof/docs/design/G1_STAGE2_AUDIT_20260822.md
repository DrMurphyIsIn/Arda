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
| **1** | **ledger monotone in `pL`** (chain depth) | **NOT** a corollary of `slack≥0`, and — CORRECTED 2026-08-22 (below) — **harder than first stated**: the general "adding bundles increases the ledger" is **false at the knee**, so lemma 1 is a **family-specific** statement about `chain3p`, not a clean cavity-contraction | 0 violations to `pL=8000`; but the *local/general* version has real counterexamples near `cav≈T0` (see correction) |
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

## Most tractable next attack (as first assessed)

**Lemma 1 (ledger cavity-contraction).** The converging positive increments (`d_ledger → 0⁺`) suggested a
clean contraction. **This assessment was wrong — see the correction below.**

## CORRECTION 2026-08-22 — lemma 1's clean route fails; it is family-specific and knee-critical

An attack on lemma 1 established, then refuted, the "clean contraction":

1. **Exact local decomposition (real).** Adding a child subtree `c` at a node changes *only that node's
   slack* (siblings'/descendants' cavities are unchanged): `d_ledger = d_slack(v) + ledger(c)`, with
   `ledger(c) ≥ 0`. Verified exactly.
2. **But the resulting general monotonicity is FALSE.** "Adding a bundle child increases the ledger" has
   **real counterexamples on achievable trees** — 1431/50000, worst `d_ledger = −0.006`, concentrated at
   `cav ≈ 0.2277 ≈ T0` (the knee). And burying the violating node under ancestors does **not** rescue it:
   `d_ledger` stays negative (`−0.00073`, converging). So the ledger is **not** monotone under
   bundle-addition, and lemma 1 does **not** reduce to a local or general per-node inequality.
3. **Lemma 1 is therefore family-specific.** `chain3p`'s `pL`-monotonicity (0/8000) holds because child_B
   accumulates *equal-cavity* `3/23` bundles, sweeping its cavity `0.47 → 0.13` **through the knee at
   `pL≈3`** — precisely where the general case breaks. The proof must exploit that equal-bundle structure;
   the naive cavity-contraction is refuted.

**Consequence for the risk assessment.** The knee **is** load-bearing for lemma 1 (as it was for the
g-step), contrary to the "risk downgrade" above — that downgrade is correct **only for lemma 2** (the
Jensen floor lemma on the globally-convex hinge, which genuinely is clean through the knee, 0/20000).
Lemma 1 is subtler than "routine cavity-contraction." `conjecture1_proved = False`; lemmas 1–3 remain
unwritten, with lemma 1 now the *hardest* rather than the most tractable of the three.

## FURTHER SHARPENING 2026-08-22 — lemma 1 is a 3-node NET monotonicity, not per-node

Exact per-node decomposition of `ledger(chain3(pT,pM,pL))` at `(pT,pM)=(1,1)` (float, but the sign
structure is robust): the bundles contribute **zero** ledger (`slack(BUNDLE)=0`, the tie), so the whole
ledger is carried by the **three spine nodes** `Z` (root) → `Y` (middle) → `X` (deep tip, `= (BUNDLE)^pL`):
`ledger = slack(Z) + slack(Y) + slack(X)` **exactly** (confirmed 0.278078 = 0.278078 at pL=5).

Tracking each spine slack as `pL: 1→11`:

| node | behaviour in `pL` | cavity |
|---|---|---|
| `slack(Z)` root | slowly **DECREASING** (0.07557 → 0.07375) | `cav_Z` ≈ flat (0.2934 → 0.2905) |
| `slack(X)` tip | **NON-MONOTONE** — rises to a peak at `pL=3` (0.09063 → 0.11325) then **falls** (→ 0.09365) | `cav_X` sweeps `0.469 → 0.074`, crossing `T0` at `pL≈3` |
| `slack(Y)` middle | **INCREASING** and dominant (0.06647 → 0.12237) | `cav_Y` **rises** (0.2778 → 0.3120) |

So lemma 1's monotonicity is a **net effect**: adding a tie-bundle to the tip `X` lowers `cav_X`, which
*raises* `cav_Y` (the middle node is drained less by its spine child), and `slack(Y)`'s rise **dominates**
the tip's post-knee fall plus the root's slow drift. The tip slack peaks **exactly at the knee** (`cav_X=T0`,
`pL≈3`), the same resonance point that breaks the general case.

**Why this matters for the attack.** Lemma 1 is *not* a per-node cavity-contraction (the tip slack is
non-monotone and the root slack moves the wrong way); it is a **coupled monotonicity through the knee** in
which the middle node's gain must be shown to dominate. That is a collective-cancellation-flavoured
statement — the same character as the g-step crux, not the clean-Jensen character of lemma 2. Any proof
must track the `cav_X → cav_Y` coupling explicitly (adding a below-knee child to a node *raises* its
parent's cavity), not bound the tip in isolation. This confirms and pins the CORRECTION above:
lemma 1 is the hardest of the three. `conjecture1_proved = False`.
