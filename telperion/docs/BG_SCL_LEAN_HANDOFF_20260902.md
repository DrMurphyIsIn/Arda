# BG asymptotic upper bound — SCL Lean formalization: HANDOFF (2026-09-02)

**Repo:** `github.com/DrMurphyIsIn/Arda` · **on `main`** at merge `c2f19b0` (PR #192).
**Branches:** `bg/unified-program` == `bg/scl-lean` == `9b04455` (the reconciliation merge; == main content).
`conjecture1_proved = False` everywhere — this closes the analytic side's SCL *infrastructure*, not the conjecture.

---

## TL;DR

The concrete single-child lemma (SCL) `V_μ(b) ≤ V_μ(cherry)` for every rooted branch is now **fully assembled in
Lean 4 (Mathlib v4.32.0), kernel-verified, no `sorry`, down to ONE precise inequality `SCLStep μ`.** The recursion,
the concrete cavity matching recursion, positivity, the `ell` recursion, the concave-log tangent, and the hub
`y`-formula are all proven. The remaining Lean work is discharging `SCLStep μ` itself (the per-hub decouple) — the
plan is written and de-risked; the leaf-exclusion crux and the log-enclosure technique are already RESOLVED.

## What is PROVEN in Lean (no `sorry`, full `lake build` green — 8850 jobs)

`proof/formalization/R3Cert/BGSCLInduction.lean` (404 lines) — the SCL infrastructure:
- `Branch` rose-tree; `bsize`/`bchildren`/`bchildren_bsize_lt`; `scl_of_child_step` (well-founded strong induction).
- `cav : Branch → ℝ×ℝ` — the concrete cavity `(U, total)` matching-sum recursion; `cav_pos`/`btotal_pos`/`bU_pos`.
- `FSTAR = log(621/64)/11`, `btotal`, `bell = log(total) − |b|·F*`, `bh`, `bY`, `bV μ b = bell b + μ·bY b`.
- `bell_node` — the ell recursion `ell(node cs) = Σ ell(c) + (log(1+S/d) − F*)`.
- `log_tangent` + `bell_node_tangent` — the concave-log tangent linearization (via `Real.log_le_sub_one_of_pos`).
- `bY_node` — the hub y-formula `y(node cs) = 1/(d + S)`, `S = Σ bY c`, `d = |cs|+1`.
- `cherry := node [node []]`; **`SCLStep μ := ∀ cs, (∀c∈cs, bV μ c ≤ bV μ cherry) → bV μ (node cs) ≤ bV μ cherry`**;
  **`scl_of_step μ (hstep : SCLStep μ) : ∀ b, bV μ b ≤ bV μ cherry`** — THE REDUCTION (recursion done).

`proof/formalization/R3Cert/BGSCLStep.lean` (127 lines) — the price-flow layer + the two resolved cruxes:
- `inI μ := 456/3703 ≤ μ ≤ 3/7`; `muPP d μ := 3(4d−1−3μ)/(4d−1)²` (the concavity-tangent price map).
- **`muPP_mem_I` (leg #1)** — the price map keeps `I` invariant for hub-degrees `2 ≤ d ≤ 6` (pure rational box).
- `PSCL b := ∀ μ ∈ I, bV μ b ≤ bV μ cherry`; `scl_of_step'` — the price-carrying recursion (child IH available at
  the flowed price `μ'' ∈ I`).
- **Leaf-exclusion crux, RESOLVED:** `leaf_le_cherry` (a leaf child satisfies the SCL for `μ ≤ 3/11`) +
  `muPP_le_three_eleven` (child price `μ'' ≤ 3/11` at `d ≥ 3`). So the naive-FALSE `∀b` SCL (leaves violate it for
  `μ > 0.297`) is repaired: leaves occur in the step only at `d ≥ 3` where `μ'' ≤ 3/11 < 0.297`; the sole `d=2`
  leaf-hub IS the cherry (base case).
- **Log-enclosure technique, RESOLVED:** `two_le_log_gap` (`2 ≤ 11·log(3/2) − log(621/64)`) via `Real.exp_one_lt_d9`
  (LOOSER rational bounds, NOT the tight frozen 10³⁰ enclosures) — the reusable method for the `hbroom` leg.

## Telperion ledger (Python, all `.check()`s green; 28 BG tests pass)

`telperion/src/telperion/bg_upper_bound.py` — the 10-GATED honest reduction; the SINGLE open input is
`2b-lo-scl-induction` (HYPOTHESIS): the well-founded SCL recursion / leaf-free near-broom argmax extremality.
Certs in `tie_regime.py`: `ExtremalityPriceMapCertificate` (#1), `BroomVsCherryOnICertificate` (#4, hardened,
margin +0.012), `LeafExchangeCertificate` (#5, d=3..6), `SCLInductionCertificate` (assembly consistency).

## What REMAINS — discharge `SCLStep μ` in Lean

The one open Lean obligation. Plan: `~/.claude/plans/sorted-conjuring-clock.md` (approved, de-risked). Shape:
1. **`hbroom` (leg #4 in Lean)** — `bV μ (broom j) ≤ bV μ cherry` for all `j ≥ 1`, `μ ∈ I`, via the
   `two_le_log_gap` `exp`-bound method (+0.012 margin, monotone tail in `j`). Concrete broom values:
   `total(B(j)) = (2j+1)/(j+1)`, `bY = 1/(2j+1)`, `bell = log((2j+1)/(j+1)) − (j+1)·FSTAR` (via `List.map_replicate`).
2. **The per-hub decouple** — assemble `bell_node_tangent` (tangent at the all-cherry reference `S* = (d−1)/3`) +
   `bY_node` + child IH at `μ'' = muPP d μ ∈ I` (`muPP_mem_I`) → reduces to the scalar residual
   `μ(S−S*)²/((d+S*)²(d+S)) ≤ margin(d,μ)`, TRUE for `d ≥ 2`, `μ ∈ I` over the non-leaf `S`-range with **5× safety**
   (worst at `d=2`, ratio 0.19). Close by `nlinarith [sq_nonneg (S−S*), …]` after clearing positive denominators —
   THIS `nlinarith` is the single highest-risk step; pre-split child cases (leaf #5 / broom #4 / deg≥7 / IH).

After `SCLStep`: flip `2b-lo-scl-induction` GATED→LEMMA. Then the SEPARATE fronts (not this file): finite-`n`
structural side (tree→hub / Hnorm–Hdom) + the matching lower bound `S(k,5)` achieves `F*`.

## Honest scope / risk

Two genuine residuals (per the plan): (1) the leaf/extremality reformulation is RESOLVED for the strong-induction
form here, but (2) telperion's *extremality argmax* (near-broom = max over ALL non-broom degree-`d` branches) was
only adversarially/numerically checked; if Agent-2's clean residual-vs-margin doesn't extend uniformly to all
non-leaf children, the argmax inherits numerical-only status and we land an honest "modulo the argmax" reduction.
`conjecture1_proved = False`.

## Environment / footguns (READ BEFORE CONTINUING)

- **Local Lean now works** (broke the old CI-only bottleneck): `PATH=$HOME/.elan/bin; cd proof/formalization;
  lake exe cache get; lake build R3Cert.BGSCLStep`. Toolchain `leanprover/lean4:v4.32.0`. The R3Cert lakefile globs
  `R3Cert.+`, so new modules are auto-built + sorry-scanned by `proof-lean.yml` CI.
- **This is a linked git worktree** (`/Users/peterwmurphy/telperion-work/.git/worktrees/bg-research`) — `.git/` is a
  file, not a dir; `test -f .git/MERGE_HEAD` LIES. Use `git rev-parse -q --verify MERGE_HEAD` / `--git-path` instead.
- **CI sorry-scan footgun:** `grep -rnwE sorry|admit` trips on bare `sorry-free` in docstrings — write **"no `sorry`"**
  (backticked), never bare "sorry-free".
- **Mathlib v4.32.0 API quirks:** `LinearOrderedField`/`OrderedAddCommMonoid` are NOT classes (use `ℝ` directly);
  `le_div_iff`→`le_div_iff₀`, `div_le_iff`→`div_le_iff₀`; `List.mem_cons_self` takes no args (use
  `List.mem_cons.mpr (Or.inl rfl)`); `Real.log_lt_iff` unknown (use `Real.le_log_iff_exp_le` /
  `Real.log_le_iff_le_exp`); `Real.exp_one_lt_d9`, `Real.log_pow`, `Real.log_div`, `Real.log_mul`, `Real.exp_bound`
  exist. `rw [FSTAR]` fails ("equation theorems") → `have hF : FSTAR = … := rfl; rw [hF]`.
- **Cross-session collision:** launch background agents that do git ops with `isolation: worktree` (a bare agent's
  checkout switched the working tree mid-commit once). Parallel Claude sessions build divergent certs — reconcile,
  don't clobber (this handoff's merge reconciled two independent extremality-cert forks).

## Verify current state

```
cd ~/bg-research && git log --oneline origin/main -3          # c2f19b0 has BGSCL*.lean
grep -nE '\bsorry\b|\badmit\b' proof/formalization/R3Cert/BGSCL*.lean | grep -v '`'   # NONE
cd telperion && python3 -m pytest tests/test_bg_upper_bound.py tests/test_tie_regime.py -q  # 28 passed
PATH=$HOME/.elan/bin; cd proof/formalization && lake build R3Cert.BGSCLStep   # green
```
