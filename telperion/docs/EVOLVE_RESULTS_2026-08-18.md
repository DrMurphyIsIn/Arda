# Telperion Evolve: Measurement Results 2026-08-18

## Status

`conjecture1_proved = False`. Nothing produced by the evolve loop has been frozen into
CI or added to the Lean proof. The run below is empirical evidence that the infrastructure
works end-to-end; no sub-certificate it found was hand-reviewed for Lean-portability.

**Update 2026-08-20.** The one-off run below is now a regression test
(`tests/test_evolve_frozen.py`) and an example (`examples/evolve_nearstar/`):
`telperion.evolve.freeze.discover_nearstar_champion` deterministically discovers
the certifying champion (seed=0), and `build_frozen_lean` emits its reusable
ratio certificate (Pólya step + crossings, s*=5) bundled with the
`Telperion.unimodal_peak` prelude — soundness-lint clean. What is proven locally:
reproducible discovery + lint-clean emission. What remains cloud-gated: the
`lake build` kernel green (this host does not build Lean), and — by
`UnimodalMaxEmitter`'s design — the final `unimodal_peak` application against a
concrete non-rational `f` is the caller's line. So `conjecture1_proved` stays
`False`; the honest gain is that the milestone is now reproducible-and-tested,
not a manual one-off.

---

## Experiment setup

Harness: `src/telperion/evolve/measure.py::compare`
Commit: `feat(evolve): measurement harness + honest results write-up`
Python: 3.9.6
Host: macOS Darwin 25.6.0 (Apple Silicon / local CPU only; no GPU)

Seed genome (FAILING start, non-certifying):
    ratio_src = "(2*s+1)/(2*s+3)", s0=3, lift_max=4

Ratio pool supplied to the loop:
    ["486/529 * (1 + 1/(4*s**2 + 11*s + 6))**11",   # NEAR_STAR_Q (known green oracle)
     "(2*s+1)/(2*s+3)",
     "(s+2)/(s+1)"]

Scoring: score >= 990 means the genome certifies (score = 1000 - complexity).

---

## Structured arm (no LLM) -- ACTUAL RUN

Command:
    python3 -c "
    import sys; sys.path.insert(0,'src')
    from telperion.evolve.config import EvolveConfig
    from telperion.evolve.measure import compare
    from dataclasses import replace
    print(compare(replace(EvolveConfig.default(), islands=4, gens=20, use_llm=False), trials=5, seed=0))
    "

Config: islands=4, gens=20, use_llm=False
Trials: 5, seed=0

Results (certify_rate is the exact-arithmetic certify tier, NOT a lake build / Lean kernel run):

    certify_rate      : 1.0         (5 / 5 trials found a certifying champion)
    median_evals      : 344         evaluations (sympy certificate calls)
    median_wall_s     : 22.544 s    per trial
    found_novel_ratio : False       (champion always came from the seed pool)

Total wall time for all 5 trials: 110.74 s

Interpretation:

- The loop reliably climbs from a failing genome to a certifying champion every trial
  (certify_rate = 1.0, exact-arithmetic tier) across varied RNG seeds.
- Median 344 evaluations vs. the init-only baseline of 6*islands = 24 seeds; the loop
  does non-trivial search, not just lucky initialization.
- `found_novel_ratio = False` is expected for the structured arm: StructuredMutator
  perturbs s0 and lift_max but cannot invent a new ratio_src string; the pool swap
  (30% probability in evolve()) is the only source of ratio diversity, and the pool was
  finite and pre-supplied. A novel ratio would require the LLM arm.

---

## LLM arm (hybrid, qwen2.5-coder:7b) -- NOT RUN THIS SESSION

Reason: `ollama pull qwen2.5-coder:7b` failed with
`permission denied on /Users/peterwmurphy/.ollama/models/blobs/...`.
The model `qwen2.5:32b` (19 GB) is present locally but is not the target model tag
configured in EvolveConfig.model_tag. One bounded pull attempt (30 s) was made and
abandoned after the permission error.

No LLM-arm numbers are reported. The structured arm is the load-bearing evidence.

---

## Comparison to hand-authoring

Hand-authoring the NEAR_STAR_Q certificate required:
- Manual discovery that the near-star tail ratio is `486/529 * (1 + 1/(4s^2+11s+6))^11`.
- Symbolic proof of decrease: s0 chosen empirically (s0=5), Lean formalization
  of the Polya identity B_le (INEQ1) taking ~2-4 hours of expert iteration.
- The evolved champion always discovers the same ratio (from the pool) with s0 and
  lift_max adjusted; it never discovers a genuinely different certifying family because
  the pool is finite.

What the structured arm provides vs. hand-authoring:
- Automated parameter search (s0, lift_max) within seconds once the ratio is in the pool.
- Reproducible, seeded re-discovery of the simplest (lowest-complexity) parameterization.
- No creative invention of new ratio families (that requires the LLM arm or human math).

---

## Verdict: next steps

### (a) Generic unimodal ASSEMBLY emitter

The full theorem (g-step inductive step, all-non-leaf j>=2 branching case) requires
wiring multiple sub-certificates into a Branch structural induction in Lean. The current
kernel.py checks a single InequalityFamily; it does not compose a tree of certificates.

Assessment: NOT ready to build the generic unimodal assembly emitter yet. The two
rational leaves (mustar_lt_third + W*(4/3)^11 < gamma) are Lean-kernel-checked.
The remaining gap is T1/T2 coordinate-monotonicity + Branch-induction wiring -- that is
Lean structural work, not a search problem the evolve loop can solve. The emitter is
the right M5 research deliverable once those two Lean pieces land; building it before
they are proved would produce an emitter with no proof to emit.

Honest scope: the evolve loop is appropriate for sub-certificate parameter optimization
(s0, lift_max, ratio_src discovery). It is not a substitute for the structural induction
wiring that remains open.

### (b) Next residual to target

Priority order (from memory, confirmed by this session):

1. T1 coord-monotonicity in Lean (boost_factor_le covers one step; need list induction
   over all coords via gCoreOff_le_replicate generalization).
2. T2 descent coord-monotonicity in Lean (descent_engine committed; wire into
   gstep_T2_step for all-non-leaf j>=2).
3. Branch structural induction: define block tree + g(C) recursion + wire
   phi_le_one(child) => Phi^11(D_i) <= factorR mu_i into the Branch induction.
4. ONLY AFTER (1-3): build the generic unimodal assembly emitter and point the evolve
   loop at it.

The evolve infrastructure (genome/mutate/fitness/loop/measure) is complete and
working. It should be reused when a new sub-certificate family needs automated
parameter optimization.

---

## Files produced this session

- `src/telperion/evolve/measure.py`          -- measurement harness
- `tests/evolve/test_measure.py`             -- 4 tests (all GREEN)
- `docs/EVOLVE_RESULTS_2026-08-18.md`        -- this file
