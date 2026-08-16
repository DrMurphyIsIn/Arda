# Review: review/amortized-hub-fix (d9030a3d..d223a2fa) — the G1 rational-certification arc

Integrating-session review, 2026-08-14. Scope: 3 commits, 5 files (amortized_hub_bound
repair, g1_floor_certificates, g1_endpoint_certificates, slack_ledger label sync,
G1_KERNEL_LEAN_DESIGN.md). Responds to REVIEW_20260814_MR69 Concern 2 (PRIORITY G1) and
the G1 float-hardening program.

**Verdict: PASS — merged with three minor amendments (applied in the integration commit).**

## Verified (ran, not just read)

* All four self-verifying modules ran GREEN end-to-end in the review worktree
  (`g1_floor_certificates`, `g1_endpoint_certificates`, `amortized_hub_bound`,
  `slack_ledger_dichotomy`), and again post-amendment on the integrated branch.
* **Concern 2 repair is sound and honest.** The false intermediate `DELTA_CHARGE = 0.0240`
  is gone; the below-window critical family is now genuinely symbolic
  (slack >= log((1+T0)/(1+T0-EPS)), T0 bracketed rationally via (1+T0)^11 = 621/64;
  L = log(1+T0) makes the mechanism a two-line monotonicity argument — checked by hand).
  The review's "analytic limit 0.023587" was indeed the first-order approximation; the
  true family infimum 0.0238699 gives DELTA_AMORT = 0.0235 a real 3.7e-4 margin.
* **The convex-minorant/Jensen mixed layer (g1_endpoint) is correct.** Hand-checked:
  minorant validity piece analysis (window case vs TAU, above case vs (11/50)EPS,
  continuity at both breakpoints — the in-code rational asserts match); Jensen direction
  (chat convex, slopes 0 <= 11/100 <= 11/50); `H_lower` interval directions all
  conservative (log at right endpoint, chat at left, cav vs T_LO); the m >= 8 uniform
  lemma (1/9 < T_LO kills the penalty; 22/25 > 1/(1+B) makes the upper branch increasing).
  The self-caught traps (T_LO-EPS breakpoint sliver; product-of-sups failure at cT=5)
  are the right kind of honesty signals.
* Heavy-top endpoint: per-dt exact + monotone tail, worst sup/target 0.9044 as claimed.
* Ledger honest throughout: `conjecture1_proved=False` everywhere; no Stage-II or
  depth>=3 claims smuggled in ("G1 COMPLETE **for the arc**" is correctly scoped — the
  depth>=3 genericity sliver from MR69 Concern 1 is a separate named gap, untouched).

## Findings → amendments applied

1. **Bisection sliver (completeness nit):** `certify_mixed_layer_all_m` bisected
   S in [1e-6, m/2], leaving S in (0, 1e-6) formally uncovered for m in {2..7} while
   claiming "ALL profiles". The bound is very slack there (H_lower(m, 0, 1e-6) >= 0.18,
   verified), so no mathematical issue — but the claim should be literal. Amended:
   S0 = 0 (bisection re-run green).
2. **Verifier wiring:** the two new g1 modules were not in `verify_20260814.py`'s module
   list, so the one-command verifier would not exercise them. Amended: added both.
3. **Supersession label staleness:** `amortized_hub_bound` and `slack_ledger_dichotomy`
   still described the mixed layer as "grid rigor (G1)" after commit d223a2fa superseded
   it at rational rigor (an UNDER-claim — safe direction, but the MR69 review flagged
   exactly this kind of cross-module status drift). Amended: both now cite
   `g1_endpoint_certificates.certify_mixed_layer_all_m` as the rational-rigor
   supersession, keeping the modules' own internal rigor labels accurate.

## Notes for the Lean port (G1_KERNEL_LEAN_DESIGN.md)

The port map is credible: the kernel collapses to `Real.log_le_sub_one_of_pos` +
exp-Taylor for three one-time constants + `norm_num`; bisection trees replaced by the
algebraic two-point estimate. The honest note on decide-shaped sweeps (native_decide
stays banned) matches the campaign method. Natural sequencing: after the P4/P5
certificate ports, since the same nlinarith/positivity toolchain serves both.

conjecture1_proved = False, unchanged.
