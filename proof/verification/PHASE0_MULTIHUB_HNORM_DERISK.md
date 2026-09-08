# Phase 0 de-risk — m≥3 multi-hub + Hnorm (both GREEN)

Branch `bg/multihub-hnorm`. Decisive gates for the plan `~/.claude/plans/quiet-singing-kahn.md`.
Both targets confirmed TRUE (not refuted); exact `fractions.Fraction` throughout. conjecture1_proved = False.

## A0 — stuck multi-hub ≤ tie  (`verification/kelmans_vertex_budget.py`, PASSES)
Run: `cd proof && PYTHONPATH=. python3 verification/kelmans_vertex_budget.py`
- two_hub_grid_dominated: True (3746 cases); small_corner: True (4); two_hub_theorem: 6 cells
  (symbolic all-nonneg certificate, ALL sizes).
- assisted_merge_grid: True (1950); assisted_merge_theorem: 6 cells.
- multi_hub_probe: 3-hub 162 cases (worst margin 1.091 = single hub wins 9.1%), 4-hub 42 cases
  (worst 1.176 = 17.6%). Margins GROW in m (~9%/extra de-loaded hub).

STRATEGIC REFINEMENT (from `vertex_budget_status`): the assisted merge REFRAMES the m-hub extension.
Complete local merge table — hubward loaded donor -> direct merge; hubward de-loaded donor -> assisted
merge; anti-hubward -> reverse roles. => STUCK configurations cease to exist on the two-hub family. So the
length>=3 Hdom residual is the ENVIRONMENT version of the two merge rules (same bilinear-identity + box
machinery as `vee_merge_le`, already done for direct merges) — NOT a research-hard global value bound.
Route A therefore prioritizes: add assisted merge to OrderedStep + prove its environment dispatch cert;
then stuck length>=3 states are vacuous and Hdom length>=3 follows. Direct value-bound (multi_hub_probe)
stands as an independent numeric cross-check / fallback.

## B0 — StraightProgress_sized (FLP)  (`verification/phase0_straightprogress_sized.py`, PASSES)
Run: `cd proof && PYTHONPATH=. python3 verification/phase0_straightprogress_sized.py`
- VERDICT: LOCAL-MOVE VIABLE. 2438 non-backbone rooted trees tested (n<=12), FAILURES = 0.
- Move family: reroot_only 2138 (88%, Aobj-invariant), spr 30, spr_plus_reroot 270.
- GENUINE (no defect-0 rooting) subset: 30 trees, ALL fixed by an SPR move with STRICT Aobj increase
  (30 strict, 0 ties, 0 failures).
=> StraightProgress_sized is true for every tested tree; the Lean gap is the move-existence FINDER (the
selection is adaptive: reroot vs FLP-SPR) + the local Aobj-gain cert. The crest-retaining FLP local gain
is already kernel-proved (aobj_flp_context_lift_crest, BGSCLRealOblACaseALift.lean:207); the naive
wholesale pushInto form is kernel-refuted (flp_context_lift_book_false).

## Verdict
Neither problem is refuted; both reduce to a crisp residual with the load-bearing local cert already
proven. Proceed to the Lean assembly (Problem A: OrderedStep assisted-merge + environment dispatch ->
stuck length>=3 vacuous; Problem B: FLP local step + finder + Type-L closure + honest Type-W conditional).
No closure claimed; conjecture1_proved = False.
