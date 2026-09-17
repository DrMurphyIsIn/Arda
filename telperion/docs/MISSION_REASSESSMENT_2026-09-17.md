# Mission reassessment — 2026-09-17 (end of the consolidation day)

*`conjecture1_proved = False`. This document assesses the RH program and the Telperion
platform after every open thread was consolidated under one owner and the day's
merges landed. It says what is proved, what the machine can and cannot do, and what
is next in what order.*

## 1. What the program is, in one paragraph

Telperion is a certificate-first Lean pipeline: emitters turn finite, algebraic,
positivity- or enclosure-shaped objects into kernel-checked theorems, with axiom guards,
negative controls, a second-kernel comparator, and a missions registry whose only path to
`proved` is a mechanical gate. Applied to RH it has produced a large, honest body of
finite and classical results — a kernel-verified zero-localization ladder to
T = 640000 (1,072,715 zeros, on the climb branch), effective de la Vallée-Poussin,
Backlund S(T) = O(log T), effective Riemann–von Mangoldt counting, the finite
Bombieri–Lagarias positivity core, the Bragg/diffraction bridges, and today the first
MIRRORMERE node discharged through an external formalization. The roadmap merged today
(Routes A–D) concludes, after adversarial review, that every route to RH relocates the
conjecture into one named wall clause. None of the above moves that clause.

## 2. State of the registry (main, evening)

| campaign | proved | open | draft | note |
|---|---|---|---|---|
| rh | 14 | 1 | 3 (+3 DBN drafts when #550 lands) | goal `RH_conjecture` draft by design |
| anduril | 0 | 9 | 1 | six nodes carry proof links; artifacts reach main with #506 |
| mirrormere | 1 (`MM_rvm_unbounded_mean_density`, #553 pending) | 15 | 2 | nine more carry proof links |
| bg | 9 | 3 | 1 | one refuted, one deprecated; not RH |

Sixteen nodes carry a `[proof]` link but are not yet granted. One (the E6 node) has its
artifact on main and is granted in #553. The other fifteen are gated on the climb-branch
reconcile (#506): their artifacts live in `zeta_reflection`, `zeta_zero_localization`,
`quasicrystal` and the Bragg/trace modules of `li_positivity`.

## 3. Is Telperion's full capability applied to RH? Honest answer

Yes for everything certificate-shaped, and the day's work shows the shape of that ceiling:

- **Where it bites.** Finite verification (the ladder), classical analytic bricks
  (dVP, Backlund, effective RvM, corridor-adjacent lemmas), finite positivity cores (BL),
  finite diffraction identities (Bragg bridge, trace reading), and external-formalization
  ports (E6: Zeta23 Theorem A). All kernel-clean, all axiom-guarded.
- **Where it cannot bite.** The wall clause is uniform-in-N / all-support / all-height:
  Weil positivity over every test function, the Vinogradov–Korobov rate, an operator with
  completion. These are not certificate-shaped and no emitter, sweep, or ladder height
  changes that. The wall campaign (#536) proved the sharper form: reflection-invariant
  per-zero functionals cannot even orient a zero within its pair.
- **Under-applied until today.** The roadmap's own critical path — cumulative RvM with an
  O(log T) remainder (`RH_rvm_unconditional`), then the corridor bound
  `‖ζ′/ζ‖ ≤ C log² T` on a good ordinate in every unit window (`RH_corridor_bound`), then
  the limit explicit formula — is classical, brick-shaped, and was unstaffed. It is now
  registered (#545) and the first brick is being attempted from Zeta23's general-window
  lemmas (see §5).

## 4. Platform state after today

- **CI**: the E2BIG monolith is out of the per-PR path. The climb branch builds as sharded
  25k-height block packages with a generated per-block `Guard_h<top>` module (`#guard_msgs`
  on `#print axioms`), so a bare `lake build` is the axiom battery; legacy box certificates
  build weekly. First runner timings: h25000 = 30 min, h50000 = 62 min; `H_CI = 50000`
  until the prior-block-cache shape lands (#554).
- **Islands**: v4.32 (localization ladder, ZFB), v4.34 (li_positivity, dbn, rh statements),
  v4.33.0-rc2 (rvm_bridge ← zeta-23-lean). Cross-island grants have precedent and a
  documented trust boundary.
- **Hygiene fixed today**: Linux Platt detection, order-independent emitter discovery,
  generator manifest completeness, definitions generator now carries every registry block.
- **Debt**: `lake env` unreliability at depth on runners (worked around, not explained);
  the monolith lakefile still exists for the local climb until the between-legs cutover;
  leg 27 (T = 680000) is emitted but unbuilt; #481 (prove2me bridge, 5.3k lines, cli.py
  conflict) needs a rebase and a real review before it is considered.

## 5. Remaining open items, in execution order

1. **#550** (DBN foundations) — CI on the pushed resolution; merge.
2. **Reconcile-2** — merge main into the climb branch (two additive conflicts: workflow
   jobs, `telperion.toml` entries); merge; then **#506** (climb → main).
3. **Grant pass** — `mission grant` for the fifteen linked nodes once their artifacts are
   on main; ledger each; the six anduril nodes plus nine mirrormere nodes.
4. **#553** (E6 grant), **#554** (guard modules), **#470/#525** (docs) — merge as CI reports.
5. **Blind read-back** of `RH_corridor_bound` and `RH_rvm_unconditional` (in progress by
   an independent auditor); promote draft → open with testimony; same for the three DBN
   drafts after #550.
6. **`RH_rvm_unconditional` proof** (in progress): cumulative O(log T) RvM from Zeta23's
   general-window lemmas with the divisor/analyticOrderAt multiplicity seam; deliver
   sorry-free or as crisp stated obligations. On success: proof-link + cross-island grant.
7. **`RH_corridor_bound`** next — it consumes item 6.
8. **Ladder CI to 200000** via the prior-block-cache/matrix shape; retire the monolith.
9. **Paper**: #525 lands the RH-primary structure; numbers must then move from 160000 to
   the CI-verified `H_CI` (cite what CI builds) with the climb height stated separately.

## 6. Tripwires (unchanged, armed)
A certified λₙ < 0 (`li_neg_refutes_rh`); a persistent band count deficit confirmed by an
off-line winding-1 box; a genuine-data negative defect window; a certified Bagchi
lower bound; Lehmer-pair quality trending to 0. Any of these is the program's only
decade-scale positive-payoff event: a certified refutation.
