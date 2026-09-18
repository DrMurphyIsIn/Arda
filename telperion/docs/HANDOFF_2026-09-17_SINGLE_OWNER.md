# HANDOFF 2026-09-17 — single-owner consolidation of the RH / Telperion threads

*`conjecture1_proved = False`. Nothing in this handoff moves RH; it consolidates
plumbing so the finite, kernel-verified results can land on `main` and the
next session can start at the frontier instead of at the merge queue.*

Context: on 2026-09-17 the operator closed every parallel session and handed all
threads to one session. This file is what that session did, what is in flight,
and where the next session should start. The durable long-form state lives in the
missions registry (`telperion/missions/{rh,anduril,mirrormere}`), the roadmap
(`RH_ROUTES_ROADMAP_2026-09-16.md`) and the B2 docs (`B2_MAIN_CI.md`,
`B2_CUTOVER_PLAN.md`).

## Merged today (main)

| PR | What | Note |
|---|---|---|
| #536 | RH wall campaign: reflection certificates (FORCED / DETECT halves), five audited sweeps, `wall-sweep` skill | maps *why* RH resists; claims no progress toward proving it |
| #532 | Routes A–D adversarially-verified roadmap + 7 audited nodes | thesis: every route **relocates** RH into one named `rh-hard-wall` clause; cross-route critical path = RvM → corridor bound `|ζ′/ζ| = O(log² T)` → limit explicit formula |
| #537 | unit-suite hygiene on the climb branch (into `rh/million-turing`) | Linux auditwheel libflint path (Platt now works on runners), order-independent `_TuringBandEmitter` discovery, dangling-symlink re-link |

Closed: #501 (superseded; masking audit run — the guard is a lake default target, the
only main run in the import-missing window was cancelled, **no masking occurred**).

## Open PRs, in merge order (refreshed 2026-09-17 evening, after the second parallel session closed)

Merged since the morning: #538 (BL proof, main), #539 (manifest, climb), #540 (B2 CI landing,
climb), #542 (artifact-side restatements for the two mirrormere grant pre-flight failures, climb),
#543 (AND_g2_reflected_band re-authored + all three pre-flight fixes ledgered, main). The grant
pre-flight blockers listed further down are therefore DONE; only the reconcile remains.

**Climb branch (`rh/million-turing`), in order:**
1. **#552** `fix/zzl-legacy-boxes`. Corrects a real defect in #540: `zzl_aux` inherited the 671
   pre-band `RHInBox_*` box certificates (~1.9 core-min each); the first hosted-runner ladder run
   spent 3 h 40 min in that step and never reached a block. The 669 boxes nothing imports move to
   `zzl_legacy_boxes`, built by a weekly 4-way-sharded workflow (`telperion-legacy-boxes.yml`,
   per-shard guard cut from `AxiomGuardRHInBox.lean`); `zzl_aux` keeps 17 targets. Split logic is
   reachability through box imports (reviewed: sound). **Its `zeta-ladder-suite` run is the first
   real per-block timing** — read the `built in Ns` lines and set `H_CI` from them.
2. **#544** `reconcile/main-into-million`. Merges main into the climb (one conflict, the
   Li-positivity guard, resolved as union). Required before #506 can merge (#506 is CONFLICTING
   until this lands).
3. **#549** `feat/d1-d4-artifacts`. Route D cheap layers: `rect_trace_reading` (the Bragg bridge
   divided by 2πi) and `spectral_cooked_control` (diagonal matrix Hermitian with prescribed real
   spectrum — the declared negative control). Axiom-clean, pre-flight MATCH. NOTE: touches
   `AxiomGuardLiPositivity.lean`, as does #551 on main → one union-merge at the #506 reconcile.

**Main, in order (all clean against main; two additive pairwise overlaps noted):**
4. **#546** roadmap corrections (docs; cost-curve calibration, Alpöge–Furman gloss, E6 sourcing).
5. **#545** registers the critical path: `RH_rvm_unconditional` (cumulative RvM, divisor count)
   and `RH_corridor_bound` (classical: some T′ ∈ [T, T+1] with a zero-free segment −1 ≤ σ ≤ 2 and
   ‖ζ′/ζ‖ ≤ C log² T). Draft, blind read-back pending. Statements reviewed: classical shape, the
   zero-free conjunct makes the bound non-vacuous under Lean's x/0 = 0.
6. **#547** the E6 bridge: a third toolchain island (v4.33.0-rc2, zeta-23-lean pin) proving
   `RvMUnboundedMeanDensity zetaOrdinates` VERBATIM (both defs checked byte-equal to `MMDefs.lean`
   modulo comments) from `Zeta23.thmA₀` (≥ 2/3 of zeros simple and on the line ⇒ distinct
   ordinates, superlinear in a dyadic window). Axiom guard lists the bridge and every consumed
   Zeta23 theorem at the 3 standard axioms. This REVERSES the 09-15 survey verdict ("no
   unconditional proof in corpus"): the survey missed `Zeta23/RvM/` and Theorem A. Reviewed:
   valid — Theorem A, not the RvM formula, is the load-bearing input, and the PR says so.
   Cross-island grant (precedent: `RH_dlvp_zero_free_region`). Apache-2.0 attribution in NOTICE.md.
7. **#548** proof-links for #547 and #549 in the mirrormere registry (merge after #547; grants
   after `rvm-bridge-compiles` is green and #549 reaches main via #506).
8. **#550** Route C foundations: DBN island (Φ even, super-exponential decay, H_t entire for every
   t, ξ bridge) + DRAFT C2/C3/C4 nodes; the representation theorem H₀ = ξ/8 is REGISTERED, not
   proved. Pairwise overlaps: with #545 on `RHDefs.lean`/`Statements.lean` (both append), with
   #547 on the workflow (both add a job) → rebase #550 after #545 and #547, keep both sides.
9. **#551** Route B/B1: Li-ladder throughput measured to n = 10³ in-kernel (cubic cost fit,
   ~1 bit precision loss per rung), bundle face (one hypothesis instead of N), negative-control
   twin decided in-kernel (fires at n = 6 on the off-line quadruple), and a real bug fix
   (`nsimplify` could silently substitute a nearby rational; now exact). Instrumentation, not
   evidence, and labelled so.
10. **#541** this handoff.

**Then #506**, the reconcile of the climb into main, after #544 and #552 are in and the ladder is
green. Merges are operator-run (`gh pr merge <n> --merge`); the agent is classifier-blocked.

Older open PRs untouched: #525 (paper reconcile), #481 (prove2me bridge), #470 (Route P spec),
#305 (codegen drift — re-check after #506).

## In flight / local state (do not clobber)

- `~/arda-million` (`rh/million-turing`, fast-forwarded to the #537 merge): holds
  **leg 27** (T = 680000) as untracked band files + `campaign_state.json` deltas —
  emitted, **never Lean-built** (no `AllZeros_h680000.olean`). Leave it; the next
  climb session either builds leg 27 through the cutover procedure or discards it.
  Also holds the sharded packages (regenerable: `campaign.py register-lakefile
  --sharded --from 1 --to 640000 --segments`) and a 142 MB untracked `edges_cache/`.
- `~/arda-million-fix` (`b2/ci-migration`): the #540 worktree.
- Two local validation builds were started and may have finished after this file was
  written: `zzl_aux` cold build (in `~/arda-million/.../lean/zzl_aux`) and the
  standalone quasicrystal build. Check `.lake/build/lib/lean` in each; the CI ladder
  job is the authoritative check regardless.
- Branches `mirrormere/gw-finite`, `anduril/b2-deploy`, `anduril/mod2pi` are fully
  contained in `rh/million-turing` (nothing lost). `~/arda-missions-am/EXTRACTS.md`
  is scratch.

## Grant pass (blocked until #506 lands)

UPDATE: the three re-authorings below were DONE in #542 (climb) + #543 (main, merged).
What remains is the reconcile, then `mission verify --deep-lean` + per-node `mission grant`,
plus the cross-island grant of `MM_rvm_unbounded_mean_density` once #547 is on main.
Original list, for the record:
- `AND_g2_reflected_band`: statement bundles `def d` + `theorem pilot` as one span; the
  artifact interposes other decls — split into two spans / re-author to one decl.
- `MM_bragg_defect_witness`: decl name `bragg_defect_witness` no longer exists in
  `BraggDefect.lean` (present: `defect_witness_online/offline`, `bragg_defect_eq_one`,
  `defect_leakage_gap`, …) — re-point.
- `MM_offline_pairs_le_defect`: statement carries explicit binders, artifact uses
  section variables — re-author against the section form.
Then `mission verify --deep-lean` + per-node `mission grant`.

## Where the next session should start (frontier, not plumbing)

The roadmap's critical path is the **corridor bound** `|ζ′/ζ(σ+it)| = O(log² T)` on the
strip corridor: it is the unique four-consumer blocker (Routes A/B/D and the limit
explicit formula all consume it), it is brick-shaped like Backlund (classical analytic
theorem, not certificate-shaped), and nobody is on it. Inputs already in-tree:
effective dVP (`riemannZeta_ne_zero_region`, effective constant), Backlund
`S(T) = O(log T)` (#489–#500), effective RvM counting (#505–#520), the
Herglotz/Blaschke zero-sum machinery (#223/#247/#256/#257). The E6 RvM port probe
(go/no-go on two external Lean artifacts) is the recommended gate before it.

The operator's Hilbert–Pólya / bosonic-permanent thought (2026-09-16) was assessed:
partition-function zeros are Lee–Yang zeros in temperature (Bost–Connes / primon gas),
not HP eigenvalues; the "explosion" is the pole at s = 1, not an off-line zero; torus
spectral zeta = Epstein zeta = a known off-line family. Nearest live lane is the
mirrormere torus-section ladder; a cheap falsifier is `per(I − P)` on bipartite
torus grids in a fugacity variable. Not built.

## Operational notes
- Merges: `gh pr merge <n> --merge` must be run by the operator (auto-mode classifier
  denies the agent).
- Local Lean builds work (elan 4.2.3; per-project pin v4.32.0). `timeout` is not on this
  macOS. `python3` is 3.9 (has python-flint 0.6.0 with Platt; lacks `tomllib` — use the
  `tomli` shim for `telperion verify`). No python ≥ 3.11 with sympy on PATH.
- Actions cache is at its 10 GB cap: do not design CI around `actions/cache` for oleans;
  `lake exe cache get` (Mathlib CDN) is the dependable path.

## Addendum 2026-09-17 (owner session, after review against live state)

Verified: #540 stacks on #539; the three campaign branches are local-only and
fully contained in `rh/million-turing`; leg 27 is untracked and unbuilt; the
`zzl_aux` cold build is complete (686 oleans, `lake build --no-build` clean);
the three grant-ledger FAIL reasons match `attempts.jsonl` on main.

Corrections to the text above:
- **#539 shows three red Lean jobs** (`bragg-amplitude-compiles`,
  `selfinversive-rigidity-compiles`, `zeta-localization-suite`). They fail
  identically on the base branch at `cf3ac2a` (Lake cannot spawn the freshly
  built Mathlib `cache` binary -- the oversized-lakefile E2BIG problem), and
  #540 removes/relocates those jobs; on #540 the bragg and selfinversive jobs
  pass. Merge #539 despite the red.
- **The quasicrystal standalone local build had NOT finished** when this file
  was written (`LeeYangCore`, `BoundaryLemmas` out of date). It has since been
  run to completion locally (3114 jobs) and the CI job on #540 passes.
- `~/arda-million` also carries **eight modified tracked files**, not only
  untracked ones: three are #540's own content applied locally (quasicrystal
  lakefile/manifest, `campaign.py`, the h375000 lakefile) and five are leg-27
  registrations (`lakefile.toml` +3601 sharded libs, `AxiomGuardRHInBox.lean`
  +3680 band imports, `campaign_state.json`, `edge_stretch.json`). All
  regenerable; "leave it" covers them too.

Grant pass -- no longer blocked on authoring, only on the reconcile:
- **#542** (`fix/grant-preflight` -> `rh/million-turing`, stacked on #540):
  artifact-side restatements `BraggDefect.bragg_defect_witness` and
  `DefectDictionary.Standalone.offline_pairs_le_defect`; both axiom-clean.
- **#543** (`fix/grant-preflight-and-statement` -> `main`): `AND_g2_reflected_band`
  re-authored through the registry writer to the contiguous span
  d / ok / grid / pilot; ledger attempts for all three nodes.
- All three nodes now MATCH under main's gate. **The registry is main-owned**:
  main carries the sha256 statement headers and the #532 nodes that the climb
  branch lacks, and the climb branch's `verify.py` predates the #534 stripper
  fix (its `/--` handling produces false mismatches). Make registry edits on
  main and artifact edits on the climb branch; grant from main after #506.

Merge order now: #539 -> #540 -> #542 (all into `rh/million-turing`), #538 and
#543 into `main` (both independent, ready), then #506.

E6 probe launched (cc-chen-tech/riemann-pnt-lean4 vs `RvMUnboundedMeanDensity
zetaOrdinates`); result to be filed as `E6_PROBE_2026-09-17.md` when in.
