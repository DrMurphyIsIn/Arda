# COMPUTE JOB PLAN: `AND_ladder_1e6` (Anduril G1, height ladder 640000 -> 1000000)

Date: 2026-09-22. Worktree of record for the JOBS: `/Users/peterwmurphy/arda-million`
(production ladder). This document lives in `arda-goal-weil` (branch `mm/gauss-window`)
and is a plan only: no Lean was written, no job was started, no git command was run.

**conjecture1_proved = False. Nothing in this document, and nothing the jobs below
produce, proves the Riemann Hypothesis.** The node is a finite-height restriction
(`0 < Im rho <= 10^6`). Finite verification is instrumentation; it is not evidence
for RH (certified prefixes are what on-line verification always produces). The
RH-equivalent nodes (`RH_conjecture`, `MM_zeta_comb_membership`) are out of scope.

---

## 0. Verdict in one paragraph

The node is correctly routed as a JOB PLAN, not a proof task: every Lean line the
node needs is emitter output (`campaign.py`), the T5 driver has zero structural
failures over 27,503 bands, and the per-band cost is linear in T. The remainder to
`T = 10^6` is **8 more legs of driver time (~670-700 CPU-hours) plus 9 serialized
`lake build` legs (~1 hour each)**, i.e. about **2 days wall at 24 driver lanes,
~4.5 days at 8 lanes**, on the 32-core / 96 GiB machine, with **~8 GB of new
persistent disk** provided the C IR is pruned after every leg (it is already pruned
today). The **grant is not gated on any of this**: when
`all_nontrivial_zeros_up_to_height_1000000_of_bands` builds, it carries exactly the
same per-segment `BandHyp` binders plus the `hgamma` 55/16-floor binder that keep
`AND_ladder_h280000` open. Discharging those (the StripClear two-box glue) is a
separate, shared, non-compute obligation.

---

## 1. Measured state on 2026-09-22 (corrections to the 09-14/09-18 triage)

Measured directly in `/Users/peterwmurphy/arda-million/telperion/examples/zeta_zero_localization`:

| Quantity | Triage said | Measured now |
|---|---|---|
| Bands ok in `campaign_state.json` | 25,743 | **27,503** ok, 0 refused, 1,156,302 zeros in bands |
| Emitted frontier (band `.lean` + `.cert.json`) | 680000 | **680000** (leg 640000-680000: all 1760 bands emitted, all on retry rung 1 = density 1.0 / prec 300) |
| Built frontier (oleans) | 640000 | **640000** (`AllZeros_h640000.olean` present; 25,711 `RHInBoxT_*.olean`; no band olean above 640000) |
| Segment/capstone sources | to 680000 | `AllZeros_h641000..680000.lean` all present (46 files in the 64xxxx-68xxxx range); `AllZeros_h680000.lean` is 1676 lines with 680 `hbands_<S>` binders |
| Lakefile registration | -- | monolith `lean/lakefile.toml` already lists all 27,504 `RHInBoxT_*` libs and 683 `AllZeros_h*` libs, including the 640000-680000 leg; file is now **3.54 MB**, `defaultTargets` line **1.49 MB** |
| `AxiomGuardRHInBox.lean` | -- | 59,167 lines, 30,260 `#print axioms`, already imports `AllZeros_h680000` (guard-update ran for the leg) |
| CPU-hours spent (driver) | 462 | **526.3** (sum of `secs` over all ok bands) |
| Driver cost per band | 125 s @ 640000 | mean **122.9 s** at 630000-640000, **128.9 s** at 640000-660000, **133.4 s** at 660000-680000; max 513 s; still linear in T (~1.97e-4 s per unit of T) |
| `.lake` on disk | 25 GB | **25 GB** = 12 GB `build/lib` (10.0 GB band artefacts over 128,651 files, 1.86 GB capstone artefacts) + 13 GB `packages`; **`build/ir` is absent (already pruned)** |
| Volume | 42 GiB free | **42 GiB free of 926 GiB (96% used)** |
| Toolchain | v4.32.0, mathlib 81a5d257 | confirmed identical in both worktrees (`lean-toolchain` v4.32.0; `lake-manifest.json` mathlib `81a5d257`, batteries `023ce7d6`); `lake` 5.0.0 on PATH |
| Driver deps | -- | `python-flint 0.6.0` on Python 3.9.6 (Platt `zeros_in_interval` route via `telperion.arb_enclosure`) |
| Previous leg build wall-clock | not recorded | **leg 600000-640000: 1760 band oleans in 40 min (09-16 13:37-14:17), 40 capstones in a further 8 min; ~48 min total on 32 cores** |
| Running builds | -- | none (`ps` shows no `lake build`, `campaign.py`, or `generate.py`) |

**So leg 1 (640000-680000) is already at step (5).** Its bands are emitted,
registered, its 40 capstones are emitted, its guard imports are added. It needs only
the single `lake build`, the verification pass, and the state bookkeeping.

Two operational facts the triage did not carry, both verified today:

1. **`lake env` is broken on the monolith locally, not only in CI.** `lake env true`
   in `lean/` returns `could not execute external process 'true'` (rc 255). This is
   the E2BIG wall documented in `B2_MAIN_CI.md` and `B2_DEPLOY_RUNBOOK.md` (macOS
   `ARG_MAX` is 1,048,576 bytes; the `defaultTargets` line alone is 1.49 MB).
   `lake build` on the same monolith **did** work on 09-16 at ~26k modules, so the
   build path and the env path fail at different thresholds. Consequence:
   anything that goes through `lake env lean` -- `campaign.py verify-bands`
   (`telperion.statement_match.statement_match_check` batches its checks into one
   `lake env lean`) and a hand-run `AxiomGuardRHInBox.lean` -- **does not run on the
   monolith today**. Section 4 step (6) gives the working substitute.
2. **The B2 sharded block packages in `arda-million` are empty stubs.**
   `lean/ZetaBands_h25000 .. ZetaBands_h650000/` each contain only a `lakefile.toml`,
   `lake-manifest.json`, `lean-toolchain` and a `.lake/packages` symlink set: zero
   sources, zero oleans. The runbook's `--sharded` route is therefore **not** a
   drop-in alternative here without first populating and building the blocks, which
   would be a second, larger build. This plan stays on the monolith route that
   produced the 640000 oleans.

---

## 2. The statement, the artefact, and the seam between them

### 2.1 Registry statement (what the grant needs)

`telperion/missions/anduril/lean/Statements/AND_ladder_1e6.lean`
(sha256 `d2d81864ddff8cee`, blind-audited clean 2026-09-14):

```lean
theorem all_nontrivial_zeros_up_to_height_1e6 :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000 → ρ.re = 1 / 2
```

Hypothesis-free. Does not pre-restrict `ρ` to the critical strip.

### 2.2 Artefact the jobs produce (what `lake build` will certify)

`AllZeros_h1000000.lean`, emitted by `campaign.py emit-segment --upto 1000000`
following the indexed (B1) template that every capstone since `AllZeros_h4000` uses.
Its shape, read off `AllZeros_h680000.lean` today:

```lean
theorem haC_1000000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 1000000
-- width policy a = 1/4000000 is still valid at 10^6 (needs dlvpRateC >= 3.45e-6;
-- the emitted proof bounds log 1000000 <= 14 via 2.7^14 >= 1.10e6 > 10^6)

def BandHyp : Prop :=      -- ONE indexed hypothesis for the [999000, 1000000] segment
  ∀ i, i < K → ∀ ρ : ℂ, ((1/4000000 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3999999/4000000) →
    (bLo i ≤ ρ.im ∧ ρ.im ≤ bHi i) → riemannZeta ρ = 0 → ρ.re = 1 / 2

theorem segment_999000_1000000 (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000 → 55 / 16 ≤ |ρ.im|) : ...

theorem all_nontrivial_zeros_up_to_height_1000000_of_bands
    (hbands_1000 : AllZeros_h1000.BandHyp) ... (hbands_999000 : AllZeros_h999000.BandHyp)
    (hbands : BandHyp)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000 → 55 / 16 ≤ |ρ.im|) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000000 → ρ.re = 1 / 2 :=
  AllZerosUpToHeight.height_chain 999000 1000000
    (AllZeros_h999000.all_nontrivial_zeros_up_to_height_999000_of_bands hbands_1000 ... hγ999000)
    (segment_999000_1000000 hbands hγ)
```

So the top capstone has **1000 `BandHyp` binders + 1 `hγ` binder** (680 today at
680000). Each band module `RHInBoxT_1d4000000_3999999d4000000_<lo>_<hi>.lean`
proves one `rh_in_box_<tag> : TuringBand.BandStatement re_lo re_hi im_lo im_hi n
<10 Arb edge enclosures> cPB RPB hs1PB` for its stretched certificate box; the
segment's `hcover` lemma (`interval_cases` + `norm_num`) weakens the nominal
partition to the stretched boxes. The kernel checks every implication; the
composition across segments is `AllZerosUpToHeight.height_chain (A B : ℝ)`, which
is width- and package-agnostic.

### 2.3 The seam (what remains hypothetical after the build, and why it is not new)

| Binder in the artefact | What discharges it | Status |
|---|---|---|
| `hbands_S : AllZeros_hS.BandHyp`, one per 1000-segment, S = 1000..999000, plus the top `hbands` | Instantiation from the imported `RHInBoxT_*` modules: each `BandStatement` conclusion must be matched positionally onto the indexed `BandHyp` (index `i` -> band `i` of segment `S`). The band modules are already imported by each `AllZeros_hS.lean`; the instantiation glue is what the roadmap calls the StripClear two-box capstone deliverable. | **Open. Identical to what holds `AND_ladder_h280000` open** (attempts.jsonl 09-14: "grant blocked on (a) the StripClear two-box hypothesis-free capstone glue, (b) the rh/million-turing -> main branch reconcile"). |
| `hγ : ∀ ρ, ζ ρ = 0 → 0 < Im ρ → Im ρ ≤ 1000000 → 55/16 ≤ |Im ρ|` | `StripClear.height_floor_of_box_certs (T := 1000000) hleft hband` where `hleft`/`hband` are the two low boxes `NoZerosInBox_0_1d1000_0_55d16` and `NoZerosInBox_1d1000_999d1000_0_55d16` (both are registered libs in the monolith lakefile). `height_floor_of_box_certs` is generic in `T`; the hypothesis-free wrapper that actually applies it exists only as `StripClear.all_nontrivial_zeros_up_to_height_100_strip_cleared` (T = 100). | **Open, same glue.** A T-generic wrapper is a ~10-line Lean change in `StripClear.lean` or a new `Capstone_h<T>.lean`; it is the lead's to author and is NOT part of this compute plan. |
| Arb/FLINT enclosures inside each `rh_in_box_<tag>` (the `av2, aht, ahb, ag1, ag2` edge intervals and the Platt zero count `n`) | The T5 trust boundary as documented in `RH_IN_BOX_INTERFACE.md` and `MILLION_CAMPAIGN_2026-09-12.md`; gated per band by the `.cert.json` sidecar and the `verify-bands` statement-match audit (with an `n+1` negative control that must mismatch). | **Unchanged by this plan.** No new trust assumption is introduced between 640000 and 10^6: same driver, same width, same retry ladder, same BandStatement shape. |

**What the finished artefact would establish:** that the kernel accepts
`all_nontrivial_zeros_up_to_height_1000000_of_bands` with axioms
`[propext, Classical.choice, Quot.sound]` -- i.e. the finite-height restriction of
RH to `Im rho <= 10^6` GIVEN the per-segment band hypotheses and the 55/16 floor,
each of which is itself the conclusion of an already-built kernel-checked module.

**What it would NOT establish:** the registry statement (until the two glue items
above are authored and built), anything about zeros above 10^6, or anything about
RH. Nothing here proves RH. conjecture1_proved = False.

---

## 3. Resource budget (measured, then extrapolated)

### 3.1 Driver (Arb T5, `generate.py --box ... --turing`)

Per-band cost model from the state file: `secs ~= 1.97e-4 * T` (122.9 s at
T ~ 635000, 133.4 s at T ~ 670000). All 3,520 bands above 600000 landed on retry
rung 1 (density 1.0, prec 300); the retry ladder `[(1,300),(2,300),(4,300),(6,300),(8,450)]`
has not been exercised at this height, so the 5% contingency below is generous.

| Leg | Range | Bands (from `campaign.py plan`) | Mean T | s/band | CPU-h | Status |
|---|---|---:|---:|---:|---:|---|
| 1 | 640000-680000 | 1760 | 660000 | 130 (measured) | 64 (spent) | **emitted; build pending** |
| 2 | 680000-720000 | 1760 | 700000 | 138 | 67 | to emit |
| 3 | 720000-760000 | 1760 | 740000 | 146 | 71 | to emit |
| 4 | 760000-800000 | 1772 | 780000 | 154 | 76 | to emit |
| 5 | 800000-840000 | 1840 | 820000 | 162 | 83 | to emit |
| 6 | 840000-880000 | 1840 | 860000 | 169 | 86 | to emit |
| 7 | 880000-920000 | 1840 | 900000 | 177 | 90 | to emit |
| 8 | 920000-960000 | 1840 | 940000 | 185 | 95 | to emit |
| 9 | 960000-1000000 | 1840 | 980000 | 193 | 99 | to emit |
| | **remaining (legs 2-9)** | **14,492** | | | **~668, budget 700** | |

Wall-clock for the remaining driver work (driver is one single-threaded process per
band; `ThreadPoolExecutor(--jobs)` fans out subprocesses; memory per driver is far
below 1 GiB so the 96 GiB box is not a constraint):

| Lanes | Wall for 700 CPU-h |
|---:|---|
| 8 | ~88 h (3.7 days) |
| 16 | ~44 h |
| 24 | ~29 h |
| 28 | ~25 h |

The roadmap's "9-12 wall-hours to 10^6" was measured at T ~ 30000 (2.7 s/band) and
is obsolete by a factor of ~50 per band.

### 3.2 `lake build` (one per leg, serialized per island)

Measured leg 600000-640000: 1760 band modules in 40 min + 40 capstones in 8 min on
32 cores. Band-module cost does not grow with T (zeros per band is pinned at ~43 by
the height policy `h(T) = min(40, floor(2*pi*43 / log(T/2pi)))`, ~22-23 at this
height). Capstone elaboration grows with binder count (680 -> 1000) and each
capstone re-lists every prior binder: budget the capstone phase at 8 min growing to
~15 min. **Plan 60-75 min per leg, ~10 h total for 9 legs, strictly serialized.**
The band driver for leg k+1 may run concurrently with the build of leg k (different
tools, different files), but cap driver lanes at 8 while a build is running so the
build keeps ~24 cores.

### 3.3 Disk

| Item | Per leg | Legs 1-9 total | Note |
|---|---:|---:|---|
| Band artefacts (`.olean`+`.ilean`+`.trace`+2 hashes, ~389 KB/band measured over 25,711 bands; 351 KB is the olean alone) | ~0.7 GB | **~6.3 GB** | persistent |
| Capstone artefacts (measured 2.9 MB avg to 640000; grows with binder count) | ~0.15-0.2 GB | **~1.6 GB** | persistent |
| Sources (`.lean` 7.6 KB + `.cert.json` 0.6 KB per band; capstone `.lean` ~60 KB) | ~15 MB | ~0.13 GB | persistent |
| Monolith `lakefile.toml` + `AxiomGuardRHInBox.lean` growth | -- | ~2.5 MB | persistent |
| **C IR (`.lake/build/ir`)** at the runbook's measured 6.2-6.7 MB per module | **~11-12 GB transient** | ~100 GB if never pruned | **prune after every leg**; the tree is already in the pruned state (no `build/ir` today) |

Net: **~8 GB new persistent, ~12 GB transient peak per leg.** With 42 GiB free this
fits without reclaim **only if** IR is pruned after every leg and nothing else on the
volume grows. Operating rule: **do not start a leg build with < 20 GiB free**; do not
start the campaign without the lead authorizing at least one reclaim below.

**Do NOT reflink the 25 GB `.lake` into `arda-goal-weil`.** It is not needed
(the jobs run in `arda-million`) and it would consume most of the free space.

### 3.4 Reclaim candidates (lead must authorize; none deleted by this plan)

All measured today (`du -sh .../zeta_zero_localization/lean/.lake`, top = highest
`AllZeros_h*.olean` present):

| Worktree | `.lake` size | Built to | Superseded by |
|---|---:|---|---|
| `~/arda-b2` | 18 GB | 560000 | arda-million @ 640000 |
| `~/arda-anduril-b2` | 15 GB | 400000 | arda-million |
| `~/arda-gw-finite` | 15 GB | 400000 | arda-million |
| `~/arda-li-ladder` | 7.7 GB | 100 | (mathlib copy + h100 island only) |
| `~/arda-main-refreeze` | 7.2 GB | 100 | (mathlib copy) |
| `~/arda-main-test` | 7.2 GB | 100 | (mathlib copy) |
| `~/arda-source-mining` | 7.2 GB | 100 | (mathlib copy) |
| `~/arda-typenone-fix` | 7.2 GB | none | (mathlib copy) |

Reclaiming `arda-b2` alone (18 GB) lifts free space to ~60 GiB and removes the
"< 20 GiB" risk for the whole campaign. Reclaiming the three ladder snapshots
(48 GB) gives ~90 GiB.

---

## 4. The per-leg recipe (exact commands)

All commands run from
`/Users/peterwmurphy/arda-million/telperion/examples/zeta_zero_localization`
with `A` = leg start, `B = A + 40000`. Legs: (640000,680000), (680000,720000), ...,
(960000,1000000). Steps are strictly in order within a leg. Only ONE `lake build`
may run in the `zeta_zero_localization` island at a time; nothing else may build it
in `arda-million` while a leg build is running.

### Pre-flight (once, before leg 1)

- `df -h /Users/peterwmurphy` shows >= 20 GiB free (42 GiB today).
- `ls lean/.lake/build/ir` -> does not exist (confirmed today). If it exists from an
  aborted build, `rm -rf lean/.lake/build/ir` first.
- `ps aux | grep -E "lake build|campaign.py|generate.py"` -> nothing running (confirmed).
- `python3 campaign.py status` -> `bands ok: 27503 refused: 0` (confirmed).
- Confirm `python3 -c "import flint; print(flint.__version__)"` -> 0.6.0 (confirmed).

### Step (1) Confirm the schedule

```
python3 campaign.py plan --from A --to B
```
Expect: 1760 / 1772 / 1840 bands per the table in 3.1, `h=21..23`,
`width=1/4000000`, segments ending at every 1000 from A+1000 to B. Any deviation from
the table (band count, a band with `h > 40`, a non-4000000 width) stops the leg.

### Step (2) Emit the bands (the Arb T5 driver; this is the CPU cost)

```
python3 campaign.py emit-bands --from A --to B --jobs N
```
- `N = 24-28` when no lake build is running; `N = 8` while a leg build runs.
- Idempotent and checkpointed: `campaign_state.json` is saved after every band; a
  band already `ok` with its `.lean` and `.cert.json` present is skipped, so a killed
  run resumes by re-issuing the same command. Leg 1 will report `1760 done, 0 to emit`.
- Exit code 1 means at least one band was REFUSED after the full 5-rung retry ladder
  (`(1.0,300) -> (2.0,300) -> (4.0,300) -> (6.0,300) -> (8.0,450)`). Zero refusals
  have occurred in 27,503 bands. A refusal is a STOP for the leg: the segment
  containing it cannot be emitted (`emit-segment` checks every band module exists).
  Report the band tag and the last stderr line to the lead; do not edit band files.
- Per band the driver writes `lean/RHInBoxT_<tag>.lean` (~7.6 KB) and
  `lean/RHInBoxT_<tag>.cert.json` (~0.6 KB) and records
  `{status, n, density, prec, secs, route: "t5"}` in the state file.

### Step (3) Register in the lakefile

```
python3 campaign.py register-lakefile --from A --to B --segments
```
Adds each new `RHInBoxT_*` and `AllZeros_h<S>` (S = A+1000..B) as a `[[lean_lib]]`
and to `defaultTargets`. Idempotent (`nothing to add` for leg 1, already done). Do
NOT pass `--sharded`: the block packages in this worktree are empty stubs (section 1).

### Step (4) Emit the 40 segment/capstone files

```
for S in A+1000, A+2000, ..., B:  python3 campaign.py emit-segment --upto S
```
(or `python3 campaign.py assemble --from A --to B`, which is steps 3+4+guard-update in
one shot). Each `AllZeros_hS.lean` picks the largest existing `AllZeros_h<A'>` with
`A' < S` as its base, refuses if the segment exceeds `SEG_BANDS = 50` bands (44-46 at
this height, fine) or any band module is missing. Leg 1's 40 files already exist.
Watch the top capstone's line count: it grows ~1.6 lines per segment (1676 lines at
680000, ~2200 at 1000000); this is the B3 "reflected fold" trigger if elaboration of
step (5)'s capstone phase exceeds ~20 min per leg.

### Step (5) ONE `lake build` for the leg

```
cd lean && lake build 2>&1 | tee ../build_leg_A_B.log ; cd ..
```
- Serialized per island. Expected 60-75 min. Expect ~1800 new band oleans + 40
  capstone oleans; jobs count in the `lake` banner will be roughly 1800 + 40 + the
  guard lib from step (6a) below.
- **Immediately after a green build:** `rm -rf lean/.lake/build/ir` (the runbook's
  disk lever; ~11-12 GB per leg). Then `df -h`.
- If `lake build` itself fails with `could not execute external process 'lean'`
  (the E2BIG signature) the monolith has crossed the argv wall for the build path
  too. STOP and report; the only remedy is the B2 sharded layout, which is a lead
  decision (populate + build `ZetaBands_h650000..h1000000`, ~14 blocks, and it
  re-uses no monolith oleans without the runbook's `Replay` wiring).
- A capstone that stalls on elaboration (heartbeat) is the B3 trigger; do not raise
  `maxHeartbeats` by hand in emitted files -- report the leg and the file.

### Step (6) Verification of the leg

Because `lake env lean` is broken on the monolith (section 1), the two verification
tools must be run in forms that do not go through `lake env`:

**(6a) Axiom battery -- as a build-time guard lib, inside the same leg build.**
Write `lean/Guard_h<B>.lean` following the existing `lean/Guard_h25000.lean` exactly
(that file is the emitter's own shape):

```lean
-- GENERATED per leg; DO NOT EDIT. Block-top axiom battery for height B:
-- `lake build` fails unless the capstone depends on exactly
-- [propext, Classical.choice, Quot.sound]. conjecture1_proved = False.
import AllZeros_h<B>
/-- info: 'AllZeros_h<B>.all_nontrivial_zeros_up_to_height_<B>_of_bands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AllZeros_h<B>.all_nontrivial_zeros_up_to_height_<B>_of_bands
```
Register it as a `[[lean_lib]]` + `defaultTargets` entry BEFORE step (5), so it is
checked by the leg's single build (no second build, no `lake env`). Optionally add
one `#guard_msgs` line per intermediate capstone `S` in the leg and for a random
sample of the leg's `rh_in_box_<tag>` theorems. The 59k-line
`AxiomGuardRHInBox.lean` remains the cumulative record (guard-update keeps appending
to it) but is NOT runnable on the monolith and should not be attempted.

**(6b) Statement-match audit (`verify-bands`).** `campaign.py verify-bands --sample 12`
audits only BUILT bands and calls `statement_match_check(env_dir=lean/)`, which
spawns `lake env lean` -- broken here. Two remedies, lead's choice; neither is in
this plan's scope to implement:
  - (i) a ~5-line `statement_match.py` option to invoke `lean` directly with
    `LEAN_PATH` set to the ~10 library dirs (`lean/.lake/build/lib/lean` and each
    `lean/.lake/packages/<pkg>/.lake/build/lib/lean`), which sidesteps the argv
    overflow because `LEAN_PATH` needs library directories, not module names; or
  - (ii) run the audit from a populated sharded block package (the runbook's
    confirmed E2BIG cure), which needs the B2 population first.
  Until one lands, record in the leg's ledger that the statement-match audit for the
  leg is PENDING and the negative-control check has not been run on it. Do not
  claim it ran.

### Step (7) Bookkeeping, then the next leg

```
python3 campaign.py status
```
Expect `bands ok` to rise by the leg's band count, `refused: 0`. Append one line per
leg to `MILLION_CAMPAIGN_2026-09-12.md`'s ledger (lead commits): leg range, bands,
zeros certified (from `plan`'s estimate vs. the sum of `n` in the state file), driver
CPU-h (sum of `secs`), build wall-clock, oleans added, `df` after prune, guard
result, verify-bands result or PENDING. The state file itself is updated by
`emit-bands`; no manual edit.

### After leg 9

`AllZeros_h1000000.olean` exists; `Guard_h1000000` built green. Then, and only then,
the lead:
1. authors the discharge glue (section 2.3: `BandHyp` instantiation from the
   `RHInBoxT_*` modules for all 1000 segments + `hγ` via
   `StripClear.height_floor_of_box_certs 1000000` from the two low boxes) producing a
   hypothesis-free `all_nontrivial_zeros_up_to_height_1e6` whose statement is
   byte-identical (modulo the generated header) to the registry stub;
2. runs the blind read-back on that file;
3. resolves the `rh/million-turing -> main` reconcile so the artefact is on the
   branch the registry points at;
4. grants `AND_ladder_h280000` (same glue, lower height) and `AND_ladder_1e6`.

Items 1-4 are not compute and are not scheduled here.

---

## 5. Overlap schedule (recommended)

Driver-bound with the builds tucked underneath:

| Wall window | Driver lanes | Build |
|---|---|---|
| t0 | -- | leg 1 build (bands already emitted) ~1 h, then prune IR |
| t0 .. +1 h | 8 lanes on leg 2 | (leg 1 building) |
| +1 h .. ~+30 h | 24-28 lanes on legs 2..9 sequentially | when leg k's bands finish: steps 3,4,6a then leg k build (drop lanes to 8 for ~1 h, then back up) |
| ~+30-36 h | -- | leg 9 build, prune, guard, status |

Total: **~1.5-2 days at 24+ lanes; ~4.5 days at a flat 8 lanes.** If the machine is
shared with other Lean builds (other islands: only `rvm_bridge` and `li_positivity`
are built in `arda-goal-weil`; each is a separate island and may build concurrently
with this one, but they compete for cores), scale the driver lanes down, not the
build.

---

## 6. Risk register

| Risk | Signal | Response |
|---|---|---|
| Disk exhaustion mid-build (IR ~12 GB transient) | `df` < 20 GiB before a build | do not start; ask lead to authorize a reclaim from 3.4 |
| Monolith crosses the `lake build` argv wall | `could not execute external process 'lean'` from `lake build` | STOP; B2 sharded migration is a lead decision (blocks are empty stubs) |
| Capstone elaboration growth (1000 binders; each capstone re-lists all prior) | capstone phase of a leg build > 20 min, or heartbeat error in `AllZeros_h<S>` | STOP; B3 reflected fold ("eventually mandatory" per MILLION docs) is an emitter change for the lead, not a per-file edit |
| Close-pair refusal at high T | `emit-bands` exit 1, `REFUSED` line | STOP the leg at the segment; report tag; the retry ladder is exhausted by design |
| Width policy at the boundary | `haC_1000000` fails `norm_num` | verified moot: `_log_exp_bound(1000000) = 14` (smallest L with 2.7^L >= B), the same L = 14 that `haC_640000` used and built green on 09-16, so `haC_1000000` is the identical inequality `1/4000000 <= dlvpRateC / 14`; no new arithmetic obligation enters between 640000 and 10^6 |
| `verify-bands` and `AxiomGuardRHInBox.lean` silently un-runnable | any leg ledger line claiming they ran on the monolith | use 6a for axioms; mark 6b PENDING until a remedy lands; never claim a check that did not execute |
| Concurrent builds in the island | a second `lake build` in `zeta_zero_localization` | forbidden; the orchestrator serialises; check `ps` before every step (5) |
| Driver contention with a build | build wall-clock > 90 min | drop lanes to 8 during builds |
| Mis-attributing progress | any wording that the ladder is "evidence" for RH | it is not; every document and header states conjecture1_proved = False |

---

## 7. Obligations (named, with owner)

Compute (this plan; executable by an operator without judgement calls):
- C1. Leg 1 `lake build` + IR prune + `Guard_h680000` (~1 h). Prerequisite: none.
- C2. Legs 2-9 `emit-bands` (~700 CPU-h; 14,492 bands). Prerequisite: none.
- C3. Legs 2-9 register / emit-segment / guard-lib / `lake build` / prune (~9 h serialized).
- C4. Per-leg ledger lines (7 fields each) for the lead to commit.

Lead decisions (blocking or de-risking):
- L1. Authorize disk reclaim (section 3.4); at minimum `arda-b2` (18 GB).
- L2. Pick the `verify-bands` remedy (6b-i direct `lean` with `LEAN_PATH`, or 6b-ii sharded block package); until then the statement-match audit is PENDING per leg.
- L3. Decide the B3 reflected-fold trigger threshold (this plan: 20 min capstone phase).

Grant gate (NOT compute; shared with `AND_ladder_h280000`):
- G1. `BandHyp` instantiation glue from the imported `RHInBoxT_*` modules (1000 segments at 10^6; 280 at 280000).
- G2. `hγ` via `StripClear.height_floor_of_box_certs T` with a T-generic hypothesis-free wrapper (exists only at T = 100 today).
- G3. `rh/million-turing -> main` reconcile.
- G4. Blind read-back of the hypothesis-free artefact against the registry statement (sha `d2d81864ddff8cee`), then lead grant.

---

## 8. Sources consulted (all read-only)

- `telperion/missions/anduril/nodes/AND_ladder_1e6.toml`, `.../AND_ladder_h280000.toml`,
  `.../lean/Statements/AND_ladder_1e6.lean`, `.../attempts.jsonl` (arda-goal-weil).
- `arda-million/telperion/examples/zeta_zero_localization/campaign.py` (constants,
  `emit_one_band`, `cmd_emit_bands`, `cmd_register_lakefile`, `cmd_emit_segment`,
  `cmd_guard_update`, `cmd_assemble`, `cmd_verify_bands`, `emit_segment_file`),
  `campaign_state.json` (27,503 records), `lean/lakefile.toml`, `lean/AllZeros_h680000.lean`,
  `lean/AllZeros_h640000.lean`, `lean/StripClear.lean`, `lean/AllZerosUpToHeight.lean`,
  `lean/Guard_h25000.lean`, `lean/AxiomGuardRHInBox.lean` (size and imports only),
  `lean/.lake/build/lib` (mtimes, sizes), `lean/lake-manifest.json`, `lean/lean-toolchain`.
- `arda-million/telperion/docs/B2_DEPLOY_RUNBOOK.md`, `B2_MAIN_CI.md`.
- `arda-goal-weil/telperion/docs/RH_ASCENT_PLAN_2026-09-18.md` (F5-3),
  `WALL_BACKLOG_MAP_2026-09-18.md` (F4 row), `ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md` (G1 row).
- `df`, `du`, `ps`, `sysctl hw.ncpu hw.memsize`, `getconf ARG_MAX`, `lake env true` (failure reproduced).

conjecture1_proved = False. Nothing here proves RH.
