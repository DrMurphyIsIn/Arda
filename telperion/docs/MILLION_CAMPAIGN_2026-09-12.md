# The 10^6 Campaign — Day 1 (2026-09-12)

Extends the T = 4000 tiled Turing verification (3,474 zeros, #358) toward T = 10^6
(~1,747,000 zeros).  Supersedes the *estimates* in `MILLION_ROADMAP_2026-09-09.md`
with measured Day-1 constants and records the campaign machinery now in-tree.
`conjecture1_proved = False` throughout — this verifies RH for finitely many zeros;
it is not a step toward proving RH.

## What shipped today

1. **Campaign orchestrator** `examples/zeta_zero_localization/campaign.py`:
   band planning (per-1000-block, integer edges, n ≈ 43 target), parallel
   checkpointed emission with the close-pair retry ladder (density 1→2→4→6→8,
   prec 300→450), lakefile + axiom-guard registration, and AllZeros_h<B>
   segment/chain codegen following the AllZeros_h4000 template byte-faithfully.
2. **Close-pair re-sweep knob**: `generate.py --density` (the manual re-sweeps of
   the 2000–4000 campaign, now automatic).
3. **The [4000, 8000] leg** at the campaign width `a = 1/4,000,000` (valid to
   10^6: `a ≤ dlvpRateC / log T` holds with margin at T = 10^6): 103 bands,
   ~4,356 zeros — more than doubling the verified count — chained as
   AllZeros_h5000 → h6000 → h7000 → h8000 (depth-5 exercise of `height_chain`).

## Measured constants (Day 1, M3 Ultra, width 1/4e6)

| Quantity | Roadmap estimate | Measured today |
|---|---|---|
| Driver per band (T≈4000) | "seconds–minutes" | **9.1 s** (winding + line sweep + emit) |
| Lean elaboration per band (n=42, 7-digit corners) | ~90–110 s | **51 s** |
| Band plan to 10^6 | ~39,000 bands | 41,895 bands, ~1,743,671 zeros, 996 segments |

Cost model at these constants (driver cost grows ~√T; Lean cost is
height-independent at fixed n and digit count):

* **Lean**: 41,895 × ~51 s ≈ 594 core-hours ≈ **2 wall-days on 13 lanes**.
* **Driver**: ~9 s at 4k scaling ~√T ⇒ ~140 s/band at 10^6; integrated ≈
  700–900 core-hours ≈ **2–3 wall-days on 13 lanes** (embarrassingly parallel).

**Verdict: ~1 week wall-clock on this machine on the primary route alone** —
substantially better than the roadmap's 2–3 weeks, before any Turing-route saving.

## The two structural items before the far ladder

1. **Binder scaling (blocking beyond ~T = 2–4·10^4).**  The `_of_bands` capstones
   accumulate hypotheses linearly (h8000 carries ~192; 10^6 would carry ~42,000 —
   impossible).  Fix: bundle the per-band Arb input as a single indexed Prop
   (`def BandInput (a : ℝ) (T0 T1 : ℝ) : Prop := <hLine ∃-form> ∧ <hArb form>`) and
   state capstones with ONE quantified hypothesis
   `∀ i < K, BandConcl (edges i) (edges (i+1))` driven by a `Fin K → Prop` table,
   plus per-package guards.  Conclusion shapes stay identical, so the chain
   composes across the redesign boundary.  This is emitter+glue codegen work, no
   new mathematics.
2. **Lake packaging.**  One lakefile cannot hold 42k modules; shard into ~80
   packages of ~500 modules (one per 12.5k-height block), chained through their
   width-free conclusions (`height_chain` is package-agnostic).

## The Turing route (the 10× lever) — status after the Backlund/RvM arcs

The newer RH work slots in exactly as the roadmap's T4/T5 projected; all
mathematical pieces are now kernel-clean on main:

| Piece | Status | Where |
|---|---|---|
| T2 effective θ | DONE | Riemann–Siegel theta, branch-cut-free (dVP bricks) |
| T3 RvM identity N(T) = θ/π + 1 + S(T) | **DONE** (#427) | `RvMLiUnified.riemannXi_winding_eq_RvM` — and it names the SAME `riemannXi` as Li's criterion (`rvm_and_li_share_riemannXi`), so the count object and the Li-positivity object are literally one function |
| Band-difference form 2π·N_band = edge argument-changes | **DONE** (#374) | `DiffractionCore.zero_count_band_edge_decomp` (classical rectangle [-1,2]×[T0,T1]) |
| Effective Backlund \|S(T)\| ≤ log((4T+19)/‖F_T 2‖)/log(7/6) + 2 | **DONE** (#484–#500) | `Backlund.riemannS_abs_le_log_of_ne_zero` (li island); its confinement/partition bricks (#489–#496) are the reusable *argument-change enclosure* machinery |
| T5 band template swap | **NOT BUILT** — the remaining engineering | new emitter |

**T5 assembly plan** (replaces the 4-edge winding certificate per band):
consume `zero_count_band_edge_decomp` with Arb-enclosed edge argument-changes:

* the two horizontal edges AH(ζ, T, 2, −1) — ~3 σ-units at heights T0/T1, cheap,
  and SHARED between adjacent bands (each interior edge priced once);
* the vertical ζ edge AV(ζ, 2) — `Re ζ(2+it) ≥ 2 − π²/6 > 0`
  (`RvMBacklundCenter.re_zeta_two_ge`) keeps it in the right half-plane, so the
  Backlund confinement lemmas certify it from sparse samples;
* the two Γℝ verticals — Archimedean, θ-shaped, enclosed from the digamma
  integral (T2) or directly.

This eliminates both in-strip long verticals (the expensive, oscillatory Arb
input) and the O(n²) box-coordinate Lean blocks.  Projected ≤10 s/band
elaboration and ~5× driver saving ⇒ **10^6 in ~2–3 wall-days end-to-end**, and
the per-band certificate becomes height-uniform in shape.  The double-check
discipline stays: line sign-count must equal the RvM edge count per band.

Recommended: build T5 while the primary-route ladder climbs (they meet in the
middle; every primary-route band already emitted stays valid — the chain
composes segments of different certificate types through their width-free
conclusions).

## T5 LANDED (same day) — reassessed wall time

The Turing band template is BUILT and adopted (`TuringBand.lean` +
`arb_edges.py` + `emit_turing_band.py` + `--turing`; `TURING_FROM = 24000`).
Measured A/B on the same N=42 band: driver 9.1 → 2.3 s (4×), Lean 51 → 4.8 s
(10.6×, now n-independent — profiling showed the true bottleneck was the
2N+1-component existential `obtain`, killed by the list-form `hLine`).

**Reassessed cost for the remaining climb [2.4·10⁴, 10⁶] (~40,000 bands):**

| Workload | Pre-T5 | With T5 |
|---|---|---|
| Lean | ~1,230 core-hr | **~55 core-hr** (4.8 s/band, flat) |
| Driver | ~1,490 core-hr | **~190 core-hr** (2.3 s at 4k, √T growth on ζ parts) |
| **Wall on this M3 Ultra (~27 lanes)** | ~4–5 days | **~9–12 hours** |

Driver now dominates; the Platt-multieval line sweep (OS front, shim already
in-tree) is the next ~30–40% cut.  Remaining structural item: the chain-glue
`AllZeros_h<B>` files still accumulate hypotheses linearly (h24000 = 636
binders / 134 KB) — tolerable to ~10⁵, then apply the same list/bundling trick
to the segment hypotheses (the per-band listing is documentary only; nothing
is ever discharged in-kernel, so a single indexed hypothesis per segment is
trust-equivalent).

## Trust boundary (unchanged)

KERNEL: dVP zero-free region + functional equation + argument principle +
winding algebra + IVT sign-change zeros + rate inequality + all glue.
ARB NON-KERNEL INPUT (documented hypotheses of every band theorem): the winding
count N, the on-line zeros (`hLine`), the edge/integrability bundle (`hArb`),
and the height floor `hγ` (55/16), discharged at assembly by StripClear.

## HONESTY FLAG (2026-09-12, evening): the winding-route `hArb` is over-quantified — VACUOUS as stated

**Finding.**  The winding-route per-band hypothesis
`hArb : ∀ (E s d), DifferentiableOn E rect → (split identity on ball) → (… ∧ (∀ ρ ∈ s, ρ in-band) ∧ …)`
is mathematically FALSE for every band: augment the canonical Blaschke data
with an out-of-band junk point `ρ'` carrying `d ρ' = 0` (or `ρ'` outside the
ball with any `d`, absorbed into `E`) — the split premise is preserved and the
in-band conjunct fails.  A false hypothesis can never be discharged, so the
winding-route band theorems are vacuous implications; the tiled ladder's
honest content currently rests only on their (unfalsifiable) hypothesis shape.
This is a STATEMENT bug in the emitter (over-quantification chosen to avoid
naming `hs1` in the signature), NOT a driver-data or kernel bug — and it is
PRE-EXISTING: the same shape ships in the T=100 … T=4000 milestones on main
(#265–#358).  Independently, `choose_ball`'s pole-midpoint radius (~T/√2 at
height) makes the in-band conjunct false even for honest instances.

**Not affected.**  The T5 route (TuringBand): `hins` is stated at the
CANONICAL `zeroFinset cPB RPB hs1PB` (hs1 exposed as a top-level theorem), the
ball is tight (`choose_ball_tight`), and the driver verifies the poke slivers
zero-free via the Platt inventory.  The kernel theorems of BOTH routes
(`rh_in_box_of_certificate`, `zeta_count_eq_winding_generic`, `TuringBand.*`)
are valid implications throughout — the defect is confined to the emitted
hypothesis SHAPE of winding-route band files.

**Remediation (recommended): re-base the ladder on T5.**
1. upTo-1 base lemma (vacuous below the 55/16 height floor via `hγ`).
2. One T5 band `[1,100]` (N = 29; `T0 = 1 > 0` keeps the pole outside).
3. Re-emit `[100, 24000]` uniformly at width 1/4e6 on T5 (~640 bands ≈ 2 h
   driver + 1 h Lean at measured T5 rates) + regenerate the chain files.
   Conclusion shapes are unchanged, so nothing downstream moves.
4. Quarter-integer band-edge nudging for the poke refusals (26/128 in leg 6).
Until then, the honest claim is: kernel-verified T5 certificates from 24000 up
(once leg 6 lands) + kernel-valid but hypothesis-vacuous winding certificates
below.  conjecture1_proved = False, and the T≤24000 milestone claims are
SUSPENDED pending re-emission.

## Remediation execution (same day, late)

1. **Quarter-integer stretch planner — DONE.**  Band certificate boxes stretch
   outward by quarters (cached per edge, Platt-checked against `_POKE = 0.08`)
   until the ball-poke slivers are zero-free; the nominal partition stays round
   and segment glue weakens bounds per branch (`le_trans` + `norm_num`).  The
   26 leg-6 refusals all re-emitted cleanly (~7 s each).
2. **T5 re-base of [1, 24000] — RUNNING.**  `TURING_FROM = 1`; new base lemma
   `upTo_1` (vacuous below the 55/16 floor); uniform width 1/4e6 plan from 1;
   all AllZeros_h1000 … h24000 chain files regenerate against the new plan.
3. **`turing_band` as a first-class Telperion kind — DESIGNED, next session.**
   Registration follows the `certify.py` registry pattern
   (`"turing_band": ("emit_turing_band", "certify_turing_band_point", "TuringBandEmitter")`),
   with the refusal guards already implemented in `run_box_turing` (RvM==line
   cross-check, pinning-width check, poke check) moving into
   `turing_band_certificate`.  The `statement_match` gate
   (`statement_match.statement_match_check`) needs a `.cert.json` sidecar per
   band (n, box, edge literals) plus an INDEPENDENT intended-type renderer —
   worth doing carefully, not hastily, since its whole value is catching
   emitter statement bugs of exactly the kind found today.  Sample-based audit
   (per-segment, not per-band) keeps it affordable.

## G0 GATE RESULT (A0 spike, 2026-09-12 evening) — DIntv confirmed, charter reading adjusted

Measured (M3 Ultra, v4.32, under campaign load): pure-kernel DIntv throughput
~1.0–1.9·10⁴ interval-ops/s (raw RED per plan thresholds); Rat is NOT
kernel-reflectable AT ALL (gcd WF-recursion sticks both rfl and decide) — the
Rat fallback is categorically refuted, DIntv (pure-Int dyadic) confirmed;
elaboration (not kernel) dominates end-to-end and is killed by Array-Int
literals (List-of-tuples caused 30–68s typeclass blowups + a maxRecDepth wall).

CONSEQUENCES (within the plan's pre-authorized A0 kill-criteria path):
1. A4 BandData is Array-Int-shaped, never nested List tuples.
2. Full in-kernel `decide` of a whole RvM band (~4·10⁷ ops) is impractical at
   any height; kernel-only `decide` remains viable for SMALL spot-check units.
3. G4 reading adjusted: "10⁹ kernel-only" → "10⁹ with native_decide bulk +
   kernel-only-decide SPOT-CHECK protocol (random bands, pure 3-axiom)" —
   flagged to the operator; matches the hybrid-ladder charter's spirit, moves
   the native island earlier on the critical path.
4. girving/interval stays only as the native-island week-3 trigger.
