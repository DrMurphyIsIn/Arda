# PROGRAM ANDÚRIL — kernel certification of the zeta zeros past 10¹³

*(Draft — being refined with scout findings; sections marked [SCOUT] pending.)*

## Context

Today's session took the kernel-verified Turing ladder from 3,474 zeros (T=4000)
to 32,988+ zeros (T=28000→36000 and climbing) on the new T5 route: RvM
edge-decomposition band certificates with kernel statement-match gates against a
canonical `BandStatement` Prop, after discovering and remediating a vacuous
hypothesis shape in the inherited winding route. Measured T5 economics: ~6s
driver + ~5s Lean per ~43-zero band; ~9–12 wall-hours to 10⁶ on this M3 Ultra.

The user now directs: build ALL the pieces of a program to surpass **10¹³
certified zeros** (Gourdon's numerical record; Platt–Trudgian's rigorous-numeric
record is 3·10¹²; NO kernel-certified verification exists at any height but
ours). Analysis established three forced regime changes:

1. **Driver**: per-point rigorous evaluation (~√T/eval) must become FFT-amortized
   (Platt's `acb_dirichlet_platt_multieval`, already present in our bundled
   libflint) — per-zero cost drops to polylog.
2. **Kernel**: per-band emitted-literal `norm_num` certificates (~9 zeros/sec)
   must become **computational reflection**: a verified interval evaluator in
   Lean + a `checkBand : BandData → Bool` with a once-proven correctness theorem,
   discharged by `decide` (kernel-only) or `native_decide` (trust dial).
   The irreducible certificate mass is Ω(N) per-zero data ≈ 30–300 TB at 10¹³.
3. **Glue**: per-segment chain theorems must become an indexed/bundled form now
   (binders: 1,036 at h36000, blocking ≈ 10⁵) and a reflected fold later.

## Program structure (five workstreams, agent team)

### WS-A: Verified evaluator (the summit) — "reflection track"
*(Design finalized by reflection-architect; full memo to be committed as
`telperion/docs/REFLECTION_TRACK_DESIGN.md` at execution start.)*
- **A0 spike FIRST** (0.5–1 aw): kernel-throughput benchmark on v4.32 in the
  exact planned style (dyadic fold checker, 1000 points; Rat-vs-dyadic
  differential; big-literal elaboration curve). All go/no-go numbers re-base on
  it. Green ≥3·10⁵ interval-ops/s; <3·10⁴ ⇒ native-first re-plan.
- **A1. In-house dyadic interval core `DIntv`** (mantissa/exponent Int pairs;
  GMP-friendly; division-free; ~3–4 aw) — NOT a girving/interval port (v4.26
  toolchain gap; UInt64 design wrong for kernel whnf). Transcendentals by
  VERIFY-NOT-COMPUTE: untrusted Arb pipeline supplies dyadic candidates, the
  kernel checks algebraic certificates (x² vs 2^2p for 1/√n; expLo/expHi
  Taylor with once-proven Lagrange remainders for ln; in-kernel Taylor after
  π-reduction for cos/sin). Fallback trigger defined (A0 data or week-3 2×
  overrun ⇒ 1-day girving port assessment for the native island only).
- **A2. Verified Euler–Maclaurin era** (10–15 aw, parallelizable): 7-theorem
  list, headliners `em_zeta_enclosure` (EM identity + remainder — ABSENT from
  Mathlib, upstreamable; 4–6 aw) and `stirling_binet_gammaR` (continuous-branch
  Im log Γℝ; 3–4 aw — serves BOTH the Γℝ edges and θ for A3). Key structural
  win: the `argChangeVert_eq_im_log_sub` FTC bridge converts 4 of the 5 edge
  quantities to POINT evaluations (only the two horizontal ζ-edges need
  Backlund cell subdivision). ζ at Re=2 via the prime-power log-series (cheap).
  Kill-to-descope: EM base case stalls ⇒ on-line-only reflection (discharge
  hLine only) — still a real trust shrink.
- **A3. Riemann–Siegel era** (12–20 aw, the research summit, no prior art in
  any assistant): θ via the A2 Stirling branch + the corpus's existing
  `theta_eq_argChangeVert_gammaR` bridge; RS main sum; MINIMAL-FIRST Gabcke
  C0-only remainder (|R| ≤ 0.053·t^{-3/4}, t ≥ 200). **CHARTER NOTE: A3 is on
  the critical path for the 10⁹ kernel-only milestone** — kernel-decide EM
  economics end at t≈10⁴ (quantified: ~4·10⁹ Int-ops/band at t=10⁵). Pivot
  ladder: Gabcke → explicit-constant AFE → (terminal) EM-era-only reflection.
- **A4. `checkBand` productionization** (2–3 aw): reflected bands prove the
  CONCLUSION outright (`ReflectedBand.Statement d`, no numeric hypotheses; the
  `band_t5shape` norm_num adapter emits the exact T5 conclusion Π-type so the
  height chain consumes reflected and T5 bands interchangeably). BandData =
  Int-mantissa literals, List folds, structural recursion only (no Rat, no
  WF-recursion, no ByteArray in the kernel island). `theorem ok : checkBand d
  = true := rfl` + once-proven `checkBand_correct`. Sibling flagged island
  `zeta_reflection_native/` shares everything above CheckBand for the
  native_decide era.
- New island: `telperion/examples/zeta_reflection/lean/` (requires
  zeta_zero_localization; same Mathlib pin).

### WS-B: Chain & architecture
- B1. Indexed-hypothesis segment/capstone redesign (due ~T=10⁵). [SCOUT: exact
      height_chain/segment lemma shapes]
- B2. Lake package sharding (one package per height block).
- B3. Reflected chain fold (single theorem over indexed family) — after A4.
- B4. hγ discharge audit (StripClear) → hypothesis-free capstones. [SCOUT]

### WS-C: Driver & scale-out
- C1. Platt multieval as PRIMARY line-sweep (grid sign boxes replace per-point
      Λ evals). [SCOUT: Z(t)↔Λ sign-box bridging]
- C2. Multi-node campaign runner: height-sharded state, journal, merge;
      compressed per-zero certificate format. [SCOUT: state-model constraints]
- C3. Width-policy ladder past 10¹² (1/(8·10⁶) top decade) + dlvpRateC margins.

### WS-D: The climb itself (compute, continuous)
- D1. Finish 10⁶ on current T5 (~9–12 h).
- D2. 10⁷ after B1 lands.
- D3. 10⁹ after A2+A4 (kernel-only decide, cluster weekend).
- D4. 10¹³ after A3 (native_decide policy per A4 gate + external compute).

### WS-E: Trust, audit, publication
- E1. Trust-base charter: axiom sets per milestone (3-axiom kernel-only through
      10⁹; +Lean.ofReduceBool beyond, with documented spot-check protocol).
- E2. verify-bands at scale; independent re-run protocol; data hashes.
- E3. Program whitepaper + PUBLICATION_LEDGER entries.

## Charter decisions (operator-confirmed 2026-09-12)

1. **Trust dial: HYBRID LADDER.** Kernel-only 3-axiom purity through 10⁹;
   `native_decide` permitted for the 10¹³ era with a documented kernel-only
   spot-check protocol (random band re-verification under pure `decide`).
2. **Compute: M3 Ultra now, cluster later.** Single-machine-correct with
   height-sharded multi-node support designed in from the start; procurement
   revisited when reflection is proven at 10⁹ scale.
3. **Sequencing: climb and build CONCURRENTLY.** The 10⁶ climb keeps rolling in
   this worktree; agents build WS-A/B/C in isolated worktrees.

## [SCOUT] findings

### Chain-scout (chain glue mechanics) — KEY CORRECTIONS
1. **B1 is codegen-only.** `all_nontrivial_zeros_in_segment_on_line` ALREADY takes
   the indexed form `hbands : ∀ i, i < n → (band-i conclusion)`; the per-band
   hypothesis scatter (134 binders at h36000, 92% of file bytes) is an artifact
   of the generated files, not the kernel lemma. Redesigned segment files take
   ONE `hbands` (+ per-segment stretched-box weakening functions bLo/bHi with a
   once-per-segment norm_num dispatch); `height_chain` is conclusion-level and
   needs NO change; downstream sees identical conclusions.
2. **No kernel binder ceiling found** — the h36000 file builds in seconds; the
   real bottleneck is source-file size (30–40K lines at 10⁶ under the current
   codegen). Bundling removes it entirely.
3. **hγ (55/16 height floor) is dischargeable TODAY**: StripClear discharges it
   at T=100 from two winding-0 box certificates
   (`height_floor_of_box_certs`); the same two-box glue discharges it at any
   capstone. E-track should produce hypothesis-free capstones per milestone.
4. Width edge confirmed: `zero_in_band` needs `a ≤ dlvpRateC / log T`, `100 ≤ T`.
5. The `line_toFinset_card` Part-A0 pattern (prove-once, instantiate-O(1)) is
   the house precedent for exactly this redesign.

### Numerics-scout (verified-numerics landscape)
1. **Toolchains**: islands on v4.32 (zeroloc) / v4.34-rc1 (li); guards enforce
   exactly [propext, Classical.choice, Quot.sound]; **no native_decide anywhere**
   (Mathlib's own linter deprecates it — downstream use is possible but the
   hybrid charter's 10¹³-era use must be an explicitly flagged, separate island).
2. **girving/interval**: active, MIT, Reservoir-registered, Lean v4.26.x —
   TOOLCHAIN GAP vs our v4.32 (port/bump risk to assess in a spike). Floating
   (64+64 software FP) + proven conservative rounding + exp/log/pow — the A1
   foundation candidate. Fallback: minimal in-house ℚ/dyadic interval core.
3. **NO Riemann–Siegel/Gabcke formalization exists in ANY assistant** (Isabelle
   zeta work stops short; PNT+ in Lean doesn't touch RS). A3 is first-of-kind.
4. **Kernel arithmetic**: GMP-backed Nat/Int reduction ~10⁹ ops/sec; Rat exact
   with GCD overhead. Mathlib has `Real.exp_bound'` (Taylor remainder) — the
   once-proven bridge lemmas for computable approximants have stdlib support.
5. **Correction to the scout's conclusion** (design clarification, kept here so
   the design agents don't inherit the error): reflection does NOT ask the
   kernel to reduce `Real.exp` (noncomputable). It defines COMPUTABLE ℚ/dyadic
   approximants (pure Rat arithmetic, kernel-reducible per (4)) plus
   once-proven `approx ≤ Real.f ≤ approx'` lemmas. Its two benefits: (i) SHRINK
   the trust boundary — today's edge/line enclosures are un-checked Arb inputs;
   reflected evaluation makes them kernel-checked; (ii) kill per-band
   ELABORATION cost (~5s today is elaboration, not kernel reduction) by making
   certificates data, not tactic scripts.
6. Platt–Trudgian 3·10¹² storage ≈ 16 TB — consistent with the 30–300 TB @10¹³
   certificate-mass estimate.

### Driver-scout (scale-out)
1. **THE HEADLINE: Platt–Trudgian's rigorous 3·10¹² run cost ~3.7 CORE-YEARS**
   (arXiv:2004.09765) ⇒ the 10¹³ driver campaign projects to **~12 core-years**
   — months on a modest cluster, 30× better than the prior conservative
   estimate. THE DRIVER IS NOT THE LONG POLE; the kernel/emission side is.
2. `acb_dirichlet_platt_multieval(res, T, A, B, h, J, K, sigma, prec)` +
   threaded variant confirmed in FLINT: uniform grid t_k = T − B/2 + k/A,
   N = A·B values of scaled Λ per call. Sign-box semantics identical to
   per-point `enclose_lambda` (positive scaling preserves signs) — same Arb
   trust class, no Lean-side change.
3. Multieval needs a UNIFORM grid — replace the adaptive sweep spacing with
   grid extraction; the Platt-hinted midpoint logic remains as the close-pair
   fallback.
4. Corrected storage arithmetic: ~44 B/zero raw (~10 B gzipped) ⇒ **~100–440 TB
   at 10¹³** — consistent with the irreducible Ω(N) analysis.
5. Multi-node model: append-only journal + per-band records, atomic
   write-temp-rename (campaign_state.json already works this way; needs only
   range-sharding + a merge tool).

## Concrete designs — WS-B and WS-C (main-session authored; code written today)

### B1 — Indexed segment/capstone codegen (unblocks ~T=10⁵; codegen-only)
Files: `telperion/examples/zeta_zero_localization/campaign.py`
(`emit_segment_file`), no kernel changes (chain-scout confirmed
`all_nontrivial_zeros_in_segment_on_line` already takes
`hbands : ∀ i, i < n → …`).
New generated shape per `AllZeros_h<B>.lean`:
- `bndSeg` (exists) + per-segment stretched-box functions `bLo bHi : ℕ → ℝ`
  with one lemma `hcover : ∀ i, i < K → bLo i ≤ bndSeg i ∧ bndSeg (i+1) ≤ bHi i`
  (K-case `interval_cases` + `norm_num`, once per segment file).
- Segment theorem takes ONE hypothesis
  `hbands : ∀ i, i < K → ∀ ρ, re-range → (bLo i ≤ im ∧ im ≤ bHi i) → ζρ=0 → re=1/2`
  and passes `fun i hi ρ hre him hz => hbands i hi ρ hre ⟨weaken via hcover⟩ hz`
  directly — NO per-band binders, NO interval_cases over bands.
- Capstone takes one `hbands_j` per PRIOR SEGMENT (~1 binder per 1000-height
  block: 1000 binders at 10⁶ — same growth as today per segment count, but
  ~30× fewer binders and ~50× smaller files; at 10⁶ the capstone is ~1000
  one-line binders ≈ manageable; the fully reflected fold (B3) removes even
  that later).
Migration: regenerate chain files h1000→current; band modules unchanged;
conclusions unchanged (downstream-safe per chain-scout §8).

### B2 — Lake package sharding (before ~2,500 modules)
One lake package per 25,000-height block (`zzl_block_NN/` with its own
lakefile + guard), depending on a shared `zzl_core` package (TuringBand,
RHInBox*, DiffractionCore, AllZerosUpToHeight...). `campaign.py` gains
`--block` routing for register/guard. Chain composes across packages via
conclusion-level `height_chain` (package-agnostic).

### C1 — Multieval-primary line sweep
`arb_platt.py`: add `platt_grid(T_center, A, B, prec) -> [(t_k, Λ-sign-box)]`
via `acb_dirichlet_platt_multieval` ctypes (threaded variant when free cores).
`generate.py`: `_online_sweep_zero_count_grid` consumes grid boxes; the
existing Platt-hinted midpoint sweep stays as close-pair fallback. Parity
gate: identical N on 3 already-certified bands before adoption.

### C2 — Multi-node campaign runner
`campaign.py`: `--shard LO:HI` (existing range args already do this) + a
`merge-state` subcommand (union of per-node `campaign_state.json`, conflict =
identical-record assert) + per-node worktrees. Per-zero compressed record
format (JSONL: zero_id, bracket lo/hi as dyadics, band_id; gzip per block)
written by the refinement pass — feeds both Bragg (B0) and the 10¹³ archive.

### C3 — Width ladder
`campaign.py WIDTH_DEN` becomes height-dependent: 4·10⁶ to T=10¹²,
8·10⁶ above; `haC` codegen already generalizes (log-bound exponent auto).

## Execution: the agent team

### Wave 1 (launches on approval; parallel, isolated worktrees)
| Agent | Mission | Deliverable |
|---|---|---|
| `spike-a0` | A0 kernel benchmark spike + DIntvDef draft (add/mul mem-soundness only) + statement-level elaboration check of the `argChangeVert_eq_im_log_sub` bridge | measured ops/s, Rat differential, literal-elaboration curve, axiom prints; foundation go/no-go memo |
| `chain-bundler` | B1 indexed segment/capstone codegen in campaign.py; regenerate h1000→current; full rebuild; guard + verify-bands | green build with ~50× smaller chain files, identical conclusions |
| `sweep-grid` | C1 multieval-primary sweep (`platt_grid` ctypes + `_online_sweep_zero_count_grid`); N-parity gate on 3 certified bands | faster sweep, parity-proven, close-pair fallback intact |
| main session | keep the climb rolling (legs 8+, T=36000→10⁵ era), integrate agent branches, run milestone verifications, commit REFLECTION_TRACK_DESIGN.md + this plan as PROGRAM_ANDURIL.md | continuous milestones on PR #506 |

### Wave 2 (gated on A0 data + Wave-1 merges)
`dintv-core` (A1 full correctness surface) ∥ `em-zeta` (theorem 1) ∥
`stirling-binet` (theorem 2) ∥ `bridge-lemmas` (theorems 3–7) ∥
`runner-shard` (C2 multi-node journal/merge + B2 lake sharding) ∥ climb to 10⁶
complete (G1) with hypothesis-free capstone via StripClear glue.

### Wave 3 (gated on A2 landing)
Reflected-band pilot at t≈100/10³ consumed by the chain (G2); EM-era reflected
re-verification to t≈10⁴ (G3); then the A3 RS/Gabcke campaign (the summit) →
10⁹ kernel-only (G4); A4 + native island + cluster procurement → 10¹³ (G5).

### Milestone gates
G0 A0 numbers → foundation confirmed · G1 10⁶ (current machinery) ·
G2 first reflected band in the chain · G3 reflected ≤10⁴ ·
G4 10⁹ kernel-only (needs A3) · G5 10¹³ (native island + cluster).

## Files to create/modify (Wave 1)
- NEW `telperion/examples/zeta_reflection/lean/` island: `Spike/DIntvMini.lean`,
  `Spike/Toy.lean`, `DIntvDef.lean` (+ lakefile, toolchain pin, guard stub).
- `telperion/examples/zeta_zero_localization/campaign.py`: B1 codegen
  (`emit_segment_file` indexed form + bLo/bHi/hcover), C1 grid sweep switch.
- `telperion/src/telperion/arb_platt.py`: `platt_grid(...)` multieval shim.
- `telperion/docs/REFLECTION_TRACK_DESIGN.md` + `telperion/docs/PROGRAM_ANDURIL.md`
  (this plan + the architect memo, committed for cross-session continuity).
- Reuse throughout: `TuringBand.lean` (BandStatement, turing_band_on_line),
  `AllZerosUpToHeight.lean` (indexed segment lemma — unchanged),
  `DiffractionCore.lean` (θ machinery, argChange defs), `StripClear.lean`
  (hγ discharge), `RHInBox.lean` Part A0 pattern, existing Arb pipeline as the
  untrusted candidate-producer.

## Verification
- **Every agent merge**: full island `lake build` green; `#print axioms` =
  exactly [propext, Classical.choice, Quot.sound] on all guarded anchors;
  `campaign.py verify-bands` sampled audit incl. negative control.
- **B1**: regenerated chain must yield BYTE-IDENTICAL capstone conclusion
  statements (diff the theorem signatures) + full rebuild + N(T) cross-check
  vs `zeta_nzeros` at the top height.
- **C1**: N-parity on ≥3 already-certified bands (grid sweep vs current) before
  the switch; refusal behavior preserved on a synthetic close-pair case.
- **A0**: profiler-separated elaboration vs kernel time; axiom print of the
  rfl pattern; numbers recorded in the design doc and re-basing the A2/A3
  height caps.
- **Milestones**: hypothesis-free capstone at each Gn via the StripClear
  two-box glue; N(T) exact cross-check; PR #506 milestone comments.
- **Honesty**: `conjecture1_proved = False` in every artifact; finite
  verification, not a proof of RH; native_decide use confined to the flagged
  sibling island with its own axiom guard printing the expanded set.
