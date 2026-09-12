# A0 kernel-throughput spike — report

*PROGRAM ANDÚRIL WS-A. Author: spike-a0 agent. Date: 2026-09-12.*
*conjecture1_proved = False (this is a benchmark, not a proof of RH).*

## TL;DR verdict — **YELLOW, leaning to a native-decide plan for the deep era**

- Measured pure-kernel interval throughput: **~1.0–1.9·10⁴ interval-ops/s** on this M3 Ultra
  (1000 points, ~15 Int ops/point, kernel typecheck 0.80–1.54 s). Per the plan thresholds
  (green ≥3·10⁵; yellow 3·10⁴–3·10⁵; **red <3·10⁴**) the *raw* number lands in the **RED**
  band. But three qualifiers pull the practical verdict up to **YELLOW**, see below.
- **DIntv foundation is CONFIRMED, and the fallback (a Rat/ℚ interval core) is
  categorically REFUTED**: `Rat` arithmetic does **not** reduce in the Lean kernel at all —
  neither `rfl` nor `decide` — so the "GCD tax" is not a slowdown, it is an infinite wall.
  Pure-`Int` `DIntv` is the *only* kernel-reflectable option. This is the single most
  decision-relevant finding.
- The dominant end-to-end cost today is **not kernel typechecking — it is ELABORATION**
  (typeclass inference 30–68 s for a 1000-tuple `List` literal). This is exactly the cost
  the reflection track exists to kill (certificates as *data*, not tactic scripts), and it is
  *addressable*: switching the literal container from `List (Int × Int)` to `Array Int`
  removed the typeclass blowup entirely.

The RED raw kernel number means: **kernel-only `decide` is viable for the EM era (≤~10⁴) but
does not by itself reach 10⁹**; the hybrid-ladder charter (kernel-only through a mid height,
`native_decide` for the deep era) is the right call and A0 does not overturn it. See the
re-based height caps below.

## What was built (new island `telperion/examples/zeta_reflection/lean/`)

Shares the sibling `zeta_zero_localization` Mathlib pin exactly
(`rev = 81a5d257c8e410db227a6665ed08f64fea08e997`, toolchain `v4.32.0`); `lake update`
pulled the shared cache with **no files to download**. Full island `lake build` is **green**
(3002 jobs). Path-requires `LambdaLineReal` (→ transitively `ZeroFreeBridge`) for the bridge
elaboration check.

| File | Role |
|---|---|
| `Spike/DIntvMini.lean` | Minimal computable dyadic-interval core (`add`/`mul`/`neg`/`roundTo`/`sign?`), pure Int, structural, no proofs. Kernel hot-path target. Builds. |
| `Spike/Toy.lean` (gen) | `checkAlt : List (Int×Int) → Bool` over `p(x)=x²−2` at 1000 dyadic points straddling √2; `toy_ok : checkAlt pts = true := rfl`. |
| `Spike/ToyDecide.lean` (gen) | Same, `by decide` — wrapper overhead. |
| `Spike/ToyRat.lean` (gen) | Same checker over `Rat` — GCD-tax differential. **See finding: does not reduce.** |
| `Spike/ToyLit.lean` (gen) | 20k Int literals in an `Array` + trivial fold — big-literal elaboration isolation. |
| `Spike/ToyLoP.lean` (gen) | Low-precision (e=−24) DIntv variant — kernel-time-vs-mantissa-width control. |
| `DIntvDef.lean` | Production-intended `DIntv` + **`add_sound` and `mul_sound` fully proven, no sorry** (Real mem-soundness; validates the bridging proof style). |
| `LogBranchesStub.lean` | `argChangeVert_eq_im_log_sub` stated as a `Prop`-valued `def` (no proof) — **elaborates against the real `DiffractionCore.argChangeVert`**. |
| `AxiomGuardSpike.lean` | `#print axioms` on the anchors (not a `lean_lib`; run explicitly). |
| `../gen_spike.py` | Emits Toy/ToyDecide/ToyRat/ToyLit; verifies sign alternation in exact rationals before emit. |

## Measured numbers (profiler-separated; M3 Ultra, under concurrent 10⁶ campaign load)

Command: `time env LEAN_ABORT_ON_PANIC=1 lake env lean -Dprofiler=true Spike/<file>.lean`,
`set_option maxHeartbeats 0` in every file. **Note:** the box was simultaneously running the
live 10⁶ Turing campaign, so the elaboration/typeclass numbers carry high variance and should
be read as order-of-magnitude, not precise.

| Variant | Kernel `type checking` | Elaboration | Typeclass inference | Verdict-relevant reading |
|---|---|---|---|---|
| `Toy` (rfl, DIntv, 1000 pt, 128-bit) | **0.80 s** | 6.0 s | 30.9 s | ~1.9·10⁴ interval-ops/s |
| `ToyLoP` (rfl, DIntv, 1000 pt, 24-bit) | **1.54 s** (noisy) | 12.6 s | 68 s | ~1.0·10⁴; **kernel time NOT ∝ mantissa width** |
| `ToyDecide` (decide, 1000 pt) | 1.24 s (+ decide tactic 2.17 s) | 8.6 s | 55.7 s | decide ≈ 1.5–3× rfl kernel cost |
| `ToyRat` (rfl) | — | — | — | **FAILS: `rfl` does not reduce Rat** |
| `ToyRat` (decide) | — | — | — | **FAILS: stuck at `Rat.instDecidableLt`** |
| `ToyLit` (20k `Array Int`, decide) | (fast) | **7.1 s** | (no blowup) | ~3.5·10⁻⁴ s/literal, no typeclass tax |
| `ToyLit` (100k `List (Int×Int)`) | 0.52 s (partial) | 51.8 s | 13.3 s | **maxRecDepth blowup — List literals don't scale** |

### Throughput (the headline metric)
~15 Int interval-ops/point × 1000 points ÷ 0.80–1.54 s kernel = **~1.0·10⁴ – 1.9·10⁴
interval-ops/s**. Below the 3·10⁴ red line. Because kernel time was ~constant across 24-bit
and 128-bit mantissas, the cost is dominated by the **number of reduction steps** (list
traversal + `min`/`max`/`Int.decLt` structure), not GMP bignum width — so higher production
precision will *not* proportionally worsen it, but the per-point step count is the floor.

### Rat/dyadic ratio
**Undefined / infinite.** `Rat` is not kernel-reflectable by either `rfl` or `decide`
(`Rat` carries a reduced-fraction invariant; its mul/lt normalize via `Nat.gcd`, which the
kernel refuses to unfold — the `decide` error literally reports "reduction got stuck at the
`Decidable` instance … `Rat.instDecidableLt`"). This *confirms the plan's choice of a
pure-Int DIntv core and refutes any Rat/ℚ fallback.*

### Elaboration-per-literal curve
`List (Int × Int)` literals trigger per-element typeclass search → the 30–68 s typeclass
inference that dominates wall time and the `maxRecDepth` wall at 100k. Switching to an
`Array Int` literal removed the typeclass blowup entirely (20k in 7.1 s, ~355 µs/lit).
**Design consequence for A4: BandData literals must be `Array`-shaped (or chunked), never a
deep `List` of tuples.**

## Axiom prints (`lake env lean AxiomGuardSpike.lean`)
```
'Spike.toy_ok'                    depends on axioms: [propext]
'DIntvProd.DIntv.add_sound'       depends on axioms: [propext, Classical.choice, Quot.sound]
'DIntvProd.DIntv.mul_sound'       depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx`, no `ofReduceBool`. `toy_ok` (the pure-Int `rfl`) needs only `propext` — cleaner
than the 3-axiom target. The soundness proofs hit exactly the expected
`{propext, Classical.choice, Quot.sound}`. The island does not disturb the existing
`zeta_zero_localization` guard (separate directory, only-new-files, no shared modules edited).

## Foundation decision memo
- **DIntv (pure-Int dyadic) CONFIRMED** as the A1 foundation. Reasons: (1) it is the only
  kernel-reflectable arithmetic — Rat is out; (2) `add_sound`/`mul_sound` proved cleanly, so
  the Real-bridging proof style scales; (3) kernel time is dominated by reduction-step count,
  not bignum width, so 128-bit+ precision is affordable per-op.
- **Fallback NOT triggered by data** (a girving/interval or Rat port). Rat is refuted;
  girving/interval targets v4.26 UInt64 FP whose kernel-whnf behaviour is untested here and
  offers no advantage over Int given the reduction-step-count bottleneck. Keep the girving
  assessment only as the week-3-overrun trigger for the *native* island, not for kernel work.
- **Practical throughput lever = fewer reduction steps, not smaller mantissas.** A4 should
  minimize per-point kernel structure (flatten `min`/`max` chains; `Array` folds; avoid `Option`
  in the hot loop) and rely on `native_decide` for the deep era per the hybrid charter.

## Re-based height caps (plan formula: ~t·log t Int-ops/band, anchored ~4·10⁷ at t=10³)
Kernel-only `decide` budget: assume a tolerable ~10 s kernel-typecheck per band. At the
measured **~1.5·10⁴ Int-ops/s**, that is **~1.5·10⁵ Int-ops/band** of kernel budget.

| Height t | Est. Int-ops/band (~t·log t, plan scaling) | vs ~1.5·10⁵ kernel-only budget |
|---|---|---|
| 10³ | ~4·10⁷ (plan anchor) | already 260× over a 10 s kernel-only band → **kernel-only decide is impractical even at 10³ for a full RvM band**; today's per-literal `norm_num` bands work because they are *emitted certificates*, not in-kernel evaluation |
| 10⁴ | ~5·10⁸ | far past kernel-only |
| 10⁵ | ~4·10⁹ (plan's own EM figure) | native-only |
| 10⁹ | — | native_decide + cluster (charter G4/G5) |

**Interpretation:** the raw kernel throughput is too low for *in-kernel evaluation of a full
band* at any campaign height; the reflection win is therefore **elaboration-cost removal**
(certificates as `Array` data checked by a once-proven `checkBand`, discharged by
`native_decide` for anything past the smallest heights), plus the **trust-shrink** of making
today's un-checked Arb edge inputs kernel-checked. This *matches* the numerics-scout's design
clarification and the hybrid-ladder charter: kernel-only `decide` is a *purity spot-check*
mechanism (random small bands), not the production discharge path beyond ~t=10³. **The 10⁹
kernel-only milestone (G4) as literally "pure `decide`" is not supported by these numbers**;
G4 should be read as "kernel-only-*spot-checkable*", with `native_decide` doing the bulk even
below 10⁹. This is the one place A0 data tightens the plan.

## v4.32 API surprises
- `Rat` non-reducibility (above) — the load-bearing surprise.
- `maxRecDepth` must be set very high (≥10⁵) for 1000-deep `List` recursion; 100k-deep `List`
  literals blow it regardless → use `Array`.
- `Mathlib.Algebra.Order.Ring.Lemmas` does not exist at this rev (used `Mathlib.Tactic`).
- Lemma directions that bit: `mul_le_mul_of_nonpos_left : b ≤ c → a ≤ 0 → a*c ≤ a*b` (flips),
  `div_mul_cancel₀ _ (ne_of_gt h)` for the `x = (x/p)*p` rewrite (not `field_simp` on a
  let-bound denominator). All resolved; `DIntvDef` is sorry-free and green.

## Handoffs
- **A1 (`dintv-core`)**: build on `DIntvDef.lean`'s proven `add_sound`/`mul_sound`; extend to
  `neg`/`sub`/`roundTo` soundness (roundTo is a monotone one-liner off add/mul) and the
  verify-not-compute transcendental certificates. Keep everything pure-Int.
- **A2 (`bridge-lemmas`)**: `LogBranchesStub.argChangeVert_eq_im_log_sub` is the exact,
  type-checked target — restate as a theorem and prove (FTC / `intervalIntegral.integral_deriv`).
- **A4 (`checkBand`)**: BandData must be `Array`-shaped; budget `native_decide` for discharge;
  reserve pure `decide` for the small-band purity spot-check protocol (E-track).
