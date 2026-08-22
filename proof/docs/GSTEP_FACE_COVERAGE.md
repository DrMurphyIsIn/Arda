# g-step face coverage: the `{ν*, ½, leaf}` maximizer, formalized in ℚ

**`conjecture1_proved = False`.** This documents the Lean face-decomposition of the g-step
(`GS(children) = base^11 · ∏ Bcap(μ_i) ≤ T`, tight only at the single arm), and states precisely
what is machine-checked vs. what remains. Synthesized 2026-08-22.

## The g-step and its maximizer

The R3 crux localizes to the **g-step**: over children with realizable subtree menus `μ_i`,
`GS = base^11 · ∏ Bcap(μ_i) ≤ T`, `base = (3(q+1)+3S+1)/(3q+3)`, `q =` #children, `S = Σμ_i`,
`T = W(5/3)^11`, `W = 64/621`, `Bcap(μ) = min(master_ub(μ), glemma(μ), 1)`.

Two empirical facts drive the decomposition (`verification`-level probes, exact ℚ):
1. **Only the single arm is tight.** `GS = T` exactly at one leaf (`q=1, μ=1`). *Every* multi-child
   config is slack (`{½,leaf}` maxes at `24.8`; best `ν*`-config `20.5`; `T = 28.407`).
2. **The extremal menus are `{ν*, ½, 1}`** — the 3-type maximizer support. `ν* ≈ 0.30774`
   (`glemma(ν*)=1`) is **irrational**, `½` and the leaf `1` are rational.

## What is machine-checked (Lean, `R3Cert/`)

| Face | Menus | Lean | Status |
|---|---|---|---|
| Homogeneous / pure-leaf (`a=0`) | `1^c` | `homog_master`, `GS_arm_le` | CI-green (`HomogMasterAssembled`) |
| `a=1` slice | `{½, 1^c}` | `ThreeTypeA1Slice.gs1_le_T` | CI-green |
| **2-type `{½, leaf}`** (all `a≥1`) | `{½^a, 1^c}` | `GStep2TypeFace.gs2_le_T` | **CI-green, on `main`** |
| **3-type `{ν*, ½, leaf}`** (all `a≥1`) | `{cap^b, ½^a, 1^c}` | `GStep3TypeFace.gs3_le_T` | **CI-green, on `main`** |

Every bound is exact `ℚ`, no `rpow`.

### The rational-enclosure device (kills the irrational `ν*`)

The cap-region children (`μ ≤ ν*`) have `Bcap = 1`, and raising a cap child's menu only raises
`base`; so over-bounding each by a **rational** `r = 31/100 ≥ ν*` over-estimates `GS` while
staying in `ℚ`. Enclosure validity `ν* ≤ r` is the single rational fact
`γ ≤ (331/300)^11` (`γ = W²(5/3)^11`, margin ≈ 0.022), proved by `norm_num`
(`GStep3TypeFace.nustar_enclosure`).

### The two reductions inside the bricks

- **2-type** (`gs2_le_T`): `base2` antitone in `c` (`U ≤ (58/51)V`, `64·(58/51)^11 ≤ 621`) drops
  any `(a,c)` to `(a,0)`; then antitone in `a` (`Ua ≤ (52/51)Va`, `Bcap(½)·(52/51)^11 ≤ 1`) drops
  to `(1,0)`; terminal `GS2(1,0) = (17/12)^11·Bcap(½) = 0.872·T ≤ T`. Both steps tight at `a=1`.
- **3-type** (`gs3_le_T`): `base3` antitone in the cap-count `b` — the cross-multiplied step reduces
  **exactly** to `D = 171a/100 + 621c/100 + 21/100 ≥ 0` (b cancels completely; `D = 9·[a(½−r)+
  c(1−r)+(⅓−r)]`, all coeffs `>0` since `r < ⅓`). So `GS3 b a c ≤ GS3 0 a c = GS2 a c ≤ T` for `a≥1`.

## Coverage: what these compose to

For configs whose menus lie in the 3-type support `{≤ν*, ½, 1}`:
- **`a ≥ 1`** (at least one ½-child): fully covered by `gs3_le_T` (any cap-count `b`, any `c`).
- **`a = 0`** (cap + leaf, no ½-child): `base3` b-antitone reduces to the pure-leaf face
  `GS2 0 c`, i.e. the **homogeneous** face. *Verified equal:* the homogeneous base at `μ=1`,
  `(6c+4)/(3(c+1))`, is exactly `base2(0,c) = (12c+8)/(6(c+1))`, so `GS2 0 c = GS c 1`, discharged by
  `GS_arm_le (c) : GS c 1 ≤ T` (`c≥1`, CI-green on `main` in
  `telperion/examples/g1_floors/lean/HomogMasterAssembled.lean`); `c=0` is `(4/3)^11 ≈ 23.6 < T`.
  This `a=0` corner is thus covered by the *existing* homogeneous brick, not re-proved here.

So `{ GS_arm_le (a=0 pure leaf) } ∪ { 3-type bricks (a≥1) }` covers the whole 3-type support — **modulo
the one open premise below.** (The formal *assembly* of these two into one statement needs the two lake
projects importable together — a separate scoped task, since `HomogMasterAssembled` and `R3Cert`
compile under different CI paths.)

## What remains (the honest gap)

The face bricks prove `GS ≤ T` *on each menu-type face*. They do **not** prove that the g-step
maximum is *attained* on the finite `{ν*, ½, 1}` support — that is **STEP 1**, the heterogeneous
achievability / reduction: that arbitrary realizable menus collapse (below-average lemma +
sum-preserving bang-bang) to the 3-type support. STEP 1 is the genuinely open crux (Gap 1 in
`PROOF_STATE_AND_PLAN.md`) — real new arithmetic, no mechanical path, and it is what keeps
`conjecture1_proved = False`. The face coverage documented here is the *downstream* half: once
STEP 1 lands, these bricks discharge the `≤ T` obligation on the reduced support without any
irrational-analysis debt.

## Provenance

- Bricks merged to `main` via PR #58 (squash `1978d25d`), Lean `lean-verify` CI-green.
- `a=1` slice: branch `feat/gstep-3type-a1` (green; superseded by `gs2_le_T`, kept for the record).
