# BG additive-SUBACTION: d=4 profiles, the deg≥5 tail, and the 27·23 tie — spec (2026-09-03)

Continues `BG_SUBACTION_TELPERION_NEXTCELLS.md` after the **degree-3 family completed** (commit `378186e`,
`R3Cert/BGSCLSubactionDeg3Mid.lean`). Covers the three remaining pieces of `IsSubaction ρwit`:
**(A) d=4 mixed profiles**, **(B) the deg≥5 tail**, **(C) the 27·23 tie identity**. All numerics verified against
`F* = log(621/64)/11`, `ρwit(leaf)=F*, ρwit(2,μ)=2F*−log(3/2)+(μ−1/3)/4, ρwit(3,μ)=μ/32, ρwit(4,μ)=μ/384, ρwit(≥5)=0`.
`conjecture1_proved = False`.

> **Stale-table correction.** The existing `subaction_cell_broom_d4` / `subaction_cell_d4_d3` /
> `log54_sub_fstar_le` / `ρ3` in `BGSCLSubaction.lean` were built for a **superseded** witness
> (`ρ3(μ)=(μ−1/5)/8`, `ρ(broom)=0`) that FAILS the high-degree tail (see the NOTE at `BGSCLSubaction.lean:159`).
> They are true isolated inequalities but are **NOT cells of `ρwit`**. The d=4 family below is for the corrected
> `ρwit` (deg-4 node ρ = `bY/384`) and is genuinely open.

---

## Part A — d=4 mixed profiles: PATTERNED, ready to emit (all TANGENT route)

A d=4 hub has 3 children; `ρwit(node) = bY(node)/384`, `bY(node) = 1/(4+S)`, `S = Σ bY(child_i)`.
All **35 profiles** (multisets of child degrees from {leaf, 2, 3, 4, ≥5}) are TRUE, and — unlike cell (D) —
**each closes with a single `log_tangent` at its binding corner** (no two-slope wall, because every d=4 profile's
binding corner puts all children at a common message, so one tangent point is exact there and slack ≥0 at the
other corners; verified over all 8 corners × all 35 profiles).

### Recipe (per profile, mirror the deg-3 cells)
For a profile with children of types `t1,t2,t3`:
1. Bound each child message to its range: leaf `=1`; deg-2 `∈[1/3,1/2]`; deg-3 `∈[0,1/3]`; deg-4 `∈[0,1/4]`; deg≥5 `∈[0,1/5]`.
2. `log_tangent (d:=4) (s:=S) (s0:=S_bind)` where `S_bind` = the binding-corner message sum (table below), giving
   `log(1+S/4) ≤ log((4+S_bind)/4) + (S−S_bind)/(4+S_bind)`.
3. Node-ρ: `ρwit(node) ≤ 1/(384·(4+S_min))` (`S_min` = children at min message).
4. Per-child ρ: deg-2 EQUALITY `2F*−log(3/2)+(μ−1/3)/4`; deg-3 `=μ/32`; deg-4 `=μ/384`; deg≥5 drop (`≥0`); leaf `=F*`.
5. The **atom** (single-log enclosure, table below). Then `linarith [message bounds]` — the post-tangent goal is
   **linear** in the messages, so `linarith` closes it over the whole box (no per-corner case split needed).

### The 35 atoms (all verified; route = tangent unless noted). Format `log(A) + kL·log(3/2) − kF·F* ≤ bound`:

| profile | atom |
|---|---|
| (leaf,leaf,leaf) | `log(7/4) − 4F* ≤ −1/2688` |
| (2,leaf,leaf) | `log(19/12) − log(3/2) − 5F* ≤ −1/2432` |
| (2,2,leaf) | `log(17/12) − 2log(3/2) − 6F* ≤ −1/2176` |
| (2,2,2) | `log(5/4) − 3log(3/2) − 7F* ≤ −1/1920` |
| (2,2,3) | `log(5/4) − 2log(3/2) − 5F* ≤ 53/5376` |
| (2,2,4) | `log(59/48) − 2log(3/2) − 5F* ≤ 1/10752` |
| (2,2,5) | `log(73/60) − 2log(3/2) − 5F* ≤ −1/1792` |
| (2,3,leaf) | `log(17/12) − log(3/2) − 4F* ≤ 61/6144` |
| (2,3,3) | `log(5/4) − log(3/2) − 3F* ≤ 101/4992` |
| (2,3,4) | `log(59/48) − log(3/2) − 3F* ≤ 209/19968` |
| (2,3,5) | `log(73/60) − log(3/2) − 3F* ≤ 49/4992` |
| (2,4,leaf) | `log(67/48) − log(3/2) − 4F* ≤ 1/6144` |
| (2,4,4) | `log(29/24) − log(3/2) − 3F* ≤ 7/9984` |
| (2,4,5) | `log(287/240) − log(3/2) − 3F* ≤ 1/19968` |
| (2,5,leaf) | `log(83/60) − log(3/2) − 4F* ≤ −1/2048` |
| (2,5,5) | `log(71/60) − log(3/2) − 3F* ≤ −1/1664` |
| (3,leaf,leaf) | `log(19/12) − 3F* ≤ 23/2304` |
| (3,3,leaf) | `log(17/12) − 2F* ≤ 13/640` |
| (3,3,3) | `log(5/4) − F* ≤ 47/1536` |
| (3,3,4) | `log(59/48) − F* ≤ 1/48` |
| (3,3,5) | `log(73/60) − F* ≤ 31/1536` |
| (3,4,leaf) | `log(67/48) − 2F* ≤ 27/2560` |
| (3,4,4) | `log(29/24) − F* ≤ 17/1536` |
| (3,4,5) | `log(287/240) − F* ≤ 1/96` |
| (3,5,leaf) | `log(83/60) − 2F* ≤ 19/1920` |
| (3,5,5) | `log(71/60) − F* ≤ 5/512` |
| (4,leaf,leaf) | `log(25/16) − 3F* ≤ 1/4608` |
| (4,4,leaf) | `log(11/8) − 2F* ≤ 1/1280` |
| (4,4,4) | `log(19/16) − F* ≤ 1/768` |
| (4,4,5) | `log(47/40) − F* ≤ 1/1536` |
| (4,5,leaf) | `log(109/80) − 2F* ≤ 1/7680` |
| (4,5,5) | `log(93/80) − F* ≤ 0`  (MONOTONE — bound is exactly 0) |
| (5,leaf,leaf) | `log(31/20) − 3F* ≤ −1/2304` |
| (5,5,leaf) | `log(27/20) − 2F* ≤ −1/1920` |
| (5,5,5) | `log(23/20) − F* ≤ −1/1536` |

Every atom's fold `X = A^11 · (3/2)^(11·kL) · (621/64)^(−kF)` satisfies `X−1 ≤ 11·bound` ⇒ **tangent route**
(`Real.log_le_sub_one_of_pos`), the cheapest — `norm_num` discharges the rational `X−1 ≤ 11·bound`. The one exception
`(4,5,5)` has bound 0 ⇒ **monotone**. **None need tight_hi** (unlike deg-3's `deg3_deg2children_enc` / cell-(D)'s
`log2_sub3fstar`). Hand this table to Telperion as 35 `emit_log_combination` calls; auto-route will pick tangent/monotone.

---

## Part B — the deg≥5 tail: THE ONE GENUINELY-OPEN PIECE (needs a uniform-in-d lemma)

A deg-`d` hub (`d≥5`) has `k=d−1` children and `ρwit(node)=0`, so `(SUB)` is
`log(1+S/d) − F* ≤ Σ_i ρwit(child_i)`, `S = Σ bY(child_i)`.

### The naive "Σρ ≥ |leaf children|·F*" design is WRONG
It fails whenever there are no leaves: e.g. **four deg-3 children** (d=5, all `bY=1/3`) has `e_node = log(19/15)−F* ≈
+0.030 > 0` but `|leaves|·F* = 0`. The message-carried ρ of the non-leaf children is **essential** and cannot be
dropped (drop-the-child, the cell-(D) escape, does NOT apply here — the deg-3 children push `S` up *and* their ρ is
needed). This is why the tail is not a uniform `≤0` collapse and not a deg-3/d=4-style patterned emit.

### Empirical map (exhaustive over compositions, d=5..14; uniform-type sampled to d=199)
- The **worst profile at each d is uniform-type**: all-deg-2 for `d ≤ 9`, all-deg-4 for `d ≥ 10`.
- Per-type minimum margin over d: **all-deg-2 → 0 (at d=6, the tie)**; all-deg-3 → +0.0119 (d=5); **all-deg-4 → +0.0057
  (d=18)**; all-deg-5 → +0.025 (d→large). Margins are tiny but strictly positive except the d=6 tie.
- A single `log_tangent` at the binding S closes each *individual* d — but the crude `log(1+x)≤x` bound (s0=0) does
  **not** close until `d ≈ 62` (deg-4 children have `ρ/bY = 1/384`, so per-child `bY/d ≤ ρ` needs `d ≥ 384`; only
  log-concavity saves it below that). So "finite cells up to D0 + crude tail" is impractical (`D0 ≈ 62`).

### Recommended proof design (the actionable path)
Two obligations:

1. **Reduce-to-uniform** (`tail_worst_is_uniform`): for fixed d, the SUB-slack `Σρ_i − (log(1+S/d)−F*)` is minimised
   at a uniform-type profile (all children the same degree, at the binding message). Exchange/convexity argument:
   each child's `(bY_i/(d+s0)) − ρ(child_i)` contribution is convex, so an extremal profile is uniform. Discharges the
   combinatorial explosion (arbitrary d−1-child mixes) down to 4 one-parameter families.

2. **Three per-type d-families** (the real content — each a `d`-indexed enclosure, tie/min at the noted d):
   - `tail_all_deg2`: `log((4d−1)/(3d)) ≤ (2d−1)·F* − (d−1)·log(3/2)`   (`bY=1/3`, `S=(d−1)/3`; **equality at d=6**).
   - `tail_all_deg3`: `log((4d−1)/(3d)) − F* ≤ (d−1)/96`                  (`bY=1/3`; min slack +0.0119 at d=5).
   - `tail_all_deg4`: `log((5d−1)/(4d)) − F* ≤ (d−1)/1536`               (`bY=1/4`, `S=(d−1)/4`; **crux, min +0.0057 at d=18**).
   - (all-deg-5 / leaves: `e_node < 0` or ρ dominates — a crude `log(1+x)≤x` closes them; no family needed.)

   Each family has slack that is **convex in d with a single interior minimum** (d=6 / d=5 / d=18). Prove by: verify the
   finite window around the minimum (a handful of explicit d), then a monotone tail `d ≥ D_t` via `log(1+x) ≤ x −
   x²/2 + x³/3` (`x∈[0,1]`) — the degree-3 log upper bound keeps enough concavity that `Σρ` (linear in d) dominates
   for large d. The **all-deg-4 family is the crux**: min margin +0.0057 at d=18, tie-adjacent, and `ρ=bY/384` is the
   flattest — this is where a naive bound dies and the cubic-log correction is required.

**Status: this is the remaining research.** It is NOT a Telperion emit (no finite atom list); it is a BG-side
uniform induction/monotonicity proof. The empirics (worst=uniform, exact d=6 tie, convex-in-d slack) de-risk it, but
the `tail_all_deg4` d-family + the reduce-to-uniform exchange lemma are genuinely new proof obligations.

---

## Part C — the 27·23 = 621 tie identity

The witness is calibrated so `(SUB)` holds with **exact equality** (margin 0) at the tie configurations — these are
where `621 = 27·23` appears and the ceiling is sharp. Two exact-equality cells (verified margin `0` to machine ε):

1. **`subaction_cherry`** (already proven) — d=2 hub, one leaf child. `bY(node)=1/3`, `ρwit(node)=2F*−log(3/2)`, and
   `(log(3/2)−F*) + (2F*−log(3/2)) = F* = ρwit(leaf)`. The **degree-2 face** of the tie (`F* ≤ F*`).
2. **`subaction_tail_tie_d6`** (open) — d=6 hub, five deg-2 children each at `bY=1/3`. `S=5/3`,
   `e_node = log((4·6−1)/(3·6))−F* = log(23/18)−F*`, `Σρ = 5·(2F*−log(3/2))`, and
   `log(23/18) − F* = 5·(2F*−log(3/2))` **exactly** ⟺ `log(23/18) + 5·log(3/2) = 11·F* = log(621/64)`
   ⟺ `(23/18)·(3/2)^5 = 621/64` ⟺ `23·243 / (18·32) = 621/64` ⟺ `5589/576 = 621/64` ✓ (both `= 9.703125`).
   This is the `27·23` identity in the tail: `23·3^5 = 23·243 = 5589` and `621·9 = 5589`, i.e. `621 = 27·23` with the
   `3^5/18 = 27/... ` bookkeeping. It is an **exact `norm_num` identity once F* is unfolded** (`11·F* = log(621/64)`,
   `log((23/18)·(3/2)^5) = log(621/64)`), NOT an enclosure — the cleanest cell in the family.

The tie also lives at the boundary of the deg-2 tail family (`tail_all_deg2` above is tight exactly at d=6), so proving
`tail_all_deg2` subsumes `subaction_tail_tie_d6`.

---

## Handoff summary
- **d=4 (Part A):** ready now — 35 tangent/monotone atoms tabulated; emit + assemble exactly like the deg-3 leaf cells.
- **tie (Part C):** ready now — `subaction_tail_tie_d6` is an exact `norm_num` log-identity (`(23/18)(3/2)^5=621/64`).
- **deg≥5 tail (Part B):** the one open research piece — reduce-to-uniform + three per-type d-families (deg-4 the crux);
  a BG-side uniform induction, not a Telperion emit.
