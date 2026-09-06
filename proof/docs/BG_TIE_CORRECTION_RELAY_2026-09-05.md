# Relay to the BG extremality lane: the tie target is the BROADENED family, not the near-star (2026-09-05)

Complement to `BG_SESSION_RELAY_2026-09-05.md`. This lane (`bg/conjecture1-attack`) worked the
`SharpRateNF`/tie side and reached a result that **corrects the tie target** the Hdom layer must
dominate toward. All exact, verified by three independent engines (a3_derisk cavity, `pi_loaded`,
literal matching-permanent). `conjecture1_proved = False`.

## 1. The near-star is NOT the finite-n maximizer (so it is the wrong `tie`)

`nearStarTie K` (value `(26/23)/rhoB·rhoB^(1+11K)`) is only the **asymptotic / large-K** maximizer.
At aligned size `n=1+11K` the size-preserving trade **load-5 arm (11 vtx) ⟷ load-4 arm (9) + cherry
(2)** strictly increases `Aobj` for small K. The maximizer is a single hub with `(K−m)` load-5 arms
+ `m` load-4 arms + `m` cherries; the near-star (`m=0`) is optimal **iff K ≥ 23**. Witness: K=5/n=56,
broadened `10754162441504397/104857600000` beats near-star `52200362289231/536870912` by **5.48%**.

⇒ `SharpRateNF`/`conjecture1_of_layers_fixedN` instantiated with the **near-star** tie is **FALSE for
K<23** (this is exactly why the `hrate` bound `(26/23)/rhoB·rhoB^n` is violated — it is only the
large-n limit). See `proof/verification/{sharprate_nearstar_gap,broadened_tie_family}.py`.

## 2. Closed-form tie value (aligned sizes)

`tie(1+11K) = max_m V(K,m)`, `V(K,m) = (621/64)^(K−m)·(513/80)^m·(3/2)^m·(1 + qSum/(K+m))`,
`qSum = (K−m)·3/23 + m·3/19 + m·1/3`. Per-child cavity data: load-5 arm `(621/64, 3/23)`, load-4 arm
`(513/80, 3/19)`, cherry `(3/2, 1/3)`. For non-aligned `n` the maximizer is the same shape with the
size remainder absorbed by load-4/6 arms + cherries (single-hub throughout; the ratio decreases
monotonically to `(26/23)/rhoB` as `n→∞`).

## 3. This makes your Hdom "multi-hub extremality" the EASY direction

Against the **corrected** (broadened, higher) tie, the multi-hub merge-normal states you flagged are
dominated with a large margin — verified:

| merge-normal 2-hub state | n | ratio | broadened-tie ratio | margin |
|---|---|---|---|---|
| two all-4-arm hubs | 92 | 0.857 | 0.949 | **10.8%** |
| 5×load5 ∥ 5×load4 hubs | 102 | 0.844 | 0.944 | **11.8%** |
| two 6×load4 hubs | 110 | 0.856 | 0.941 | **10.0%** |
| two (5,4,4,4,4) hubs | 96 | 0.852 | 0.945 | **11.0%** |

So multi-hub merge-normal states are ~0.85 while the tie is ~0.94: Hdom's multi-hub case holds with
margin **once the tie is the broadened family**. The load-bearing content is therefore the
**single-hub** side — proving the broadened single-hub family is the maximizer and no single-hub
merge-normal state exceeds it.

## 4. Honest scope

RIGOROUS: near-star non-maximal for K<23 (explicit witness trees, exact); `V(K,m)` closed form;
the 4 tabulated multi-hub states dominated. EMPIRICAL: the `(K−m,m,m)` family is the maximizer within
the searched single-hub building blocks (arm-loads {2..6} + cherries) and beats every multi-hub config
tried; a fully rigorous global-maximizer proof and the non-aligned-`n` remainder formula are the open
steps. These define the corrected `tie : ℕ → UTree` the capstone needs. Artifacts + memory on
`bg/conjecture1-attack`. Available to certify any finite family you isolate. `conjecture1_proved = False`.
