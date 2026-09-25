# L1: `StructProp 492` for the spider family (2026-09-25)

Lean: `proof/formalization/R3Cert/BGSpiderStruct.lean`, theorem `R3Cert.BGSpiderStruct.structProp_492`
(axioms: propext, Classical.choice, Quot.sound; no `sorry`, no `native_decide`).
Exact check: `proof/verification/bg_spider_struct_check.py`.

Claim: every F-maximizer `l` of the two-level spider family (model of `BGSpiderOpt`) with `nv l >= 492`
satisfies `Cand l`: at most 8 cherries, every arm in {4,5,6}, not both 4 and 6, at most 10 fours and at most
10 sixes. This is about one explicit family only. `conjecture1_proved = False`.

## Tools

**Local exchange** (`F_exchange_lt`, `not_isMax_of_exch`, `count_lt_of_exch`). Take `l ~ old ++ rest` and
replace `old` by `new` with the same total cost. The product over `rest` cancels. With D0 = |rest|,
R0 = sum of r over rest, and a rational bound gamma' <= G(new)/G(old), the move strictly raises F when

    (|old| + D0 + R_old + R0)(|new| + D0)  <  gamma' (|new| + D0 + R_new + R0)(|old| + D0).

This is affine in R0, so it is enough to check the two ends of the allowed R0 range. Both ends are
quadratics in D0, and each one is certified positive (checked in exact arithmetic by the script, then
proved by `nlinarith` in Lean).

| exchange | gamma (exact) | gamma' used | region needed | exact minimal D0 |
|---|---|---|---|---|
| 11 A_j -> (2j+1) A_5, j = 1,2,3,7..12 | 1.94, 1.26, 1.075, 1.052 .. 1.40 | 3-digit floor | D0 >= 0, 0 <= R0 <= D0 | 0 |
| 11 A_6 -> 13 A_5 | 1.01681 | 1271/1250 | D0 >= 0, 0 <= R0 <= D0/3 | 0 |
| 11 A_4 -> 9 A_5 | 1.01135 | 10113/10000 | D0 >= 27, D0/9 <= R0 <= D0 | 15 |
| 9 P -> 2 A_4 | 1.06963 | 1069/1000 | D0 >= 27, D0/9 <= R0 <= D0 | 16 |
| A_{u+13} -> A_{u+2} + 2 A_5 (split), all u | (529/486) a_{u+2}/a_{u+13} | exact | D0 >= 0, 0 <= R0 <= D0/3 | 0 |

For the split, the cleared-denominator difference is `Dd = D0(u,X) + Y D1(u,X)` with u = k-2 >= 0,
X = D0, Y = R0. `D0(u,X)` has only positive coefficients. The value at Y = X/3 is positive because it is a
positive-coefficient part plus u times a definite quadratic plus a definite quadratic. The identity
`X Dd = (X-3Y) D0 + 3Y E` then closes the proof (`exch_split_lt`).

**Global comparison with the rule winner** (`global_contra`). Put h(P) = 1 and h(A_j) = (2/3) alpha_j^2.
Then `(prod g)^2 = (3/2)^(n-1) prod h`, so

    F(l)^2 <= (1+hi)^2 (3/2)^(n-1) K^(#arms)      if every r <= hi and every arm has h <= K,
    F(W n)^2 >= (10/9)^2 (3/2)^(n-1) (529/486)^37 (W's arms have r >= 1/9; h(A_4), h(A_6) >= 1; w5 >= 37).

Here `w5 n >= 37` for n >= 492, because w4 <= 10 and w6 <= 4 and they are never both non-zero.

## Steps (for an F-maximizer l with nv l >= 492)

1. `three_le_length`: |l| >= 3. Otherwise use the global comparison with hi = 1, K = 32/27, #arms <= 2:
   4 (32/27)^2 = 5.62 < 28.43.
2. `arm_le_twelve`: no A_j with j >= 13. Balance (|l| >= 3) puts every other arm at size >= 12, so every
   r <= 1/3, and then the split wins.
3. `arm_le_six`: no A_j with 7 <= j <= 12. Balance gives arms >= 6, so r <= 1/3. The exchanges
   11 A_k -> (2k+1) A_5 (k = 6..12) cap every size at 10, and balance leaves at most two adjacent sizes,
   so #arms <= 20. Global comparison with hi = 1/3, K = h(A_12) = 578/507:
   (16/9) K^20 = 24.45 < 28.43.
4. `count_cherry_le_eight`: now every cost is <= 13, so |l| >= 38, and every r >= 1/9. Then 9 P -> 2 A_4
   with D0 = |l| - 9 >= 29.
5. `four_le_arm`: no A_j with j <= 3. If there were one, balance forces all arms <= 4, so costs are <= 9
   and |l| >= 55. But the counts give at most 1 leaf, at most 10 each of A_1, A_2, A_3, at most 10 A_4
   (D0 >= 44), and at most 8 cherries, so |l| <= 49.
6. `cand_of_isMax`: arms are in {4,5,6}. 4 and 6 cannot both occur (balance). count A_4 <= 10 comes from
   11 A_4 -> 9 A_5 with D0 >= 27, and count A_6 <= 10 from 11 A_6 -> 13 A_5 (every r <= 1/3).

`structProp_492 : StructProp 492` is step 6. Every sub-claim holds at N0 = 492. The tightest margins are
the step-3 global comparison (24.45 vs 28.43, which uses w5 >= 37 at n = 492) and, for the local
exchanges, 11 A_4 -> 9 A_5 and 9 P -> 2 A_4. Those two need only D0 >= 15 and 16 in exact arithmetic,
and the proof has D0 >= 27.
