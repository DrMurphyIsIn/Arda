# B2: exact optimization of Aobj over the two-level spider family (2026-09-24)

Scope: this note solves the optimization problem **inside one explicit family of trees** (a centre carrying
leaves, cherries and arms of cherries). It says nothing about trees outside the family, except the n <= 100
comparison in section 1, which reuses the exhaustive all-tree data. `conjecture1_proved = False`.

Script: `proof/verification/bg_spider_opt.py`. Lean: `proof/formalization/R3Cert/BGSpiderOpt.lean`.
Data: `proof/verification/bg_spider_opt_4_2400.json` (per-n maximizers, n = 4..2400).

## Summary

- **Closed form.** Label the centre's children as cherries P and arms A_j (a vertex adjacent to the centre
  that carries j cherries; A_0 is a leaf). Put alpha_j = (4j+3)/(3(j+1)) and b_j = 3/(4j+3). Then
  `Aobj = (3/2)^(C + sum j) * prod alpha_j * (1 + (C/3 + sum_j b_j)/D)`, with D the centre degree. This is the
  formula of the brief: a leaf is the case j = 0, where alpha_0 = b_0 = 1. It was checked against the tree
  engine `aobj_exact` on every configuration with n <= 22 (1309) and on 2941 random ones (4250 in all).
- **Membership (checked, exact).** For every n = 4..100 the maximum over the family equals the maximum over
  all n-vertex trees, and the two maximizer sets agree up to isomorphism. So all 97 sizes are inside the
  family. The n = 31 "two hub" shape L0C5-L0C5A[4] is the family member L0C5A[5, 4] rooted at a
  different vertex.
- **Proved exchange lemmas** (analytic, and formalized in Lean):
  (a) two leaves are never better than one cherry, so a maximizer with D >= 3 has at most one leaf;
  (b) *balance*: if D >= 3, moving a cherry from a larger arm to an arm at least 2 smaller strictly raises
  F. The exact identity is in section 2. So every maximizer with D >= 3 has all arm sizes (leaves included)
  in {s, s+1}.
- **Exact solution for every n.**
  - 4 <= n <= 2400: exhaustive exact maximization over the whole family. The balance lemma cuts the
    family to a two-parameter search, and everything is decided in exact arithmetic (section 3).
  - n >= 2320: a rigorous certificate (exact rationals, rigorous log enclosures) proves that the unique
    maximizer is R_inf(n) (section 4).
  - Together these prove the optimal rule below for all n. Only n = 4..243 needs a finite table.
- **The rule (proved for all n >= 244).** Let s = 6(n-1) mod 11, so that n-1 = 2s (mod 11). The maximizer has
  no leaves and no cherries, and its arms are all 5 except:
  - s = 0: none; s = 1..4: s arms of size 6; s = 5..10: 11-s arms of size 4. This is R_inf(n).
  - Exceptions: s = 1 with n <= 333 has one cherry (C = 1), and all arms are 5. For s = 2, 3, 4, the
    configuration with 11-s arms of size 4 wins up to n = 423, 722 and 2319 respectively, and R_inf wins
    after that.
- **Structure (proved, via the exhaustive range plus the certificate).**
  - Arms: for n >= 46 all arms are in {4,5,6}, and 4-arms never coexist with 6-arms.
  - Cherries: 0 <= C <= 8 for n >= 32, C <= 1 for n >= 244, C = 0 for n >= 334.
  - Arms other than 5: at most 9 fours or at most 4 sixes for n >= 46, and at most 6 fours or 4 sixes for
    n >= 2320. So the number of non-5 arms stays bounded (at most 9). Asymptotically it follows n mod 11
    with period 11.
  - Uniqueness: the maximizer is unique up to isomorphism for every n except n = 21. There, L0C10 and
    L0C3A[3, 3] tie.

## 0. The family and the closed form

Take the centre as the root. With the cavity recursion of `hwh_coverage_large_n.py`
(`S_v = prod S_c (d_v+R_v)/d_v`, `r_v = 1/(d_v+R_v)`, root value `prod S_c (k+R)/k`) the three child types
come out as follows:

| child | vertices c | S (= g) | r |
|---|---|---|---|
| leaf A_0 | 1 | 1 | 1 |
| cherry P | 2 | 3/2 | 1/3 |
| arm A_j (j >= 1) | 2j+1 | (3/2)^j alpha_j | b_j = 3/(4j+3) |

For an arm vertex of degree j+1 with j cherry children, R = j/3. So S = (3/2)^j (j+1+j/3)/(j+1) =
(3/2)^j (4j+3)/(3(j+1)) and r = 3/(4j+3). The value is `F(X) = prod_children g * (1 + R/D)`, with
n = 1 + sum c. `closedform` checks F against `aobj_exact` on the built tree for all 1309 configurations with
n <= 22 and 2941 random ones (C <= 8, at most 6 arms of size <= 9). All 4250 are equal.

The same tree can have several representations; a different vertex can serve as the centre. These are:
S(C; j) = S(j; C) (swap the two hubs when m = 1), and L1C0A[j] = L0C(j+1). Every such duplicate that
appears among the maximizers is listed in section 3, and each one was checked to be a single tree
(canonical form). All claims below are about the function F over representations. A strict statement
about representations implies the same statement about trees.

**Per-vertex rates.** rho_j = ln g(A_j)/(2j+1): 0.18654 (j=1), 0.20232, 0.20565, **0.2064721 (j=4)**,
**0.2065862 (j=5)**, **0.2064696 (j=6)**, 0.20628, 0.20607, 0.20587 (j=9). For a cherry it is ln(3/2)/2 =
0.2027326. A_5 is the unique best (this is the repo's d=6 five-cherry tie, `BGSCLSharp`). A_4 and A_6 are
almost tied behind it, and the bracket (1 + R/D) prefers small arms, since b_4 > b_5 > b_6. That is why the
optimum mixes 4s and 5s for moderate n and switches to 6s only for large n.

## 1. Membership check, n = 4..100 (exact, all trees)

`membership` runs the exhaustive all-tree `FrontierDP(100, "all")` from `hwh_coverage_large_n.py`. For
every n = 4..100 it compares that against the family optimum (section 3). Result: the maxima are equal as
exact fractions, and the sets of maximizing trees (canonical forms) are equal. So the true maximizer lies
in the family for every n in 4..100, including the small-n shapes (plain spiders L0Ck, one arm, and n = 31).

## 2. Proved exchange lemmas

Notation: a configuration is a multiset of children. D is the centre degree, and D0, R0 are the count and
r-sum of the children not involved in the move.

**Lemma 1 (balance, exact identity).** Put Q_c(x, y) = alpha_x alpha_y (c + b_x + b_y). For k >= 0 and
t >= 0:

    Q_c(k+t+1, k+1) - Q_c(k+t+2, k) = (t+1) * ((c-3)(8k+4t+15) + 3) / (9 (k+1)(k+2)(k+t+2)(k+t+3)).

Replace A_{k+t+2}, A_k by A_{k+t+1}, A_{k+1}. This keeps n and D fixed and keeps the power of 3/2 fixed.
It multiplies F by Q_c(new)/Q_c(old) with c = D + R0. If D >= 3 then c >= 3, so the move strictly
increases F. Consequence: every F-maximizer with D >= 3 is **balanced**, meaning all arm sizes (leaves are
size 0) differ by at most 1. For D = 2 with no other child the sign flips (c = 2), so two-child
configurations prefer imbalance. That is why D <= 2 is handled separately. Lean: `balance_identity`,
`F_balance_lt`, `balanced_of_isMax`.

**Lemma 2 (leaf pair).** [F(P + rest) - F(A_0 + A_0 + rest)] = P_rest (D0^2 + D0 R0 + 4 R0) / (2 (D0+1)(D0+2)) >= 0.
It is strict when D0 >= 1. So a maximizer with D >= 3 has at most one leaf. Lean: `F_leafpair_sub`,
`F_leafpair_lt`, `leaf_count_le_one_of_isMax`. With balance, a leaf forces every arm to be A_0 or A_1.
Such configurations are never optimal for n >= 22 (they only show up as the duplicate representations
L1C0A[j] = L0C(j+1)).

**Lemma 3 (cherry absorption P + A_j -> A_{j+1}, exact).** The move raises F if and only if

    3 D0^2 + D0 (3 R0 - 4j^2 - 11j - 6) + R0 (12j^2 + 33j + 24) - 4j^2 - 2j > 0.

Lean: `F_absorb_sub` gives the exact difference. With j = 5 and R0 about 0.13 D0, the move helps once D0
is about 29 or more. So cherries die out once the centre degree exceeds about 30 (n around 330), which is
what the exact data shows (C = 0 for n >= 334). Lemma 3 is used here only as an explanation. The proofs in
sections 3-4 do not depend on it.

**Lemma 4 (D <= 2 is small).** For n >= 3, every configuration with D <= 2 has F <= 3 (3/2)^((n-2)/2):
- A_j alone: F = (3/2)^j (alpha_j + 1/(j+1)) <= 2 (3/2)^((n-2)/2).
- P + A_j: F = (3/2)^((n-2)/2) ((7/6) alpha_j + 1/(2(j+1))) <= 2.06 (3/2)^((n-2)/2).
- A_j + A_k: F = (3/2)^((n-3)/2) (alpha_j alpha_k + (alpha_k/(j+1) + alpha_j/(k+1))/2) <= 3.11 (3/2)^((n-3)/2).
- P + P (n = 5): F = 3.

This matters because ln(3/2)/2 < rho_5, so these configurations are exponentially worse. The certificate
(section 4, step 0) uses Lemma 4. The exhaustive search (section 3) enumerates D <= 2 explicitly.

## 3. Exhaustive exact maximization over the family, n = 4..2400

`python3 bg_spider_opt.py search 4 2400 F.json` handles each n in two parts:
1. **D <= 2**: every configuration (one child, or any two children of total size n-1), O(n) of them.
2. **D >= 3, balanced**: by Lemma 1 these contain every maximizer with D >= 3. A balanced configuration is
   fixed by C and the arm count m: the arm vertices V = n-1-2C give sum j = (V-m)/2, then
   s = floor(sum j / m), and t = (sum j mod m) arms have size s+1. So the search covers every C and every m.

Every configuration is first scored by a float log F. Any configuration within 1e-9 of the float maximum is
then evaluated exactly (`fractions.Fraction`) and the decision is made on the exact values. For n <= 4000,
|ln F| < 850 and each float log is a sum of at most 4 terms, so the float error is below 1e-11, well under
the margin. The smallest observed gap between the maximizer and the best non-maximizer is 1.7e-6 (log
scale, at n = 2330), so the margin is never close to binding. This is an exact, exhaustive maximization over
the whole family. Nothing is sampled.

Independent cross-checks:
- The exact Pareto DP over the whole family (`dp`: no balance assumption, no arm-size cap, the pruning of
  `hwh_coverage_large_n._prune`) agrees exactly, maximizer sets included, for every n <= 600. The repo
  subcommand was run to n = 400; the run to 600 used a scratch copy of the same code.
- For n <= 100 it agrees with the all-tree DP (section 1).
- `search 2401 4000` agrees with the certificate at every n in 2401..4000.

**Maximizers for n = 4..243.** Notation: `L<leaves>C<cherries>A[arm sizes]`; `A{5:11,4:4}` means eleven
5-arms and four 4-arms. `X = Y` means two representations of the same tree. The one exception is n = 21,
where L0C10 and L0C3A[3, 3] are two different trees that tie.

| n: maximizer | n: maximizer | n: maximizer |
|---|---|---|
| 4: L0C0A[1] = L1C1 | 84: L0C6A[5, 5, 5, 5, 4, 4, 4] | 164: L0C3A{5:11,4:4} |
| 5: L0C2 = L1C0A[1] | 85: L0C8A[6, 5, 5, 5, 5, 5] | 165: L0C5A{5:14} |
| 6: L0C1A[1] | 86: L0C6A[5, 5, 5, 5, 5, 4, 4] | 166: L0C3A{5:12,4:3} |
| 7: L1C0A[2] = L0C3 | 87: L0C5A[5, 5, 4, 4, 4, 4, 4, 4] | 167: L0C3A{5:8,4:8} |
| 8: L0C1A[2] = L0C2A[1] | 88: L0C6A[5, 5, 5, 5, 5, 5, 4] | 168: L0C3A{5:13,4:2} |
| 9: L1C0A[3] = L0C4 | 89: L0C5A[5, 5, 5, 4, 4, 4, 4, 4] | 169: L0C3A{5:9,4:7} |
| 10: L0C2A[2] | 90: L0C6A[5, 5, 5, 5, 5, 5, 5] | 170: L0C4A{5:13,4:2} |
| 11: L1C0A[4] = L0C5 | 91: L0C5A[5, 5, 5, 5, 4, 4, 4, 4] | 171: L0C3A{5:10,4:6} |
| 12: L0C2A[3] = L0C3A[2] | 92: L0C7A[5, 5, 5, 5, 5, 5, 5] | 172: L0C4A{5:14,4:1} |
| 13: L1C0A[5] = L0C6 | 93: L0C5A[5, 5, 5, 5, 5, 4, 4, 4] | 173: L0C3A{5:11,4:5} |
| 14: L0C3A[3] | 94: L0C8A[5, 5, 5, 5, 5, 5, 5] | 174: L0C4A{5:15} |
| 15: L1C0A[6] = L0C7 | 95: L0C5A[5, 5, 5, 5, 5, 5, 4, 4] | 175: L0C3A{5:12,4:4} |
| 16: L0C3A[4] = L0C4A[3] | 96: L0C5A[5, 5, 4, 4, 4, 4, 4, 4, 4] | 176: L0C5A{5:15} |
| 17: L1C0A[7] = L0C8 | 97: L0C6A[5, 5, 5, 5, 5, 5, 4, 4] | 177: L0C3A{5:13,4:3} |
| 18: L0C4A[4] | 98: L0C5A[5, 5, 5, 4, 4, 4, 4, 4, 4] | 178: L0C2A{5:10,4:7} |
| 19: L1C0A[8] = L0C9 | 99: L0C6A[5, 5, 5, 5, 5, 5, 5, 4] | 179: L0C3A{5:14,4:2} |
| 20: L0C4A[5] = L0C5A[4] | 100: L0C5A[5, 5, 5, 5, 4, 4, 4, 4, 4] | 180: L0C2A{5:11,4:6} |
| 21: L1C0A[9] = L0C3A[3, 3] = L0C10 | 101: L0C6A[5, 5, 5, 5, 5, 5, 5, 5] | 181: L0C3A{5:15,4:1} |
| 22: L0C5A[5] | 102: L0C5A[5, 5, 5, 5, 5, 4, 4, 4, 4] | 182: L0C2A{5:12,4:5} |
| 23: L0C4A[3, 3] | 103: L0C7A[5, 5, 5, 5, 5, 5, 5, 5] | 183: L0C3A{5:16} |
| 24: L0C5A[6] = L0C6A[5] | 104: L0C5A[5, 5, 5, 5, 5, 5, 4, 4, 4] | 184: L0C3A{5:12,4:5} |
| 25: L0C4A[4, 3] | 105: L0C8A[5, 5, 5, 5, 5, 5, 5, 5] | 185: L0C4A{5:16} |
| 26: L0C6A[6] | 106: L0C5A[5, 5, 5, 5, 5, 5, 5, 4, 4] | 186: L0C3A{5:13,4:4} |
| 27: L0C4A[4, 4] | 107: L0C5A[5, 5, 5, 4, 4, 4, 4, 4, 4, 4] | 187: L0C2A{5:10,4:8} |
| 28: L0C6A[7] = L0C7A[6] | 108: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 4] | 188: L0C3A{5:14,4:3} |
| 29: L0C5A[4, 4] | 109: L0C5A[5, 5, 5, 5, 4, 4, 4, 4, 4, 4] | 189: L0C2A{5:11,4:7} |
| 30: L0C7A[7] | 110: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5] | 190: L0C3A{5:15,4:2} |
| 31: L0C5A[5, 4] | 111: L0C5A[5, 5, 5, 5, 5, 4, 4, 4, 4, 4] | 191: L0C2A{5:12,4:6} |
| 32: L0C7A[8] = L0C8A[7] | 112: L0C6A[5, 5, 5, 5, 5, 5, 5, 5, 5] | 192: L0C3A{5:16,4:1} |
| 33: L0C5A[5, 5] | 113: L0C5A[5, 5, 5, 5, 5, 5, 4, 4, 4, 4] | 193: L0C2A{5:13,4:5} |
| 34: L0C8A[8] | 114: L0C7A[5, 5, 5, 5, 5, 5, 5, 5, 5] | 194: L0C3A{5:17} |
| 35: L0C6A[5, 5] | 115: L0C5A[5, 5, 5, 5, 5, 5, 5, 4, 4, 4] | 195: L0C2A{5:14,4:4} |
| 36: L0C4A[4, 4, 4] | 116: L0C4A[5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4] | 196: L0C4A{5:17} |
| 37: L0C7A[5, 5] | 117: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 4, 4] | 197: L0C2A{5:15,4:3} |
| 38: L0C5A[4, 4, 4] | 118: L0C4A[5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4] | 198: L0C1A{5:12,4:7} |
| 39: L0C7A[6, 5] | 119: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 4] | 199: L0C2A{5:16,4:2} |
| 40: L0C5A[5, 4, 4] | 120: L0C4A[5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4] | 200: L0C2A{5:12,4:7} |
| 41: L0C7A[6, 6] | 121: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 201: L0C2A{5:17,4:1} |
| 42: L0C6A[5, 4, 4] | 122: L0C5A[5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4] | 202: L0C2A{5:13,4:6} |
| 43: L0C8A[6, 6] | 123: L0C6A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 203: L0C2A{5:18} |
| 44: L0C6A[5, 5, 4] | 124: L0C5A[5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4] | 204: L0C2A{5:14,4:5} |
| 45: L0C8A[7, 6] | 125: L0C7A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 205: L0C3A{5:18} |
| 46: L0C6A[5, 5, 5] | 126: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4] | 206: L0C2A{5:15,4:4} |
| 47: L0C5A[4, 4, 4, 4] | 127: L0C4A[5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4] | 207: L0C1A{5:12,4:8} |
| 48: L0C7A[5, 5, 5] | 128: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4] | 208: L0C2A{5:16,4:3} |
| 49: L0C5A[5, 4, 4, 4] | 129: L0C4A[5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4] | 209: L0C1A{5:13,4:7} |
| 50: L0C7A[6, 5, 5] | 130: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4] | 210: L0C2A{5:17,4:2} |
| 51: L0C6A[5, 4, 4, 4] | 131: L0C4A[5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4] | 211: L0C1A{5:14,4:6} |
| 52: L0C7A[6, 6, 5] | 132: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 212: L0C2A{5:18,4:1} |
| 53: L0C6A[5, 5, 4, 4] | 133: L0C4A[5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4] | 213: L0C1A{5:15,4:5} |
| 54: L0C7A[6, 6, 6] | 134: L0C6A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 214: L0C2A{5:19} |
| 55: L0C6A[5, 5, 5, 4] | 135: L0C4A[5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4, 4] | 215: L0C1A{5:16,4:4} |
| 56: L0C5A[4, 4, 4, 4, 4] | 136: L0C7A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 216: L0C3A{5:19} |
| 57: L0C6A[5, 5, 5, 5] | 137: L0C4A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4] | 217: L0C1A{5:17,4:3} |
| 58: L0C5A[5, 4, 4, 4, 4] | 138: L0C4A{5:6,4:7} | 218: L0C1A{5:13,4:8} |
| 59: L0C7A[5, 5, 5, 5] | 139: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4] | 219: L0C1A{5:18,4:2} |
| 60: L0C6A[5, 4, 4, 4, 4] | 140: L0C4A{5:7,4:6} | 220: L0C1A{5:14,4:7} |
| 61: L0C8A[5, 5, 5, 5] | 141: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4] | 221: L0C1A{5:19,4:1} |
| 62: L0C6A[5, 5, 4, 4, 4] | 142: L0C4A{5:8,4:5} | 222: L0C1A{5:15,4:6} |
| 63: L0C8A[6, 5, 5, 5] | 143: L0C5A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 223: L0C2A{5:19,4:1} |
| 64: L0C6A[5, 5, 5, 4, 4] | 144: L0C4A{5:9,4:4} | 224: L0C1A{5:16,4:5} |
| 65: L0C5A[4, 4, 4, 4, 4, 4] | 145: L0C6A[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] | 225: L0C2A{5:20} |
| 66: L0C6A[5, 5, 5, 5, 4] | 146: L0C4A{5:10,4:3} | 226: L0C1A{5:17,4:4} |
| 67: L0C5A[5, 4, 4, 4, 4, 4] | 147: L0C3A{5:7,4:7} | 227: L0C0A{5:14,4:8} |
| 68: L0C6A[5, 5, 5, 5, 5] | 148: L0C4A{5:11,4:2} | 228: L0C1A{5:18,4:3} |
| 69: L0C5A[5, 5, 4, 4, 4, 4] | 149: L0C3A{5:8,4:6} | 229: L0C0A{5:15,4:7} |
| 70: L0C7A[5, 5, 5, 5, 5] | 150: L0C4A{5:12,4:1} | 230: L0C1A{5:19,4:2} |
| 71: L0C6A[5, 5, 4, 4, 4, 4] | 151: L0C4A{5:8,4:6} | 231: L0C0A{5:16,4:6} |
| 72: L0C8A[5, 5, 5, 5, 5] | 152: L0C4A{5:13} | 232: L0C1A{5:20,4:1} |
| 73: L0C6A[5, 5, 5, 4, 4, 4] | 153: L0C4A{5:9,4:5} | 233: L0C0A{5:17,4:5} |
| 74: L0C8A[6, 5, 5, 5, 5] | 154: L0C5A{5:13} | 234: L0C1A{5:21} |
| 75: L0C6A[5, 5, 5, 5, 4, 4] | 155: L0C4A{5:10,4:4} | 235: L0C0A{5:18,4:4} |
| 76: L0C5A[5, 4, 4, 4, 4, 4, 4] | 156: L0C6A{5:13} | 236: L0C0A{5:14,4:9} |
| 77: L0C6A[5, 5, 5, 5, 5, 4] | 157: L0C4A{5:11,4:3} | 237: L0C0A{5:19,4:3} |
| 78: L0C5A[5, 5, 4, 4, 4, 4, 4] | 158: L0C3A{5:8,4:7} | 238: L0C0A{5:15,4:8} |
| 79: L0C6A[5, 5, 5, 5, 5, 5] | 159: L0C4A{5:12,4:2} | 239: L0C0A{5:20,4:2} |
| 80: L0C5A[5, 5, 5, 4, 4, 4, 4] | 160: L0C3A{5:9,4:6} | 240: L0C0A{5:16,4:7} |
| 81: L0C7A[5, 5, 5, 5, 5, 5] | 161: L0C4A{5:13,4:1} | 241: L0C1A{5:20,4:2} |
| 82: L0C5A[5, 5, 5, 5, 4, 4, 4] | 162: L0C3A{5:10,4:5} | 242: L0C0A{5:17,4:6} |
| 83: L0C8A[5, 5, 5, 5, 5, 5] | 163: L0C4A{5:14} | 243: L0C1A{5:21,4:1} |

Values: `max_float` for every n and the exact fraction for n <= 120 are in `bg_spider_opt_4_2400.json`.
They agree with the `BG_HWH_COVERAGE_LARGE_N_2026-09-24.md` table for every n in 4..100.

## 4. Certificate for n >= 2320 (proved, exact rational arithmetic)

`python3 bg_spider_opt.py asymptotic 2320` prints `CERTIFICATE for all n >= 2320: True`. It fails at
N* = 2319, as it must, because R_inf(2319) is not the maximizer. The argument, for a maximizer X at size
n >= N*:

Log accounting. Put rho = ln g(A_5)/11 and pen_t = c_t rho - ln g_t >= 0. For any X,
ln F(X) = rho (n-1) - sum_t k_t pen_t + ln B(X), where B = 1 + R/D. Since F(X) >= F(R_inf(n)):

    Pen(X) <= Pen(R_inf) + ln B(X) - ln B(R_inf).

All logs are enclosed in rational intervals (atanh series with an explicit remainder). The values are:
pen_P = 0.0077073, pen_4 = 0.0010264, pen_6 = 0.0015153, pen_3 = 0.0065644, pen_7 = 0.0046036. Pen(R_inf) is
at most Pbar = 0.006159, and B(R_inf) >= 1 + b_6.

- **Step 0.** By Lemma 4, D <= 2 is beaten: ln F(R_inf) >= rho(n-1) - Pbar + ln(1+b_6) > ln 3 + (n-2)/2 ln(3/2).
  So D >= 3, and X is balanced.
- **Step 1 (s = 0).** Every arm is A_0 or A_1 and B <= 2. Then Pen >= (n-1) pen_P/2 > Pbar + ln(2/(1+b_6)).
  Impossible.
- **Step 2 (s >= 1, s not in {4,5}).** No arm has size 5 and every r <= 3/7, so B <= 10/7. Per-vertex
  penalties are at least mu = rho_5 - rho_4 = 1.1405e-4 for any arm size other than 5. That bound is checked
  as an interval for j <= 20, and for j >= 21 through rho_j <= ln(3/2)/2 + (ln(4/3) - ln(3/2)/2)/(2j+1). For
  cherries the per-vertex penalty is 3.85e-3. So Pen(X) >= mu (n-1), which exceeds Bud1 = Pbar + ln((10/7)/(1+b_6)) = 0.2575
  once n >= 2259. Hence arm sizes are in {4,5} or {5,6}, and C <= Bud1/pen_P, so C <= 33.
- **Step 3 (refined budget).** Now D >= m >= (n-1-2C)/13. Write
  B(X) = 1 + b_5 + [C(1/3 - b_5) + k4(b_4 - b_5) - k6(b_5 - b_6)]/D and use ln(1+x) <= x. For each residue
  class s this gives C(pen_P - e_P) + k4(pen_4 - e_4) + k6 pen_6 <= Pen(R_inf, s) + y/(1-y). The terms e_P,
  e_4, y are O(1/n) and bounded at N*. Together with the congruence C + k6 - k4 = s (mod 11) (because
  n-1 = 11 a5 + 9 k4 + 13 k6 + 2C), this leaves R_inf alone in every class except s = 4. There the one other
  candidate is (C, k4, k6) = (0, 7, 0).
- **Step 4 (exact comparison).** For each remaining candidate Z, F(Z)/F(R_inf) = K * B(Z)/B(R_inf), with K a
  fixed rational (the 5-arm counts differ by a constant) and each B a ratio of two affine functions of
  N = a5(R_inf). Here F(Z) < F(R_inf) is the sign of an explicit quadratic in N. It holds for all
  N >= N0(N*), checked exactly (leading coefficient, vertex, and integer points up to the vertex).

So for every n >= 2320 the unique maximizer is R_inf(n). The steps are monotone in n: every e-term shrinks
and every penalty lower bound grows with n, so checking at N* covers every n >= N*.

**Rule thresholds (exact).** F(alt)/F(R_inf) - 1 at the last and first size of each switch:

| class s | alternative | last n it wins | ratio - 1 there | next n in class | ratio - 1 there |
|---|---|---|---|---|---|
| 1 | C = 1, all 5-arms | 333 | +1.51e-4 | 344 | -4.71e-5 |
| 2 | nine 4-arms | 423 | +1.44e-4 | 434 | -1.21e-5 |
| 3 | eight 4-arms | 722 | +2.00e-5 | 733 | -3.45e-5 |
| 4 | seven 4-arms | 2319 | +3.58e-6 | 2330 | -1.73e-6 |

## 5. The optimal rule, and what is proved

**Theorem (spider family, all n).** For n >= 244 the maximizer of F over the family is unique and is given
by the rule in the summary. For 4 <= n <= 243 it is the table in section 3. For n >= 46 it lies in the
bounded, n-independent candidate set Cand(n) = {C <= 8 cherries, arms in {4,5,6} with at most 9 fours or at
most 4 sixes, not both}.

Status of each part:

| claim | status |
|---|---|
| closed form = Aobj of the tree | derivation (cavity recursion) + exact check on 4250 configurations |
| Lemma 1 (balance), Lemma 2 (leaves), Lemma 3 identity, F permutation-invariant | **proved**, Lean (axiom-clean) |
| Lemma 4 (D <= 2 bound) | proved (elementary, this note); not in Lean |
| maximizer(s) for every 4 <= n <= 2400 | **proved by exhaustive exact computation** (relies on Lemma 1; float prefilter with a 1e-9 margin, exact decision) |
| n >= 2320: unique maximizer R_inf(n) | **proved** by the exact-rational certificate (`asymptotic 2320`); not in Lean |
| rule for all n >= 244; Cand(n) for n >= 46; C, arm-size and non-5 bounds | proved: combination of the two rows above |
| 2401..4000 exhaustive search agrees with the rule | checked (redundant with the certificate) |
| n <= 100: family maximum = all-tree maximum | checked exhaustively and exactly (reuses FrontierDP) |
| n > 100: true (all-tree) maximizer lies in the family | **not proved, not checked here** |

The computer-assisted parts (search and certificate) are rigorous: exact rational arithmetic, plus
interval-enclosed logs and a quantified float margin in the prefilter. They have not been formalized.

## 6. Lean

`R3Cert/BGSpiderOpt.lean` (namespace `R3Cert.BGSpiderOpt`) models a configuration as `List Child` with the
closed-form value `F` over ℚ. It is not connected to the tree graph. Theorems: `balance_identity`,
`Q_lt_of_three_le`, `F_balance_lt`, `balanced_of_isMax`, `F_leafpair_sub`, `F_leafpair_le`,
`F_leafpair_lt`, `leaf_count_le_one_of_isMax`, `F_absorb_sub`, `F_perm`. `lake build R3Cert.BGSpiderOpt`
succeeds. `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every one; there is no
`sorry` and no `native_decide`. The six main ones are registered in `AxiomGuard.lean`, and
`lake env lean AxiomGuard.lean` exits 0.

## Reproduce

    cd proof/verification
    python3 bg_spider_opt.py closedform
    python3 bg_spider_opt.py symbolic
    python3 bg_spider_opt.py search 4 2400 /tmp/s.json     # ~70 CPU-s (seconds on 24 workers)
    python3 bg_spider_opt.py rule /tmp/s.json
    python3 bg_spider_opt.py asymptotic 2320
    python3 bg_spider_opt.py dp 400                        # ~2.5 min (600: ~25 min)
    python3 bg_spider_opt.py membership                    # ~6 min (all-tree FrontierDP to 100)
