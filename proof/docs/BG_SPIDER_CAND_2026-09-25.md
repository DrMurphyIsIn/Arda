# BG spider certificate, part L2: `CandProp 492` (2026-09-25)

**Result.** `R3Cert.BGSpiderCand.candProp_492 : R3Cert.BGSpiderRule.CandProp 492` is kernel-checked. Among
the bounded candidates `Cand`, the rule winner `W n` maximizes the closed-form spider value `F` at every size
n >= 492. Candidates have at most 8 cherries, arms of 4, 5 or 6 cherries only, never both 4-arms and 6-arms,
and at most 10 arms of 4 and at most 10 of 6. The axioms are propext, Classical.choice and Quot.sound, with
no `sorry`, no `native_decide` and no new axioms (checked in `AxiomGuard.lean`).

This discharges one of the two open inputs of `BGSpiderRule.bg_maximizer_of`. The other one is `StructProp`,
which says every F-maximizer is a candidate. `conjecture1_proved = False` is unchanged.

## How the proof works

1. **Closed form from the counts** (`BGSpiderCandBase`). A list of admissible children (cherries and arms of
   4, 5 and 6) is fixed up to permutation by its counts (C, k4, k5, k6). By induction on the list,
   `F l = Φ C k4 k5 k6` and `nv l = 1 + 2C + 9k4 + 11k5 + 13k6` (`F_eq_Φ`, `nv_eq`). The same lemma gives
   `F (W n) = Φ 0 (w4 n) (w5 n) (w6 n)` (`F_W_eq`). Here
   `Φ = (3/2)^C G4^k4 G5^k5 G6^k6 (1 + (C/3 + k4 B4 + k5 B5 + k6 B6)/(C+k4+k5+k6))`, with
   G4 = 513/80, G5 = 621/64, G6 = 6561/448, B4 = 3/19, B5 = 3/23 and B6 = 1/9.
2. **One quadratic per comparison.** The combo (C, k4, k6) fixes the residue class
   s = 6(n-1) mod 11 = (C - k4 + k6) mod 11. The class fixes the winner's (w4, w6). For s = 3 and s = 4 you
   also need to know which side of 722 or 2319 n is on, so those classes split into two regimes. Within one
   regime, k5 - w5 is a constant. So we write k5 = m + k1 and w5 = m + k2, where m = min(k5, w5). Dividing out
   G5^m reduces `Φ(combo) <= Φ(W)` to `0 <= P(m)`, where P is an explicit quadratic
   (`BGSpiderCandBase.P`, `Φ_le_of_P`).
3. **Certificates.** n >= 492, together with the regime bounds, gives an integer range L <= m (<= U). Two
   certificate shapes are used:
   * **mono** (221 certificates): `P(L + t) = c0 + c1 t + c2 t^2` with every ci >= 0, so the bound holds for
     all t >= 0.
   * **bern** (2 certificates): `P(L + t) = b0 (T-t)^2 + b1 t(T-t) + b2 t^2` with every bi >= 0, on
     [0, T] with T = U - L. Both are low-regime cases where the rival would win outside the range:
     * (C, k4, k6) = (0, 0, 3) against 8 fours, for m in [39, 59], which is n <= 722.
     * (0, 0, 4) against 7 fours, for m in [39, 205], which is n <= 2319.

   Lean checks each polynomial identity with `ring`. The signs are checked with `norm_num`, and then
   `positivity` finishes.
4. **Assembly.** `cand_counts` splits into the 189 combos with `interval_cases` and applies
   `combo_C_k4_k6`. Each of those reads off `sres`, `w4`, `w6` and `w5` with `omega` and then calls the
   certificate. `candProp_492` pulls the counts out of `Cand` (k4·k6 = 0 comes from the no-4-and-6 clause)
   and applies `cand_counts`.

In total there are 189 combos and 223 certificates. No combo fails for any n >= 492. The rule, including the
exception thresholds 722 and 2319, is exactly right on `Cand`.

## Files

- `proof/verification/bg_spider_cand_certs.py` builds every certificate with exact `Fraction` arithmetic. It
  then re-checks each one: the identity is tested at 7 points, and it also checks the signs, that the range
  and regime match the rule's `w4`/`w6`/`w5`, and that the ends of each range are tight. Finally it
  brute-forces CandProp for n = 492..3000. `--emit` regenerates the Lean files listed below.
- `R3Cert/BGSpiderCandBase.lean` (hand-written): Φ, the counts lemma, P, `Φ_le_of_P`, the certificate
  shapes and the winner-count lemmas `w_zero`, `w_six` and `w_four`.
- `R3Cert/BGSpiderCandCells{0..8}.lean` (generated, one file per cherry count): `cert_C_k4_k6_r` and
  `combo_C_k4_k6`.
- `R3Cert/BGSpiderCand.lean` (generated): `cand_counts` and `candProp_492`.

## Build

`lake build R3Cert.BGSpiderCand` succeeds. The nine cell files build in parallel in about 43 s each, and the
build takes about 1 min of wall time on top of a built `.lake`. `lake env lean AxiomGuard.lean` exits 0.
