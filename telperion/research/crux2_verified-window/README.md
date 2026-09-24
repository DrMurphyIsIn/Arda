# crux2_verified-window: a kernel-certified form-level comb constant, and what verified zeros buy on a fixed Weil window

**conjecture1_proved = False.** RH is open, and nothing here moves it. Everything in this directory
concerns one **fixed** window `[-L, L]` of the Weil explicit formula. Weil positivity for *all*
windows is RH. For one window it is a strictly weaker statement: Davenport-Heilbronn is positive
on small windows despite having off-line zeros.

The idea handed to this builder had four parts:

* a **form-level** comb constant `A_win` that replaces Zhu's pointwise constant `A_L`, about 3x
  smaller in the exponent;
* a Theorem 1 that uses this constant with no zeros at all;
* a Theorem 2 that glues verified zeros below height `T` to the window arithmetic above `T`;
* a numerical instance: at `T = 640000`, `lambda_min(Q_L) >= -10^-1157` for every `L <= 2.25`
  (support 4.5).

The task input contained the idea in full. The only referee material was the referees' check
scripts (`aw.py`, `twist.py`, `eps.py` in `/private/tmp/claude-0/crux2/ref-verified-window/`),
and their outputs agree with the idea's numbers. So I re-derived everything below independently
instead of taking it from the idea.

Status tags follow the house convention: THEOREM-kernel-checked, THEOREM-paper-proof, COMPUTED,
CONJECTURE-with-evidence, HEURISTIC.

---

## 1. The story in one page

Zhu's barrier (arXiv:2608.24827, Thm 1.4) says this: a certificate that bounds the prime comb
`P_L(t) = sum_{log n < 2L} 2 Lambda(n)/sqrt(n) cos(t log n)` **pointwise** can do no better than
`sup_t P_L = A_L ~ 4 e^L`. The frequency cutoff it needs is then `2 pi e^{A_L}`. The escape the
idea proposes is elementary.

In the Weil form the comb never meets an arbitrary function. It meets `|F|^2` with `f` supported
in the window. There it acts as the operator
`P = sum_n (Lambda(n)/sqrt n)(tau_{log n} + tau_{log n}^*)` compressed to `L^2[-L, L]`. The norm
of that compressed operator, `A_win`, is much smaller than `A_L`, because a shift by nearly `2L`
barely overlaps the window with itself. Nothing here needs the phases `t log p` to misalign. The
twisted comb (the symbol at frequency `t + r`) is dominated entry by entry by the untwisted one,
because `Lambda >= 0`. So the same constant bounds every high-frequency Rayleigh quotient.

**What is now proved in the kernel**, on the program's own explicit-formula vocabulary
(E6Bridge4/5 on the `rvm_bridge` island), is the following.

1. **Form-level comb bound (general).** Suppose a positive weight `w` satisfies the Schur
   inequality `sum_n c_n (1_W w(x - log n) + 1_W w(x + log n)) <= lam w(x)` on `W = [-L, L]`.
   Then for every continuous, compactly supported `g` vanishing off `W`:
   `||primeSide(g * g~)|| <= lam ||g||^2`.
   The same bound holds for every twist `g -> e^{irx} g`.
   Theorems: `schur_comb`, `primeSide_autocorr_le`, `autocorr_modulate`,
   `primeSide_autocorr_modulate`, `primeSide_autocorr_twist_le`, `weilForm_autocorr_ge`.
   The idea's finite core, `schur_twist_bound`, is ported into the same file.
2. **The certified constant at `L' = 2.3`.** An exact-integer certificate is evaluated by the
   kernel. It uses 920 cells, the 35 prime powers `n < 100`, and rational enclosures of
   `log p` for `p <= 97`, which are themselves proved from Mathlib's `log 2` bounds and the log
   series. It gives
   `||primeSide(g * g~)|| <= 11.161373010 ||g||^2` for every `g` supported in `[-2.3, 2.3]`
   (`primeSide_autocorr_le_cert`).
   The pointwise constant of the same window is `A_{2.3} = sum_{n<100} 2 Lambda(n)/sqrt n = 33.79`,
   and the kernel checks `3 * 11.161373 < A_{2.3}` (`combMass_gt_three_lam`).
   The Galerkin lower bound is 11.0586, so `A_win(2.3)` lies in `[11.0586, 11.1614]`.
3. **Theorem 2's gluing on the real explicit formula** (`weil_almost_pos_of_glue`,
   `weil_almost_pos_cert`). Put `G_phi := g*g~ - gH*gH~`. Assume:
   * `|gH^| <= |g^|` on the real line;
   * every nontrivial zero with `|Im| <= T` lies on the line;
   * the unverified-zero tail of `G_phi` sums to at most `E_1`;
   * `Re Arch(gH*gH~) >= lam ||gH||^2 - E_2`.

   Then `Re W(g*g~) >= -(E_1 + E_2)`. The prime side of `gH*gH~` is discharged by the certified
   constant.

**What stays paper proof plus computation.** Theorem 2's three analytic inputs are:

* the Fejer-power multiplier `K = 1_{[-Tm,Tm]} * kappa` and its tail bounds;
* the digamma envelope and the leakage below `R`;
* Trudgian's explicit `S(t)` for counting unverified zeros.

I re-derived all three (section 4). One harmless correction to the idea: the idea took
`R = 2 pi e^{A+}(1 + 10^-6)`, but Zhu's Lemma 3.1 does not support that margin. With the
**kernel-certified** constant, `A+ = 11.161373`, the instance gives

    lambda_min(Q_L) >= -10^-997      for every L <= 2.25   (support 4.5, CCM window x = e^{4.5} ~ 90),

conditional on the zeros up to 640000 lying on the line. The idea's float constant, 11.084,
reproduces its own figure: -10^-1163 here, against -10^-1157 in the idea.

Exact positivity, `lambda_min(M_T) > eps`, remains a CONJECTURE-with-evidence and was not built
here.

---

## 2. How to check the Lean

```
cd telperion/examples/rvm_bridge/lean
/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/leanlock.sh \
    lake env lean Crux/Crux2_verified_window.lean
```

Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb. The check takes about 80 s; the kernel
evaluation of the 920-row certificate accounts for about half of that. The file contains no
`sorry`, `admit`, `native_decide`, `opaque` or new `axiom`. Every `#print axioms` line reports
only `[propext, Classical.choice, Quot.sound]`; `cw_check` and `checkRows_sound` report only
`[propext]`. The output is in `outputs/lean_check_output.txt`.

The file is **generated**:

```
cd scripts && python3 build_lean.py ../certificates/cert_L23_N920.json <out.lean> header.lean.part cw
```

This reproduces the checked file byte for byte. `generic_part.lean` holds the hand-written
theory. `emit_instance.py` and `build_lean.py` write the log-bound lemmas, the per-entry facts,
the weight tree and the gluing section.

### 2.1 Why this certificate design (footguns found on the way)

* `decide` on `IsPrimePow n` gets stuck for `n = 15`, because `Nat.minFac` is well-founded
  recursion. The non-prime-powers below 100 are therefore handled by one lemma: `Lambda n = 0`
  whenever `n = a*b` with coprime `a, b > 1`.
* A list lookup (`List.getD`) inside the kernel checker costs time linear in the index, and it
  made a 460-row probe take minutes. A complete binary tree (`WTree`) makes each lookup
  O(depth). With the tree, 920 rows x 35 shifts x 2 sides check in well under a minute under
  `decide +kernel`.
* Plain `decide` runs out of heartbeats in the elaborator. `decide +kernel` evaluates in the
  kernel and adds no axiom.
* The log-series enclosure uses `log p = log(p+1) + log(1 - 1/(p+1))`. For `p <= 97`, `p + 1`
  factors into smaller primes, so the enclosures chain from `log 2`. Widths are at most
  `4e-9`.

---

## 3. The certificate, and the other windows

This is a Schur/Collatz-Wielandt test in which the step weight is exact:

* The window `[-L', L']` is divided into `N` cells of width `h`, and the weight is
  `w = f(cell(x))` with integer values `f(k) >= 1`.
* `log n` is enclosed in `[A q, B q]`, where `q = h/H`.
* For `x` in cell `k`, the shifted point `x - log n` lies in the cell range
  `[(kH - B) div H, min(((k+1)H - A) div H, N-1)]`, and `x + log n` lies in
  `[min((kH + A) div H, N-1), min((kH + H + B) div H, N-1)]`.

The checker takes the maximum weight over those ranges and verifies
`sum C_n (M- + M+) <= Lam f(k)` in integers. The soundness lemmas (`mMinus_sound`,
`mPlus_sound`, `schur_of_check`) are proved for arbitrary data. The loss relative to the true
norm is O(1/N), from taking a maximum over two adjacent cells: 11.2387 at `N = 460`, 11.1614 at
`N = 920`.

| window `L'` | used for | Galerkin lower | certified upper | status of the upper bound | idea's float CW |
|---|---|---|---|---|---|
| 2.3 | `A+` for `L = 2.25` | 11.0586 | **11.161373010** | **kernel-checked** | 11.0840 |
| 2.25 | `A+` for `L = 2.2` | 10.5018 | 10.603790 | exact-integer Python, same algorithm | 10.5268 |
| 2.05 | `A+` for `L = 2.0` | 8.4222 | 8.508782 | exact-integer Python | 8.4612 |
| 1.4666 | `A+` for `L = 1.4166` | 4.0773 | 4.138132 | exact-integer Python | 4.2449 |

The PNT continuum model replaces the prime comb by the kernel `e^{|x-y|/2}` on `[-L, L]`
(`outputs/pnt_check.txt`). There `lambda_max/e^L` is 1.2325 at `L = 2`, 1.1033 at `L = 4` and
1.0047 at `L = 8`, while the pointwise mass divided by `e^L` tends to 4. So `A_win ~ e^L ~ A_L/4`
(HEURISTIC asymptotics). The threshold `2 pi e^{A_win}` is asymptotically the fourth root of
Zhu's `2 pi e^{A_L}`.

---

## 4. Theorem 2: re-derivation, correction, numbers

**Statement (THEOREM-paper-proof).** Let `kappa = c_m (sin(ax)/(ax))^{2m}` with `a = delta/4m`,
and let `K = 1_{[-Tm,Tm]} * kappa`, `omega = 1 - K`, `phi = K(2 - K)`. Assume every zero with
`|Im rho| <= T` lies on the line. Then for `f` in `C_c^inf(-L, L)` with `||f|| = 1`:

    Q(f) >= M_T(f) - eps,
    M_T(f) = sum_{|gamma|<=T} phi(gamma)|F(gamma)|^2 + (1/2pi) int omega^2 |F|^2 (Psi_0 - A+)_+   (>= 0),
    eps = (A+ + 5.3722) tau_0(Tm - R)^2 + 4(e^L - 1) tau_{1/2}(Tm)^2
          + 12 L e^L sum_{k>=0} log(T+k+1) tau_{1/2}(T+k-Tm).

Here `A+ = A_win(L+delta/2)`, and `tau_y(X) = int_{|x|>X} |kappa(x+iy)| dx`.

**Proof, in the order of the kernel skeleton.**

* The split `G = phi G + omega^2 G` is an identity of entire functions. Both pieces are
  transforms of `C_c^inf` tests: `C_c^inf * L^1_c`. The explicit formula is linear, so it can be
  applied to each piece. Because the split is made on `|F|^2`, there are no cross terms.
* **The `phi G` piece, on the zero side.**
  * A verified zero contributes `m phi(gamma)|F(gamma)|^2 >= 0`, because `0 <= K <= 1` on the
    real line.
  * An unverified zero has `|phi| <= 3|K| <= 3 tau_{1/2}(|Re gamma| - Tm)` and
    `|F(gamma) F(conj gamma)| <= 2 L e^L`.
  * Unverified zeros are counted per unit height by Trudgian's bound: at `t = 640000` it gives
    11.3, below `log t = 13.4`.
* **The `omega^2 G` piece, on the arithmetic side.** Its test is `autocorr(mu * f)`, and
  `mu * f` is supported in `[-L', L']`. The prime side is at most `A+ ||mu * f||^2`; this is the
  kernel-checked bound. The pole term is at least `-4(e^L - 1) tau_{1/2}(Tm)^2`: `K(i/2)` is
  real, and a contour shift gives `|1 - K(i/2)| <= tau_{1/2}(Tm)`.
* **The archimedean part.** `Psi_0` is even and increasing in `|t|`, with minimum
  `Psi_0(0) = -5.372183`. On `|t| < R`, `0 <= omega <= tau_0(Tm - R)`.

**Correction (harmless).** The idea used `R = 2 pi e^{A+}(1 + 10^-6)`. Zhu's Lemma 3.1,
`Psi_0 >= log(t/2pi) - 1/t`, does **not** give `Psi_0 >= A+` at that `R`. At `A+ = 11.084`,
`log(R/2pi) - 1/R - A+ = -1.44e-6`; at `A+ = 4.2449` the deficit is `-2.3e-3`
(`outputs/psi0_check.txt`). The true `Psi_0(R) - A+` is `+1.0e-6`, because
`Psi_0 = log(t/2pi) - 1/(24t^2) + ...`. So the needed inequality is true, but the cited lemma
does not prove it. The fix is to take `R` as the root of `log(R/2pi) - 1/R = A+`, which is about
`2 pi e^{A+} + 1`; the effect on `eps` is invisible. Separately, the idea's constant
`I_m >= 1.42/sqrt m` is valid but conservative: `I_m >= sqrt(5pi/2m) erf(sqrt(2m/5)) ~ 2.8/sqrt m`.

**Numbers.** These come from `scripts/eps_rigorous.py`: log domain, 50 digits, the `k`-sum
bounded rigorously. The inputs are `T = 640000` and `delta = 0.1`. The rows are COMPUTED and
conditional on the zeros up to 640000 lying on the line. That fact is established in the
literature by Platt-Trudgian (to `3e12`). Inside the program it is `AllZeros_h640000`, which is
Arb-conditional and lives on the `li_positivity` island.

| L | `A+` | source of `A+` | R | m | Tm | log10 eps |
|---|---|---|---|---|---|---|
| **2.25** | **11.161373010** | **kernel** | 442083 | 1000 | 513333 | **<= -997.3** |
| 2.25 | 11.084 | idea's float CW | 409167 | 1100 | 489959 | <= -1163.4 |
| 2.25 | 11.37 | idea's robustness threshold | 544639 | 500 | 579923 | <= -473.7 |
| 2.2 | 10.603790 | exact-integer Python | 253133 | 1700 | 384668 | <= -1949.7 |
| 2.0 | 8.508782 | exact-integer Python | 31154 | 3000 | 250338 | <= -3065.5 |
| 1.4166 | 4.138132 | exact-integer Python | 394.9 | 3000 | 224257 | <= -3234.7 |

For comparison:

* Yoshida and Connes-Consani reach `L <= log2/2 = 0.347`, where no primes enter.
* Zhu certified exact positivity at `L = 0.8`.
* Zhu's pointwise one-stroke ceiling at `T = 640000` is `L < log17/2 = 1.4166`.

The result here is **almost**-positivity, not positivity.

---

## 5. Negative controls and circularity

**Davenport-Heilbronn.** Its `Lambda_D` is signed; for example `Lambda_D(6) = +1.9364`. The
domination step therefore fails, and it must. In the cell-Galerkin check
(`outputs/twist_dh_check.txt`):

| L | zeta, untwisted | zeta, best twist | D, untwisted | D, best twist | D excess |
|---|---|---|---|---|---|
| 1.0 | | | 1.25306 | 1.29178 | |
| 1.717 | 5.67476 | 5.67476 | 2.91210 | 4.45127 | +53% |
| 2.3 | 11.05626 | 11.05626 | | | |

The zeta twists are the best of 400 random twists plus Nelder-Mead. The D value 4.45127
reproduces the idea's 4.452. D's form-level threshold at its indefiniteness onset,
`2 pi e^{4.45} = 539`, lies far above its first off-line zero, at `85.70`. So Theorem 2's
hypothesis can never hold where D is indefinite. In Lean, D would need `|c_n|` in `schur_comb`,
and the resulting constant is then genuinely larger than the untwisted norm.

**Surgered Euler factor at `p0 > e^{2L}`.** It has the same window form as zeta but off-line
zeros at every height. The hypothesis of Theorem 2 fails for it. The implication runs from
verified zeros to the window, never back.

**Circularity.** Positivity at one fixed `L` is not RH-equivalent: D is positive for
`L < 1.717`. The hypothesis is a finite verification, and the conclusion is a fixed-window
almost-positivity.

---

## 6. Verdicts on the idea's statements

| # | idea's claim | verdict here |
|---|---|---|
| 1 | form-level bound, twist invariance, sharpness | bound and twist invariance: **THEOREM-kernel-checked** in continuous x-space form, not only the finite core. Sharpness (Kronecker plus modulation): THEOREM-paper-proof, not formalized. |
| 2 | Theorem 1, general `omega` | THEOREM-paper-proof, correct. Kernel-checked for `omega == 1` (`weilForm_autocorr_ge_cert`). It is **not** Zhu's retracted `A_eff` substitution, which bounds the comb from below, and it is not symbol capping, since no pointwise minorant of `Psi_L` is claimed. Whether the reduced finite block is PSD remains open. |
| 3 | values of `A_win` | 2.3: **[11.0586, 11.1614], upper kernel-checked**. Others: exact-integer Python (table in section 3). |
| 4 | Theorem 2 | THEOREM-paper-proof, re-derived, with the `R`-margin correction. The gluing logic is **kernel-checked** on the E8 explicit formula. |
| 5 | instance at `T = 640000` | COMPUTED: `-10^-997` with the kernel constant, `-10^-1163` with the float constant. |
| 6 | exact positivity from `lambda_min(M_T) > eps` | CONJECTURE-with-evidence, unchanged, not built. |
| 7 | no-go and rate | (a) holds. (b) is proved only for methods that use a frequency-independent comb constant (sharpness); the reading "any method needs `T >= 2 pi e^{A_win}`" is HEURISTIC, scoped like Zhu's Thm 1.4. (c) is heuristic, with PNT-model evidence. The phrase "contradicts Zhu's Remark 1.6" is better stated as: "the `A_L -> A_win` gain comes from the window (uncertainty), not from phase non-alignment". Zhu's remark is about pointwise envelopes. |
| 8 | negative controls | consistent; the D twist excess is reproduced. |

---

## 7. What remains

1. **Formalize Theorem 2's three analytic inputs**, so that `weil_almost_pos_cert` becomes
   unconditional apart from the zero ladder. They are:
   * the multiplier `K` and its tail bounds, which are Fejer-power estimates;
   * the per-zero bound `|F(gamma)F(conj gamma)| <= 2 L e^L`, via `Zeta23.EF.paperFT_weilTest`
     and Cauchy-Schwarz;
   * an explicit `S(t)` bound.

   The zero ladder itself (`AllZeros_h640000`) lives on another toolchain island. It composes at
   the registry level, not by import.
2. **Exact positivity.** This needs a certificate that `lambda_min(M_T) > eps` on the
   Nyquist-scale block `T* = 2 pi e^{2L}`. The expected margin is `lambda*(2.25) ~ 10^-470`
   against `eps ~ 10^-997`.
3. **Tighter kernel constant.** `N = 1840` would bring the kernel constant to about 11.12, at
   about twice the kernel time. The idea's symbolic-breakpoint CW (11.084) would need
   sub-cell breakpoints in the checker. A kernel-checked *lower* bound, making the enclosure
   two-sided in the kernel, would need exact cell overlaps with interval-valued shifts; it is
   not done.
4. **The most promising use of the form-level constant is exact positivity through Theorem 1
   combined with Zhu's pipeline, not through the zeros** (CONJECTURE). At `L = 1.0` the
   one-stroke cutoff drops from `2 pi e^{A_L} = 2187` to about `2 pi e^{A_win + beta} ~ 60-100`.
   That is a Legendre block of roughly 150-200 modes at about 40 digits, the size of Zhu's own
   certified `L = 0.8` run. Such a certificate would extend certified exact positivity from
   support 1.6 to support 2.0, provided the reduced form stays PSD. Whether it does is not
   known: Zhu's "symbol capping" failure shows what happens when a replaced symbol reaches the
   frequencies where the minimal direction lives. The cutoff must sit several times above
   `T* = 2 pi e^{2L}`. Not attempted here.

---

## 8. Files

* `telperion/examples/rvm_bridge/lean/Crux/Crux2_verified_window.lean`: the Lean file (generated).
* `scripts/`:
  * `generic_part.lean`, `header.lean.part`: the hand-written Lean;
  * `build_lean.py`, `emit_instance.py`, `emit_lean.py`: the generators;
  * `logbounds.py`: rational `log p` enclosures, computed exactly as the Lean proves them;
  * `cert_gen.py` (the Lean-mirror integer checker) and `cert_fast.py` (the certificate
    optimizer);
  * `eps_rigorous.py`, `psi0_check.py`, `twist_dh_check.py`, `pnt_check.py`, `schur_grid.py`.
* `certificates/`: `cert_L23_N920.json` (the one in the Lean file) and the Python-only
  certificates for 2.25, 2.05 and 1.4666.
* `outputs/`: every run log, plus `lean_check_output.txt`.
* Working notes: `/private/tmp/claude-0/crux2/verified-window/NOTES.md` (the BUILDER PASS section).
