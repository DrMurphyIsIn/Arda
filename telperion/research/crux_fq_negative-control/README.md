# crux_fq_negative-control: Fourier-quasicrystal properties against the control zoo

`conjecture1_proved = False`. Nothing in this directory, or in the Lean file it describes, says
anything about where the zeros of the Riemann zeta function lie. No claim here is a step toward RH.

## The question

This round's lead was the Fourier-quasicrystal (FQ) literature, set against round 1's Theorem A.
Theorem A is a rigidity statement about zeta's coefficient side. It says the positive measure
whose Dirichlet transform satisfies zeta's exact functional equation is the integer comb. The FQ
literature proves reality and rigidity theorems for measures whose Fourier transform is again a
measure. The papers are Lev-Olevskii, Kurasov-Sarnak, Olevskii-Ulanovskii, Alon-Cohen-Vinzant,
Favorov, Meyer and Bondarenko-Radchenko-Seip. So the natural hope was an FQ-type property of
zeta's Guinand-Weil pair: the zero measure on one side, and prime-power atoms plus an archimedean
density on the other. That property would hold for zeta and force the zeros onto the line.

The negative-control seat tested that hope in the only way that can kill it. Take every FQ-type
property and ask whether it separates zeta from the program's controls:

- Davenport-Heilbronn (DH);
- the Epstein zeta of x^2 + 5y^2;
- the golden fake over F_5;
- the surgered zeta W1;
- the fooling-lemma zeta W2;
- the imaginary shift E_theta(s) = zeta(s + theta) zeta(s - theta).

Each control has a functional equation and a Dirichlet series, and each has zeros off its critical
line. Any property that holds for a control cannot force the zeros onto the line.

The verdict (seat notes: `/private/tmp/claude-0/crux-fq/negative-control/NOTES.md`) is that no such
lever exists. Every FQ-type property that separates zeta from all the controls is one of two things:

- RH_F itself: real support, temperedness of the Fourier-Laplace dual, Weil positivity, or
  Lee-Yang at finite rank;
- an arithmetic identification of zeta (P_min, or Selberg's class), whose reality statement is RH
  or GRH.

This directory holds the reproducible part of that verdict: a kernel-checked Lean file, Arb
certificates, and the mpmath computations.

## What the kernel checks

The file is `telperion/examples/rvm_bridge/lean/Crux/CruxFQ_negative_control.lean`. It has 2024
lines and lives on the rvm_bridge island (Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 fbdc36bb).
Its sha256 at the time of writing is `fa94d1d0...29c5d78`.

The check command is `lake env lean` run through the machine's lean-slot lock. It exits 0. It
prints 44 `#print axioms` lines, and every one is exactly `[propext, Classical.choice, Quot.sound]`.
The code contains no `sorry`, `admit`, `native_decide`, new `axiom` or `opaque`. The transcript is
`out/lean_axioms_transcript.txt`. Like the other Crux files, the file is untracked and is not in CI
or AxiomGuard.

The file tells six short stories.

**A. The dual weights exist, and one lemma tells you when they leave the prime powers.** The
prime side of a Guinand-Weil pair is the sequence Lambda_F of coefficients of -F'/F.
`exists_isLogDerivCoeff_of_bounded` proves that this sequence exists for every Dirichlet series
with a(1) = 1 and bounded coefficients. The proof uses Mathlib's Dirichlet inverse and a new
polynomial growth bound, `dirichletInverse_norm_le`. The two-prime lemma `LogConv.mul_primes`
proves Lambda_F(pq) = log(pq)(a(pq) - a(p)a(q)). So the dual has an atom at the non-prime-power
frequency log(pq) exactly when the coefficients fail to be multiplicative at (p, q).

**B. Davenport-Heilbronn's dual is signed and off the prime powers.** `dh_dual_values` and
`dh_dual_exists` prove two things. Every representation of -D'/D has
Lambda_D(2) = kappa log 2, Lambda_D(3) = -kappa log 3 < 0, Lambda_D(4) = -(2 + kappa^2) log 2 and
Lambda_D(6) = (1 + kappa^2) log 6 != 0, where 6 is not a prime power. And such a representation
exists. The FE of DH is not in the kernel: these are theorems about its coefficient sequence
(1, kappa, -kappa, -1, 0).

**C. W2: Lee-Yang is |a| <= 1, while being an Euler factor is a^2 = 1.** W2's finite factor is the
restriction of P_a(z, w) = 1 + a(z + w) + zw to a torus orbit. `LY2_leeYang_iff` proves that P_a
is Lee-Yang iff |a| <= 1. `LY2_factor_iff` proves that it splits as an Euler factor iff a^2 = 1.
`Ea_zero_re_of_leeYang` proves that for |a| <= 1 every zero of E_a lies on Re s = 1/2. That holds
whether or not E_a is multiplicative.

`W2_LSeries_eq` identifies the coefficient sequence of W2 = zeta E_a. `W2_dual_defect` and
`W2_dual_exists` compute its atom at p1 p2: sqrt(p1 p2)(1 - a^2) log(p1 p2).
`W2_fooling_instance` treats a = 1 + 10^-4 at (101, 10007). That instance is neither Lee-Yang nor
Euler, and its atom there is negative. Numerically the atom is -2.7801354, which
`lean_crosscheck.py` reproduces.

This corrects the seat's claim 8, which said "Lee-Yang iff a = 1". The conclusion of claim 8
survives: a finite window of real zeros cannot certify Lee-Yang. The correction also sharpens the
table, because Lee-Yang (real-rootedness) at finite rank is strictly weaker than the Euler product.

**D. At finite rank, three FQ conditions are one condition.** Take the one-prime completed factor
Q_c(s) = p^{s-1/2} + c + p^{1/2-s}. `finite_rank_realZeros_iff_tempered_iff_leeYang` proves that
the following three conditions are each equivalent to |c| <= 2:

- all its zeros lie on the line;
- its normalized dual weights qw c k are bounded, which is temperedness;
- the roots of x^2 + c x + 1 lie on the unit circle, which is local Lee-Yang.

The golden fake is p = 5, c = sqrt 5. `golden_weights` gives its weights as (-1)^k (phi^k + phi^-k),
so they are unbounded. `golden_zero_re` puts its zeros exactly at Re s = 1/2 +- log phi / log 5.
`golden_count_pos` proves that its full formal-curve dual is nevertheless positive: the counts
5^k + 1 - alpha^k - beta^k = (1 - alpha^k)(1 - beta^k) are positive. So positivity of the full dual
does not rescue it. W1 is p = 29, c = 11/sqrt 29, and `W1_fails_finite_rank` shows that it fails
all three conditions.

**E. The imaginary shift, the control the arithmetic-FQ spec asked for.** E_theta = zeta(s+theta)
zeta(s-theta) is zeta's zero measure translated by +-i theta. On the dual side it has everything
zeta has:

- a self-dual entire completion xi(s+theta) xi(s-theta) with gamma factor
  Gamma_R(s+theta) Gamma_R(s-theta);
- dual weights Lambda(n)(n^theta + n^-theta) = 2 cosh(theta log n) Lambda(n), which are
  nonnegative, carried exactly by the prime powers, and decaying against sqrt n for |theta| < 1/2.

These dual-side facts are `XiTheta_one_sub`, `XiTheta_eq_completion`, the `LambdaTheta_*` lemmas,
`Etheta_logDeriv_hasSum` and `Etheta_isLogDerivCoeff`. The zero side is where it differs:

- `Etheta_offline_zeros`: E_theta has zeros off Re s = 1/2 above every height, unconditionally,
  with no Hardy input.
- `XiTheta_no_zero_on_line_of_RH`: under RH it has no zero on the line at all.
- `RH_iff_XiTheta_two_lines`: RH holds iff every zero of E_theta lies on Re s = 1/2 +- theta. So
  the control's correct "RH" is zeta's RH, translated.

Its Arb-free separation from zeta is the pole at 1 + theta (`Etheta_pole`), which sits to the
right of every zero (`XiTheta_zero_re_bounds`). `eisShift_violates_RH_analogue_unconditional`
discharges the `hzero` hypothesis flagged on the corpus scratch file (RH_CRUX_RESEARCH row 20). The
capstone for this section is `Etheta_shift_control`.

**F. Temperedness of the Fourier-Laplace dual is real support.** This is the mechanism of the
seat's claim 2. `dualSum_polyBounded_iff_real` takes finitely many points gamma_j in C with
positive multiplicities. It proves that x -> sum_j m_j e^{i gamma_j x} is polynomially bounded on R
iff every gamma_j is real. The proof takes Cesaro means of e^{-(d+it)n} times the sum along the
integers. No dual positivity, no Euler product and no conductor enter, which is why "FQ grade" read
as temperedness is a relabeling of real support for zeta and every control alike.

`negative_control_capstone` bundles A-F.

## What is Arb-certified (python-flint, not the Lean kernel)

`certify_offline_zeros.py` writes `out/certify_offline_zeros.json`. It uses segment-certified
winding numbers from `arb_winding.py`, a self-contained copy of the crux_dynamics-ergodic tool, at
200-bit precision. The run takes 11 seconds. It certifies the following:

- **New:** the Epstein zeta of x^2 + 5y^2 has a second off-line zero,
  0.9376669067003994 + 29.9833952351555 i. It is certified in the box (0.90, 0.97) x (29.95, 30.02),
  and the whole half-strip [0.52, 2] x [20, 30.85] holds exactly one zero. The corpus had certified
  only the zero near 15.668.
- **New:** W2's factor E_a with a = 1 + 10^-4 has off-line zeros near heights 162.6905, 164.0533
  and 165.4162. The FE partner of the first is certified as well.
- **New:** all 330 zeros of E_a with 1/10 < Im s < 150 lie on the line. The winding number of
  [-1/2, 3/2] x [1/10, 150] is 330, and there are 330 certified sign changes of the real function
  on the line. So these real zeros certify nothing about Lee-Yang.
- **Tool controls:** the corpus-certified Epstein zero at 15.668 and the DH zero at 85.699 are
  re-certified, and a control box gives winding 0.

## What is computed (mpmath, 30 digits, one process, not interval-certified)

`run_all.sh` re-runs the seat's Guinand-Weil checks one script at a time; outputs are in `out/`.
Every residual reproduces the seat's table:

| object | residual | note |
|---|---|---|
| zeta | 4.1e-29, 6.9e-32 | positive control |
| DH | 4.6e-29 | Dropping the off-line quadruple changes the residual by 4.0855. Using zeta's Lambda in place of Lambda_D leaves 0.4074. |
| W1 | 4.0e-18, -2.0e-31 | |
| W2 | 3.6e-17 | Argument-principle count 72 = 66 + 6. |
| Epstein x^2+5y^2 | 1.6e-15 | Count 21 = 17 + 2 + 2, which is how the second off-line pair was found. |
| golden fake | -2.0e-31 | Poisson identity. |
| E_theta | -2.4e-15 (theta = 0.2), -2.0e-31 (theta = 0.45) | |

`lean_crosscheck.py` evaluates every closed form the Lean file proves. It also checks the degree-2
segment of claim 5, which is not in Lean. For F_t = zeta_K + (2t-1) L(chi_-4) L(chi_5) with
K = Q(sqrt -5), the coefficients a_K(n) +- b(n) are nonnegative for n <= 10^4. The multiplicativity
defect at (2, 3) is c(1)c(6) - c(2)c(3) = 8(2t - 1), so only t = 1/2 (zeta_K) is multiplicative.
The normalization c_t(1) = 2t matters here.

## What stays paper-level

- Claim 2 for infinite zero sets (class C). Its proof goes through the Laplace transform and the
  identity theorem; the kernel has the finite-rank form.
- The functional equations of DH, W2 and Epstein, and every control's explicit formula. These are
  numerics only; zeta's own explicit formula is E6Bridge4.
- The ACV step "not Lee-Yang implies an off-line zero on the torus orbit". The certificates above
  replace it for a = 1 + 10^-4.
- Selberg's gamma-axiom failure of E_theta, Landau's pole shadow in general (claim 6), and
  Bondarenko-Radchenko-Seip (claim 7, a literature reading).
- The "P_min lever" analysis (claim 10), which is HEURISTIC as a lever: in degree one it is
  round 1's class P = {zeta}, so "P_min implies real support" is RH verbatim.

## Reproduce

```
cd telperion/examples/rvm_bridge/lean && <leanlock.sh> lake env lean Crux/CruxFQ_negative_control.lean
cd telperion/research/crux_fq_negative-control
./run_all.sh                      # about 20 min, one process at a time (Epstein is 12 min)
python3 certify_offline_zeros.py  # about 11 s, python-flint 0.6
python3 lean_crosscheck.py        # about 3 s
```

## Files

- `efcommon.py`, `ef_*.py`: the seat's Guinand-Weil checks, copied from the seat directory.
- `run_all.sh`: runs the checks in sequence.
- `arb_winding.py`: certified winding numbers.
- `certify_offline_zeros.py`: the Arb certificates.
- `lean_crosscheck.py`: numerical mirror of the Lean statements.
- `out/`: every output, timing, and the Lean transcript.
