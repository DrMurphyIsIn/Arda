# Blind read-back testimony: `RH_bl_explicit_formula` (roadmap B7-ii)

**Auditor:** independent blind read-back, 2026-09-18. No author context; own derivation completed
before the design memo was opened.
**Target:** node `RH_bl_explicit_formula`, worktree `/Users/peterwmurphy/arda-b7`, branch
`rh/b7-ef-statement`.
**Files read:** `telperion/missions/rh/nodes/RH_bl_explicit_formula.toml`,
`telperion/missions/rh/lean/Statements/RH_bl_explicit_formula.lean`, the `BombieriLagarias` block
of `telperion/missions/rh/lean/Statements/RHDefs.lean`, then (afterwards)
`telperion/docs/B7_BL_EXPLICIT_FORMULA_DESIGN_2026-09-18.md`.
**Island:** built green at `leanprover/lean4:v4.34.0-rc1` / Mathlib `de5ce8a9`
(`lake build`, exit 0). No registry file was modified. Probe files were created under
`Statements/` and deleted afterwards; `git status` is clean.

---

## Verdict

**CLEAN.** No Lean edit is required.

The registered statement is the correct classical Bombieri-Lagarias / Li claim, with every
normalisation, sign and factor right; it is non-vacuous and not trivially closable in Lean; the
`0 < n` hypothesis is load-bearing and I proved that in Lean; the summability design decision
(symmetric-window `Tendsto` rather than `HasSum`) is the only correct one and the `HasSum`
alternative would indeed be false rather than vacuous.

Two **documentation errata** and one **consumer-composition caveat** are recorded below. None of
them touches the theorem statement, so they do not change the verdict. The first erratum lives in
a generated registry comment and is worth fixing before promotion.

---

## 1. My independent derivation (done before reading the memo)

### 1.1 Zero side

Li's kernel is `H_n(s) = 1 - (1 - 1/s)^n`. Expanding the generating function directly:

```
Sum_{n>=1} lambda_n z^{n-1} = Sum_rho Sum_{n>=1} [1 - (1-1/rho)^n] z^{n-1}
```

With `w = 1 - 1/rho` the inner sum telescopes to `(1-w)/[(1-z)(1-wz)] = 1/[(1-z)(rho(1-z)+z)]`.
Substituting `s = 1/(1-z)` (so `z = 1 - 1/s`, `ds/dz = s^2`) this is `s^2/(s + rho - 1)`.
Reindexing `rho -> 1 - rho`, which the zero multiset admits, gives

```
Sum_{n>=1} lambda_n z^{n-1} = s^2 * (xi'/xi)(s) = d/dz [ log xi(1/(1-z)) ],   s = 1/(1-z).
```

So `lambda_n = n * [z^n] log xi(1/(1-z))`. **The reindex `rho -> 1 - rho` is the load-bearing
step, and it is legitimate only in an order closed under that involution**, which is exactly
what the symmetric window `|Im rho| <= T` provides. This is precisely the reason the author
gives, and it is the right one.

### 1.2 Arithmetic side, term by term

`xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s)`, hence

```
xi'/xi(s) = 1/s + 1/(s-1) - (1/2) log pi + (1/2) psi(s/2) + zeta'/zeta(s).
```

Multiply each piece by `s^2` and take `[z^{n-1}]` with `s = 1/(1-z)`, `s - 1 = z s`,
`[z^{n-1}] z^m (1-z)^{-(m+2)} = C(n, m+1)`:

| piece of `xi'/xi` | contribution to `lambda_n` | matches |
|---|---|---|
| `1/s` | `s^2/s = 1/(1-z)`, coefficient `1` | the leading `1` of `archSide` |
| `-(1/2) log pi` | `-(log pi / 2) * n` | `-(n/2) log pi` |
| `(1/2) psi(s/2)`, constant term `psi(1/2) = -gamma - 2 log 2` | `-(n/2)(gamma + 2 log 2)` | rest of the `-(n/2)(gamma + log pi + 2 log 2)` factor |
| `(1/2) psi(s/2)`, order `m >= 1`, using `psi^(m)(1/2) = (-1)^{m+1} m! (2^{m+1}-1) zeta(m+1)` | `(-1)^j C(n,j) (1 - 2^{-j}) zeta(j)`, `j = m+1` | the `Finset.Icc 2 n` sum, exactly |
| `1/(s-1) + zeta'/zeta(s) = -Sum_j eta_j (s-1)^j` | `-Sum_{j=0}^{n-1} C(n, j+1) eta_j` | `finiteSide n = -Sum_{j=1}^n C(n,j) eta_{j-1}`, exactly |

The pole of `1/(s-1)` and the pole of `zeta'/zeta` at `s = 1` cancel against each other before any
coefficient is taken; that cancellation is what the `eta_j` encode, and it is why there is no
separate pole term. **Every sign and every factor in the registered `archSide` and `finiteSide`
matches my derivation with nothing left over.**

Sign convention check: `zeta'/zeta(s) = -1/(s-1) + gamma + O(s-1)`, so
`-zeta'/zeta(s) - 1/(s-1) = -gamma + O(s-1)`, i.e. `eta_0 = -gamma`. That is the convention the
node uses and the value the `Function.update` installs.

Closed-form sanity at `n = 1`: `archSide 1 + finiteSide 1 = 1 - (gamma + log 4pi)/2 + gamma
= 1 + gamma/2 - (1/2) log 4pi = 0.0230957...`, the published `lambda_1` (Keiper 1992 / Li 1997).
I proved this reduction **in Lean**, see probe P7.

### 1.3 Numerical confirmation, computed independently

`mpmath` 1.3.0 at 80 digits. `lambda_n` computed from Li's generating function
`lambda_n = n * [z^n] log xi(1/(1-z))` by contour Taylor extraction (radius 0.3), with no
reference to the author's closed form; `eta_j` by contour Taylor extraction of
`-zeta'/zeta(1+z) - 1/z`; `archSide`/`finiteSide` transcribed literally from the Lean source.

```
eta_0        = -0.577215664901532860606512090082
-gamma       = -0.577215664901532860606512090082

 n | lambda_n (Li gen.fn)          | archSide+finiteSide           | |diff|
 1 | 0.02309570896612103381431     | 0.02309570896612103381431     | 1.878e-81
 2 | 0.09234573522804667038573     | 0.09234573522804667038573     | 5.535e-81
 3 | 0.2076389205543248037915      | 0.2076389205543248037915      | 3.163e-81
 4 | 0.3687904794922416385905      | 0.3687904794922416385905      | 1.265e-80
 5 | 0.5755427144611774524311      | 0.5755427144611774524311      | 3.268e-80
 6 | 0.827566012282379297425       | 0.827566012282379297425       | 2.214e-80
 7 | 1.124460117570959490583       | 1.124460117570959490583       | 5.06e-80
 8 | 1.465755677147060632656       | 1.465755677147060632656       | 8.434e-81
```

Agreement at `1e-80`, eight orders of magnitude tighter than the memo's `1e-39`. Individual terms
of `S_inf(n)` are of order `n` while the totals are of order `1e-2` at small `n`, so any wrong
sign or factor would be visible at order one. It is not.

---

## 2. Check 1 - Li's kernels, test class, summability

**Test class.** `H_n` is rational with a pole of order `n` at `s = 0` and `H_n(s) ~ n/s` at
infinity. On the critical line `s = 1/2 + ir` it decays only like `n/|r|`. Its prime-side partner
under the Weil pairing `H(s) = Integral g(u) e^{(s-1/2)u} du` is supported on `u < 0`, has a jump
at `0`, and decays like `e^{-|u|/2}`. I verified the `n = 1` case by hand: `Integral_{-inf}^{0}
e^{u/2} e^{(s-1/2)u} du = 1/s = H_1(s)` for `Re s > 0`, so `g_1(u) = e^{u/2} 1_{u<0}`, consistent
with the claimed `g_n(u) = e^{u/2} L^{(1)}_{n-1}(-u) 1_{u<0}` since `L^{(1)}_0 = 1`. The jump is
the `1/|r|` decay, and the `e^{-|u|/2}` decay is exactly borderline against the `Lambda(k)/sqrt k`
weight. **`g_n` is in neither the E8 class (`C_c^infinity`) nor the Guinand class. Confirmed.**

**Non-summability.** `|m(rho) H_n(rho)| ~ n/|gamma|`, and `Sum_{0<gamma<=T} 1/gamma ~
(log T)^2/(4 pi)` from `N(T) ~ (T/2pi) log T`. In a finite-dimensional space unconditional
summability is absolute summability, so `HasSum` for this family is **false**, not vacuous. This
is exactly the FLAG the brief told me to hunt for, and the statement does **not** use `HasSum`.
Measured over the first 400 conjugate pairs (`T = 679.74`, `n = 1`):

```
K=  25  sum |kernel| = 1.100     K= 100  2.062     K= 400  3.459
```

growing like `(log(T/2pi))^2/(2 pi) = 3.49`. Divergent as claimed.

**One-sided windows diverge.** Measured imaginary part of the one-sided sum against the predicted
`-(log(T/2pi))^2/(4 pi)` for `n = 1`:

```
 K     T        Im(partial)     predicted
 25    88.81    -0.55014        -0.55825
100   236.52    -1.03099        -1.04753
400   679.74    -1.72933        -1.74580
```

Agreement to about 1 percent, converging. The author's stated asymptotic is right including the
`log(T/2pi)` shift and the `n` factor.

**Symmetric windows converge.** They are real (imaginary part exactly 0, conjugate pairing) and
increase to `lambda_n`. The residual at `T = 679.74` is exactly the predicted tail, see section 6.

**Conclusion:** the `Tendsto`-over-symmetric-windows shape is not a stylistic choice, it is the
only true one. No flag.

---

## 3. Check 2 - arithmetic side, signs, Gamma contribution, pole terms

Covered term by term in section 1.2. Summary of what I checked and found correct:

- The `1` is the residue contribution of the `1/s` factor of `xi` (the trivial pole at `s = 0`),
  equal to `Sum_{j=1}^n C(n,j)(-1)^{j-1} = 1` for `n >= 1`.
- The `-(n/2) log pi` comes from `-(1/2) log pi` and nothing else; the archimedean `Gamma`
  contribution splits into `psi(1/2) = -gamma - 2 log 2` (giving the `gamma + 2 log 2` inside the
  same `(n/2)` bracket) and the derivative tower
  `psi^(m)(1/2) = (-1)^{m+1} m! (2^{m+1} - 1) zeta(m+1)`, giving exactly
  `(-1)^j C(n,j)(1 - 2^{-j}) zeta(j)` after `j = m+1`. The factor `(1 - 2^{-j})` is
  `(2^j - 1) 2^{-j}` and the `1/2` in `(1/2) psi(s/2)` combines with the `2^{-m}` from
  `((s-1)/2)^m` to produce it. I re-derived this rather than trusting it; it is right.
- `gamma + log pi + 2 log 2 = gamma + log 4pi`, the form in which Bombieri-Lagarias state it.
- **No separate pole term appears, correctly.** The pole of `1/(s-1)` in `xi'/xi` and the pole of
  `zeta'/zeta` at `s = 1` cancel, and the residual analytic data is exactly the `eta_j`. Writing a
  pole term as well would double-count.
- **The naive prime sum genuinely diverges.** `Sum_k Lambda(k) P_n(-log k)/k` has leading term
  `Sum_{k<=x} Lambda(k)/k ~ log x`. The residue form is therefore not a convenience, it is forced.

No sign or factor error found.

---

## 4. Check 3 - multiplicity, index set, pairing

**Weight.** `WeilExplicit.zeroMult rho` is `(MeromorphicOn.divisor riemannZeta {s | 0 < s.re
and s.re < 1}) rho |>.toNat`, the same divisor expression as `RvMCount.zetaZeroCount`. On the open
strip `s(s-1)` is nonzero and `Gamma(s/2)` is nonzero with no poles, so the order of `zeta` at
`rho` equals the order of `xi` at `rho`. That is the multiplicity Hadamard/`xi'/xi` uses. Correct.

**Index set.** `{rho | 0 < rho.re and rho.re < 1 and |rho.im| <= T}` is the open strip
intersected with a symmetric horizontal window. It contains non-zeros, but `zeroMult` vanishes
there, so the `finsum` support is exactly the window zeros. The support is finite (a true fact,
not an assumption), so the `finsum` is the honest sum and not its junk value. `rho = 0` and
`rho = 1` are outside the strip, so the `1/rho` junk value never fires.

**Pairing.** The window is closed under **both** `rho -> conj rho` (conjugate symmetry of `zeta`)
and `rho -> 1 - rho` (functional equation), with multiplicity preserved in both cases. Either
pairing makes the summand `O(1/gamma^2)`:

- `1/rho + 1/conj rho = 2 Re rho / |rho|^2`, bounded numerator;
- `1/rho + 1/(1-rho) = 1/(rho(1-rho))`.

The author's stated reason is the `rho -> 1 - rho` closure. That is the correct one to cite,
because it is the involution my derivation actually uses to turn `Sum s^2/(s + rho - 1)` into
`s^2 xi'/xi(s)`. The classical statement (Li 1997; Bombieri-Lagarias 1999, section 1) is
`lim_{T -> infinity} Sum_{|Im rho| <= T}`, which is what is registered. **The pairing matches the
classical statement and the limit exists for the reason given.**

---

## 5. Check 4 - vacuity and triviality in Lean (probe results)

All probes elaborated against the built island with `lake env lean`. Exact outcomes:

### Trivial-close attempts on the full statement

| tactic | result |
|---|---|
| `simp [six defs]` | `simp made no progress` |
| `simp_all` | `simp_all made no progress` |
| `aesop` | `aesop failed, made no progress` |
| `norm_num` | unsolved goals |
| `trivial` | `assumption` failed |
| `exact tendsto_const_nhds` | typeclass instance stuck (type mismatch) |
| `unfold ... ; simp` | unsolved goals |
| `apply tendsto_of_tendsto_of_tendsto_of_le_of_le` | no `OrderTopology C` |
| `decide` | expected type contains free variables |

Nothing closes it.

### Degenerate `n = 0` (the `hn` hypothesis is load-bearing)

Proved in Lean, sorry-free:

```lean
example (rho : C) : liKernel 0 rho = 0 := by simp [liKernel]
example (T : R) : liZeroSum 0 T = 0 := by simp [liZeroSum, liKernel]
example : archSide 0 + finiteSide 0 = 1 := by simp [archSide, finiteSide]
example : not (forall n : N, Tendsto (liZeroSum n) atTop
    (nhds (archSide n + finiteSide n))) := ...   -- closed via tendsto_nhds_unique
```

So the statement **without** `0 < n` is provably FALSE, and `hn` is real content rather than
decoration. The admissible class `{n | 0 < n}` is nonempty, so the statement is not vacuous.

### Junk-value audit of `eta`

`Function.update` at the single point `s = 1` is the correct device here: the un-updated function
is analytic on a punctured disc around `1` (a zero-free neighbourhood of the pole), and the update
installs exactly the analytic extension's value, so `zetaLogDerivReg` agrees with the analytic
extension on a whole disc and `iteratedDeriv j _ 1` is the honest `j`-th derivative. Verified in
Lean:

```lean
example : zetaLogDerivReg 1 = -(Real.eulerMascheroniConstant : C)   -- closes by simp
example : eta 0 = -(Real.eulerMascheroniConstant : C)               -- closes by simp
example : Real.eulerMascheroniConstant != 0                          -- via one_half_lt_...
```

I also built the un-updated function and proved, in Lean, what would happen without the update:

```lean
theorem zeta_not_diff_one : not (DifferentiableAt C riemannZeta 1)   -- from riemannZeta_residue_one
example : rawReg 1 = 0                                               -- deriv junk => logDeriv junk
example : rawEta 0 = 0
```

### Other junk surfaces checked

- `zeroMult` is **not** simp-reducible to `0` (`simp` leaves
  `(MeromorphicOn.divisor riemannZeta {s | ...}) rho <= 0`). And a hypothetical junk collapse of
  `zeroMult` would make the statement **false** (`lambda_1 != 0`), not vacuously true, which is the
  safe failure direction.
- `riemannZeta 1` never enters: `archSide`'s sum runs over `Finset.Icc 2 n`.
- `finsum` on infinite support would give `0`; the support here is genuinely finite.
- `Tendsto` has a concrete limit, not a junk one.

### Parse pinning

Precedence and casts in `archSide`/`finiteSide` were pinned against hand-written closed forms and
close by `simp`:

```lean
example : archSide 2 = 1 - (g + log pi + 2 log 2) + (3/4) * riemannZeta 2
example : archSide 3 = 1 - (3/2)(g + log pi + 2 log 2) + (9/4) riemannZeta 2 - (7/8) riemannZeta 3
example : finiteSide 2 = -(2 * eta 0 + eta 1)
example : archSide 1 + finiteSide 1 = 1 + g/2 - (log pi + 2 log 2)/2
```

`1 - 1/(2:C)^j` parses as complex `1 - 2^{-j}` (not natural division), `(n : C)/2` is an explicit
cast, `Finset.Icc 1 n` with `eta (j-1)` never underflows the natural subtraction, and the
`1 - X + Sum` association is the intended one.

**Conclusion: non-vacuous, non-trivial, well-formed. No flag.**

---

## 6. Check 5 - consumers, and the exact seam to B7-i

B7-i (`RH_bl_finite_multiset`, status `proved`) is:

```lean
theorem bl_finite_multiset (S : Finset C) (h0 : 0 not-in S) (h1 : 1 not-in S)
    (hsym : forall rho in S, 1 - conj rho in S) :
    (forall n, 0 < n -> 0 <= (Sum_{rho in S} (1 - ((1 - 1/rho)^{-1})^n)).re)
      <-> forall rho in S, rho.re = 1/2
```

I verified the two algebraic bridges **in Lean**, sorry-free:

```lean
-- S1: rho -> 1 - rho swaps the two kernel bases
example (rho) (h0 : rho != 0) (h1 : rho != 1) : (1 - 1/(1-rho)) * (1 - 1/rho) = 1
-- S2: B7-i's own involution rho -> 1 - conj rho CONJUGATES the base
example (rho) (h0 : rho != 0) (h1 : rho != 1) :
    (1 - 1/(1 - conj rho)) * conj (1 - 1/rho) = 1
-- S3: hence over such an S the B7-i summand is the conjugate of the B7-ii summand,
--     so exactly the REAL PARTS agree
```

**Named seams, in order of severity.**

1. **Order-of-quantifiers seam (the important one, and the one the memo states only softly).**
   B7-i gives, for each fixed finite window `S_T`, an `n` depending on `T`. B7-i's own nonvacuity
   record says explicitly that *no bounded universal `n` exists* (the first negative index grows
   without bound as points approach the line). So an off-line zero yields a negative window sum at
   index `n_T`, with `n_T -> infinity` as `T -> infinity`, and **this does not descend through the
   limit to `lambda_n < 0` for any fixed `n`**. Consequence: B7-i plus B7-ii compose in the easy
   direction (RH implies `lambda_n >= 0`, since every window is on-line so every window sum has
   nonnegative real part and the limit inherits it) and **do not** compose in the hard direction
   without a uniform-in-`T` quantitative input. That input is precisely the effective truncation
   bound `|liZeroSum n T - lambda_n| <= C n^2 log T / T` which the memo queues (section 2.1, and
   decision 4 of section 9) and does not register. B10 cannot close Li's criterion from these two
   nodes alone. This is not a defect in B7-ii; it is the thing the integrator should not assume is
   already bought.

2. **Multiplicity seam.** B7-i quantifies over a `Finset C`, one weight per point; `liZeroSum`
   carries `zeroMult`. They coincide only if every window zero is simple, which is open. Either
   B7-i is lifted to multisets (Bombieri-Lagarias Theorem 1 is stated for multisets) or the
   consumer carries a simplicity hypothesis. The author records this in the node header and in
   memo section 4.1, and does not paper over it. Correctly flagged, not fixed.

3. **Representation seam (not stated anywhere I found).** `liZeroSum` is a `finsum` over a
   *set*; B7-i takes a `Finset`. Converting one to the other requires a proof that the window
   support is finite **and** an explicit `Set.Finite.toFinset` bridge. Window finiteness is a
   theorem the node does not assert and does not import. Cheap, but it is an obligation, and it is
   the same obligation `RvMCount.zetaZeroCount` already carries.

4. **Kernel-form seam.** Handled: S1/S2 above. Note that closing it needs **two** distinct
   symmetry facts with matching multiplicity, conjugation *and* the functional equation, not one.

**On the E8 dependency.** `depends_on` lists `RH_limit_explicit_formula`, while the node header
says the E8 statement is not applicable to this class. The dependency is real but it is vocabulary
and shared inputs (`WeilExplicit.zeroMult`, `RH_corridor_bound`, `RH_rvm_unconditional`), not
logical consumption. That is stated honestly in the header; I record it so the graph is not
misread as "B7-ii follows from E8".

---

## 7. Did the memo change anything?

No. The memo's derivation (its section 3) is the same computation I did independently, reaching
the same closed form by the same route, and its vacuity table (section 6) overlaps my probe list.
It is a careful document and it does not oversell: `conjecture1_proved = False` is stated, the node
is `draft`, the statement carries the by-design `sorry`, and the hard parts of the proof route
(sections 7.3 and 7.5) are named as the serious work rather than hand-waved.

Reading it surfaced two errata it shares with the registry comments.

### Erratum 1 (registry comment, worth fixing before promotion)

`RHDefs.lean`, `BombieriLagarias` block, and memo section 6 both say that without the
`Function.update` "every `eta_j` with `j >= 1`" would be `0` and the statement would be false
"for `n >= 2`".

That understates it. I proved in Lean that the un-updated function evaluates to `0` at `s = 1`,
so **`eta_0` would be `0` as well**, giving `finiteSide 1 = 0` instead of `gamma`, and the
statement would already be false at **`n = 1`** (`archSide 1 = 1 - (gamma + log 4pi)/2 =
-0.554` against `lambda_1 = +0.023`).

The comment is a comment, so the theorem is unaffected. The block is generated, so the fix belongs
in `telperion/missions/rh/build_rhdefs.py`, in the `BOMBIERI_LAGARIAS_BLOCK` literal, followed by
regeneration. Suggested replacement for the clause

```
-- would make every eta_j with j >= 1 equal to 0 and the statement FALSE for n >= 2.
```

with

```
-- would make every eta_j equal to 0 (eta_0 included: -logDeriv riemannZeta 1 - 1/(1-1) = 0,
-- since riemannZeta is not differentiable at 1 so deriv returns the junk value 0) and the
-- statement FALSE already for n = 1 (finiteSide 1 = 0 instead of gamma).
```

The same sentence appears in the node header comment of
`Statements/RH_bl_explicit_formula.lean` in the shorter form "`eta_0 = -gamma`; the extension at
`s = 1` is pinned by Mathlib's `tendsto_riemannZeta_sub_one_div` so `iteratedDeriv` sees no junk",
which is accurate as written and needs no change.

### Erratum 2 (memo only, internal inconsistency)

Memo section 5 says the residual of the truncated symmetric window is "the leading tail
`Sum_{gamma>T} n/gamma^2 ~ 0.0016 n`". The correct law is `n^2`, not `n`, and the memo's own
section 2.1 states it correctly as `O(n^2/gamma^2)`. The error hides at `n = 1`, where the two
agree, which is the only case section 5 checks. Measured at `T = 679.74` over 400 ordinate pairs,
with `Sum_{gamma>T} 1/gamma^2` predicted as `(log(T/2pi)+1)/(2 pi T) = 0.00133081`:

| n | actual gap `lambda_n - window sum` | `n * tail` | `n^2 * tail` |
|---|---|---|---|
| 1 | 0.0013295 | 0.0013308 | 0.0013308 |
| 2 | 0.0053181 | 0.0026616 | 0.0053233 |
| 3 | 0.0119658 | 0.0039924 | 0.0119773 |
| 4 | 0.0212725 | 0.0053233 | 0.0212930 |

The `n^2` law matches to four significant figures at every `n`; the `n` law is wrong by a factor
of `n`. The reason is that on the line `|1 - 1/rho| = 1`, so the paired term is
`2(1 - cos(n theta))` with `theta ~ 1/gamma`, giving `n^2/gamma^2`. This matters because the
effective truncation bound is what B10's tail budget consumes, and section 2.1's `n^2` form is the
one to carry forward.

---

## 8. What I did not verify

- I did not attempt any proof, and I offer no opinion on whether the memo's section 7 route
  closes. Steps 3 and 5 there (an order-`n` pole against `Lambda'/Lambda` in the rectangle
  identity, and the digamma derivative tower) are genuinely new contour work, not engineering.
- I did not check the regularized prime-sum representation of `eta_j` (memo section 2.4). It is
  deliberately excluded from the statement, which I agree with: for `j >= 1` its existence is PNT
  with an error term, a different theorem.
- I did not re-run `mission verify rh` or check the generated `sha256` header; promotion mechanics
  are the integrator's gate.
- I did not audit `RH_bl_finite_multiset`'s proof, only its statement, in order to name the seam.

`conjecture1_proved = False`. Nothing in this node is evidence for or against RH; it registers a
classical 1999 identity as an unproved statement.
