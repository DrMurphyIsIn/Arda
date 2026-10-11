# The sextic bottleneck in OpenAI's 7/8 argument: what the constant 6 is, and what would have to change (2026-10-11)

Companion to `OAI_QRH_METHOD_MAP_2026-10-10.md` (sections 1, 4, 5) and `telperion/research/qrh_stage3/`.
Bounded exploration of the one lever that section 5 of the map identified. Nothing here is a result; it is
an accounting of where the method's boundary comes from, done against the paper's LaTeX source
(openai/math, preprint `The-Quasi-Riemann-Hypothesis-September-30-2026`, `build/paper.tex`, 16,677 lines;
the October 5 preprint `paper2.tex` is the simplified 11/12 version). `conjecture1_proved = False`; nothing
here touches `Lambda = 0`.

## 1. Restating the boundary

Section 5 of the map established, inside the paper's own exponent system, that 7/8 is pinned from below:

    sigma0  >=  1 - h/6 + b/12,     h = (1 + b + 3 ell)/2,     6 ell <= 1        =>   sigma0 >= 11/12 - ell/4 >= 7/8,

with equality at the paper's point, while the high side (the row-exponent system of section 20) has about
0.01 of room. The map's closing line was that "all three levers are the sextic 1/6 in different clothes".
That sentence was too quick. Reading section 15 of the source separates three different sixes.

## 2. Three sixes, two of them sextic

| constant | where it enters | origin in the source | sextic? |
|---|---|---|---|
| `h/6` in `C(sigma0) = sigma0 + l_x/2 - 1 + h/6` | the normalization every exponent is measured against (Lemma 10.4, l. 6139-6150) | the scalar factor `zeta_F^S(6 z_0)`: the principal row sum over SIXTH-POWER rows `u = a^6` is a Dirichlet series in `6 z_0` | yes: `6` = order of the symbol / power of the rows |
| `b/12` in the low estimate `Z^{l_x/2 + b/12}` | Prop. 15.2 (quantitative Gram bound), l. 8540-8560 | the count of `a_1` with `q_{a_1} <= K_R^{1/6}`: a SIXTH-ROOT count, giving `P_a^{1/6}` and after the square root `P_a^{1/12}` | yes: sixth roots |
| the slot cap `6 ell <= 1` | Lemma 15.1 (compensated completed-row norm), l. 8300-8320 | the row-energy algebra `1 + 3 ell' - 2 M'` with `M' = 1 - ell - 2d`, `ell' = ell - d`: the exponent is `M' + ((5 ell - 1 + d)/4)_+`, and it must vanish for all `0 <= d <= ell`; at `d = ell` this is `6 ell <= 1` | NO: the `3` is the CUBE in the rows `c n^3` (Patterson's cubic theta), the `2` is the mean square; the symbol order does not appear |

So the slot length cap is cubic-plus-mean-square, and the two constants that set the LAW are sextic. Writing
`k` for the power of the rows / order of the symbol and keeping the cubic-energy cap, the law would read

    sigma0_low(k)  =  1 - h/k + b/(2k)  =  1 - (1 + 3 ell)/(2k)      (b cancels as before),

and at the cap `ell = 1/6`:

| k | sigma0_low(k) | Lambda <= 2(sigma0 - 1/2)^2 | note |
|---|---|---|---|
| 6 | 7/8 = 0.8750 | 9/32 = 0.2813 | the paper |
| 5 | 17/20 = 0.8500 | 0.2450 | |
| 4 | 13/16 = 0.8125 | 25/128 = 0.1953 | beats Platt-Trudgian's 0.2 |
| 3 | 3/4 = 0.7500 | 1/8 = 0.1250 | |
| 2 | 5/8 = 0.6250 | 1/32 | meaningless: quadratic theta functions are the classical theta function, and this architecture does not exist for them |

## 3. The high side does not object (heuristic)

`telperion/research/qrh_stage3/kmodel_heuristic.py` takes `stage3_search.model` and replaces every constant that
section 15 and section 20 derive from sixth powers by its `k`-analogue (`h/6 -> h/k`, `b/12 -> b/(2k)`,
`h (z_0 - 1/6) -> h (z_0 - 1/k)`, plain capacity `1/(6 kappa) -> 1/(k kappa)`), keeps the cubic cap
`6 ell <= 1`, and leaves every other constant of section 20 (17/50, 2/3, 76/75, 51/100, 7/37) as the paper
has it, because their dependence on `k` was not traced. It is a screen, not a model. Its output:

- sanity: `k = 6` at the paper's point reproduces `E_max = -7/1200`, `C-low = 0`;
- at `sigma0 = sigma0_low(k)`, `ell = 1/6`, the high side closes for `k = 5, 4, 3` with MORE margin than at
  `k = 6` (`E_max` = -0.013, -0.015, -0.019 against -0.012 with the same Stage-III-style input), because the
  term `h (z_0 - 1/k)` becomes more negative as `k` falls;
- for `k = 4` the high side tolerates every `sigma0` from 13/16 upward.

So, inside the screen, the entire boundary is the low-side law, and the law is the symbol order. This
corrects section 5 of the map on one point: raising `ell` past 1/6 at `k = 6` fails on the high side
(that finding stands), but changing `k` is a different move and the high side has nothing to say about it.
The question is therefore entirely whether an apparatus with `k = 4` or `k = 3` exists.

## 4. Where the 6 comes from, structurally

(Filled from the source by a reading pass; see section 6 for what the paper says and what is inference.)

The twist is `chi_n(u) = (u/n)_6` and the rows are `u a^6`. Patterson's cubic theta function has Fourier
coefficients that are cubic Gauss sums, with twisted multiplicativity in the CUBIC residue symbol; that is
the `3`. The reflection side works with a quadratic mean square (the Goldmakher-Louvel / BGL "paired residue
characters" large sieve, specialized to the sextic case in the paper's Lemma `sextic-large-sieve`); that
pairing supplies the `2`. The sextic character is the product, and "at each good prime the sextic residue
character has exact order six, since the residue multiplicative group is cyclic" (l. 4807). So `6 = 3 x 2`:
the cubic structure of the theta function times the quadratic structure of the mean square.

## 5. What would have to be true for k = 4 or k = 3

- `k = 3` (cubic rows and cubic symbol, no quadratic factor): the mean-square step would have to be run
  against a CUBIC large sieve rather than a quadratic one. Heath-Brown's cubic large sieve (2000) exists and
  the paper already cites "Heath-Brown's cubic estimate" for another purpose, so the question is whether the
  quadratic pairing on the reflection side is essential to the theta transformation or only to the sieve.
  This is the question the reading pass in section 6 addresses.
- `k = 4` (quartic rows, quartic symbol): would need a quartic analogue of Patterson's theory, i.e. theta
  functions on the 4-fold metaplectic cover with Fourier coefficients given by quartic Gauss sums. As far as
  this author recalls, this is exactly where the subject stops: Kazhdan-Patterson showed that for covers of
  degree n >= 4 the Fourier coefficients of the theta function are NOT determined by Gauss sums (the
  "theta function problem"; Patterson's conjectures, partial results for n = 4 by Suzuki and by
  Eckhardt-Patterson). If that recollection is right, `k = 4` is blocked by an open problem in the theory of
  metaplectic forms, not by an estimate. This needs checking against the literature before it is repeated.

In the model's terms: `k = 3` would give `sigma0 = 3/4` and `Lambda <= 1/8`, `k = 4` would give 13/16 and
`Lambda <= 25/128 < 0.2`. Both are far beyond anything a Stage III could do at `k = 6` (section 5 of the map:
at most about 0.01).

## 6. Reading pass on the source (what the paper says)

PENDING: filled in from `SEXTIC_ORIGIN_REPORT.md` when the reading pass completes.

## 7. Verdict

The sextic bottleneck is real and it is the symbol order, not a tuning constant: the low-side law is
`1 - (1 + 3 ell)/(2k)` with the cubic cap `ell <= 1/6`, and the high side would accept any `k`. Lowering `k`
is therefore the one move that would change the constant by more than a hair, and it is a question about
metaplectic theta functions, not about this exponent system. It is not something Telperion can certify;
it is something to put to a number theorist who works on higher-order Gauss sums. Until then, 7/8 stands,
`0 <= Lambda <= 9/32` is the kernel-checked picture, and `Lambda = 0` is untouched.
