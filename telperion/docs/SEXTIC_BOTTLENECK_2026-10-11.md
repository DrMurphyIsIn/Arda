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

## 4. Where the 6 comes from, structurally (the team ledger already has this)

The Riemann session's thread-C ledger, `~/rh-team/C/loss_ledger.md` (with `C/scripts/exact_bookkeeping.py`,
which re-derives 11/12 and 7/8 exactly), answers the question this note was heading toward, and section 5.2
of it should be cited rather than redone. In its terms:

- The identity `sigma0 = 5/6 + (M - 2 ell)/12 + excess/2` (b drops out), with `M` the reflected-energy
  length; the proved lemmas force `M + ell <= 1` and `2M >= 1 + 3 ell`, which gives the **13/15 floor** for
  proved inputs (at the triple point `ell = 1/5`, `M = 4/5`), and idealising everything except sixth-power
  sparsity gives the **5/6 = 1 - 1/k architecture floor**. Our law `1 - (1 + 3 ell)/(2k)` is the same
  bookkeeping with `M = 1 - ell` substituted (the paper's choice), and the two agree: 7/8 at `ell = 1/6`,
  13/15 at `ell = 1/5`.
- **Why k = 6 is forced (ledger section 5.2).** Two things must hold at once. (a) After Poisson summation the
  dual coefficients are `mu(n) gamma_{-1}(n)` with an order-k Gauss sum, and Mobius has to be absorbed into a
  Gauss sum with a known theta formula. For `k = 2m` the Hasse-Davenport duplication
  `gamma_{-1} gamma_{m-1} = (ray) gamma_{-2} gamma_m` does this; for `m = 3` it turns `mu(n) gamma_{-1}(n)` into a
  ray-class factor times the cubic Gauss sum `gamma_2(n)` (paper2.tex:322); for `m = 2`, i.e. `k = 4`, the
  relation degenerates to `|g|^2 = |g|^2` and carries no information; for odd `k` there is no quadratic
  character in the family and `mu` survives, which rules out `k = 3`. (b) The absorbed coefficient must be a
  theta coefficient with an explicit formula: Patterson's `c_theta(n b^3) = 3^{5/2} |b| chibar_n(lambda)^2
  gamma_2(n)` (paper2.tex:363). Explicit squarefree-index coefficients of the m-fold metaplectic theta on
  GL_2 are known only for `m = 2, 3` (Kazhdan-Patterson uniqueness of the Whittaker model; the ledger flags
  this as from memory, unchecked against a source; so does this note).
- **k = 2 is circular**, not sieve-limited: the dual family is again a Mobius sum twisted by quadratic
  characters, the only theta is the classical one whose transformation law is Poisson summation itself, and
  the needed bound including the square rows is equivalent to the conclusion. The cubic theta is what breaks
  the circularity (its residue is the sparse `X^{5/6}` term, Heath-Brown-Patterson).

So the "6" is `2 x 3` in a precise sense: the `2` is the quadratic character needed for Hasse-Davenport
duplication to absorb Mobius, the `3` is the only odd `m` for which the resulting Gauss sum is a theta
coefficient with a formula. Neither factor is a tuning choice.

## 5. What the k-general table in section 2 actually means

Read against section 4, the rows `k = 5, 4, 3, 2` of the table are counterfactuals, each blocked at a named
step: `k = 4` at the duplication identity (degenerate), `k = 3` and `k = 5` at the absence of a quadratic
character (Mobius survives), `k = 2` by circularity, `k = 2m` with `m >= 5` at the theta formula (and worse
sparsity). The heuristic screen of section 3 adds one honest fact to that: the high side of the argument
would not have objected to any of them. The boundary of the method is therefore located, to this note's
satisfaction, in two theorems about Gauss sums and metaplectic theta functions, not in the exponent system,
and not in any constant Telperion could certify or any geometry it could search.

## 6. Reading pass on the source (`SEXTIC_ORIGIN_READING_2026-10-11.md`, line references to paper.tex)

An independent reading pass over the September 30 source, done without the ledger, lands in the same place
and adds the mechanism on the reflection side:

- The sextic symbol is introduced at l. 628-631 with no motivation beyond `q_p = 1 mod 6`. The theta input is
  cubic (l. 1895-1900); its coefficients are cubic Gauss sums, `gamma_2 = (sextic Gauss sum)^2` (l. 1992-2001);
  the completed index is `c n^3`.
- The quadratic part is forced by the reflection formula: after reflecting a sextic twist of exponent `j`
  the local column factor is `chi^{-j-2}` (l. 1783-1789), so a squarefree row (`j = 1`) reflects to `chi^3`,
  the QUADRATIC symbol. The paper says so itself: "The reason for the quadratic sieve is already visible for
  squarefree rows ... `chi_R(nb)^3`" (l. 2848-2856), and then applies the Goldmakher-Louvel quadratic large
  sieve with its clean `U + V` bound (l. 2644-2650) to get reflected energy `Z^{1+eps}` (l. 2866-2871). A cubic
  twist would reflect to a cubic kernel and need the cubic large sieve, whose `(KD)^{2/3}` term gives
  `Z^{4/3}` at balanced lengths and breaks the low estimate. This is the reflection-side face of the ledger's
  Mobius-absorption argument: the sextic twist is exactly the twist that the cubic Gauss-sum reflection turns
  into a quadratic character.
- The paper contains no remark on the choice of order: no "quartic", "biquadratic", "Kazhdan", "metaplectic
  cover" beyond the citation line l. 121, no "other fields".
- Sextic-origin constants: `z = 1/6` (pole of `zeta_F^S(6z)` from rows `u a^6`, l. 3758, 4045, 6270),
  `q_p^{-5/6}` and `Z^{-ell/6}` (slot factor at `z = 1/6`, l. 15562-15583), `h/6` in `C(s)` and hence `2/3` in
  `C_I` and `11/16` in `C_II` (l. 6316, 8794), the Gram count `K^{1/6}` (valuations divisible by six,
  l. 8535-8545), the `4/3 - delta` Stage I row envelope (sextic sieve `(KD)^{2/3}`, l. 5192), `1 - 2 delta/3` and
  `alpha = 5/6` (sixth-power amplification `e(r) = max{1, (1+5r)/6}`, l. 12363-12395, 15103). Not sextic: the
  detector floor `51/100` (l. 4214) and `76/75` (bookkeeping so `R = 1` at `delta = 1/50`, l. 16148-16153).
  Uncertain: `17/50`, `7/37`, `1/(6 kappa)` (the paper says the `5M/6` threshold comes from "counting their
  sixth-power form", l. 12590-12595). The slot cap `ell = 1/6` comes from the cube plus the mean square
  (l. 8300-8320), as section 2 says, with one caveat the reading pass adds: the "3" there is the THETA order,
  so with a k-th order theta the cap itself would move; section 2's table holds the cap fixed and is to that
  extent conservative or wrong in a direction that does not matter, since every row except `k = 6` is blocked
  anyway (section 5).
- Stage I's 11/12: the principal row carries `zeta_F^S(6z) zeta_F^S(w) / L(s, eta)` (l. 6227); the double
  residue at `w = 1`, `z = 1/6` has outside power `X^{1/3} Z^{s - 5/6}` (l. 6299-6300), `Z^{s - 2/3}` at
  `X = Z^{1/2}` (l. 5547); equating with the low bound `Z^{1/4}` (l. 6692-6693) gives 11/12. The 1/12 is `h/6`
  at `h = 1/2`: the density of sixth powers among the Poisson frequencies, the same sextic 1/6 as the pole.
- The pass's own reading of the alternatives (inference, flagged as such): `k = 3` without the quadratic factor
  is blocked because the reflected kernel is then cubic and the cubic large sieve's `(KD)^{2/3}` term is, to its
  recollection, sharp on GRH (Dunn-Radziwill, the paper's reference [DR], l. 16521); `k = 4` over `Q(i)` would
  have the quadratic factor built in (`lcm(2,4) = 4`) and would give the 13/16 law in principle, but is blocked
  by the open problem of the Fourier coefficients of quartic Kubota-Patterson theta functions, which are not
  Gauss sums (Kazhdan-Patterson; Eckhardt-Patterson), so no completed reflection identity exists. Both
  recollections are unchecked against sources, as is the ledger's.

## 7. Literature check (session peterwmurphy-23's survey, 2026-10-11)

The three "from memory" claims above were checked by an independent survey (`~/arda-research/reports/Narrowing
the zeta zero free strip.md`, 56 sources; twist-order notes in `~/arda-research/research_notes/.../higher_order_
twists_inputs.md`, every claim tagged proved / GRH / conjectured). Its findings, as relayed:

- **(a) Metaplectic theta coefficients: correct in substance, sharper wording.** Hecke relations plus
  Kazhdan-Patterson periodicity reduce the coefficients of the n-fold cover of GL_2 to those at
  `1, pi, ..., pi^{n-1}`, leaving `n/2 - 1` (n even) or `(n-1)/2 - 1` (n odd) undetermined coefficients: n = 3
  gives 0, n = 4 gives 1, n = 6 gives 2 (David-Dunn-Hamieh-Lin, arXiv:2306.11875 section 1.2, after Hoffstein 1993
  and Broker-Hoffstein 2016). Chinta-Friedberg-Hoffstein 2011: "the Fourier coefficients of these mysterious
  functions have not been determined beyond n = 3"; non-uniqueness of the Whittaker functional for n > 3 is the
  reason. Quartic status: Suzuki 1983 gives the coefficients at squares (biquadrates, cubes known); the prime
  coefficients are unknown; Patterson's 1984 quartic conjecture (corrected by Eckhardt-Patterson 1992) is proved
  only over `F_q(T)` (Hoffstein 1992). de Faveri-Dunn-Hoffstein, arXiv:2607.07911, section 1.2: "No such
  evaluation is available for n >= 4, and this is the main obstruction."
- **(b) Sharpness of the cubic sieve's `(KD)^{2/3}`: correct, and now unconditional.** Dunn-Radziwill, Annals
  200 (2024), Theorem 1.4: under GRH for Hecke L-functions over `Q(omega)`, `(AB)^{2/3} << B(A,B) << (AB)^{2/3+eps}`
  with only the lower bound needing GRH, extremal sequence the normalised cubic Gauss sums; de Faveri-Dunn-
  Hoffstein (July 2026) Theorem 1.1 makes the lower bound unconditional for n = 3 and proves the quartic lower
  bound `A + B + A^{3/4}B^{1/2} + A^{1/2}B^{3/4}`.
- **(c) The `K + D` sextic sieve: expected FALSE for arbitrary coefficients.** dFDH Conjecture 1.8: for every
  n >= 3, `Xi_n(A,B) = (AB)^{o(1)}(A + B + A^{1-1/n}B^{2/n} + A^{2/n}B^{1-1/n})`, two-sided; the sextic family
  contains the cubic characters and inherits the `X^{5/6}` bias. Best proved sextic upper bound: de Faveri,
  arXiv:2610.04045 (2 October 2026), `A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6}` over the sixth-power-free kernel,
  replacing BGL's `(AB)^{2/3}`. Plugged into a copy of the ledger's optimiser it gives `sigma0 = 1` on the
  unreflected branch for all `ell`, `M` (the `A^{5/6}` mixed term is exactly neutral against the Mellin `+M/12`;
  modelled, not proved), and it does not touch Lemma 15.1's reflected cap. So the ledger's one "specified input
  below 0.85" is, as of October 2026, expected not to exist.
- **(d) A quartic Patterson-type reflection over `Q(i)` EXISTS in some form.** David-Dunn-Hamieh-Lin
  (arXiv:2306.11875, v5 January 2026), Theorem 1.1, unconditional: `sum g~_4(c) (c/|c|)^l Lambda(c) R(Nc/X) <<
  X^{5/6+eps} + X^{3/4+eps}|l|^{3/2+eps}`, improving Patterson 1987. Mechanism: twisted multiplicativity
  `g~_4(ab) = g~_4(a) g~_4(b) (a/b)_2` reduces Type II to a QUADRATIC large sieve over `Q(i)` (Onodera 2009,
  Goldmakher-Louvel 2013), with "the `X^{5/6+eps}` bottleneck in Type II"; Type I uses Suzuki's squares formula.
  Two cautions: the same `X^{5/6}` appears, so k = 4 does not obviously beat the sextic cost; and the ledger's
  algebraic point that the Hasse-Davenport absorption degenerates at k = 4 was not independently checked by
  the survey. This is the one place where section 5's "blocked" might be too strong: there is a quartic
  apparatus for prime sums, just not (yet) one that absorbs Mobius or yields a completed reflection identity.
  No paper treats Mobius-weighted cubic, quartic or sextic sums at all.
- **(c') de Faveri's bound applied to the paper's own sums** (`~/arda-research/followups/defaveri_vs_row_family.md`):
  it applies verbatim to the sextic large sieve of Lemma 9.1 (paper.tex l. 4707; non-binding, no change to `sigma0`)
  and, after a reduction costing `Z^eps` on columns with the exact factorisation `m = m_1 m_2^6` on rows, to the
  unreflected completed row (l. 8078-8110); the modelled no-gain result `sigma0 = 1` stands for every `ell`, `M`.
  Extra finding: the completed-row probe sums over ALL `m` prime to `S` (l. 3406-3412), so any sieve over it,
  including a hypothetical `K + D` one, carries an inherent `Q^{1/6} N` term that the ledger's scenario C omits;
  with it, scenario C's 0.85 becomes `14/15 - ell/15` (0.8667 at `ell = 1`). So even the conjectural input would
  not have reached 0.85.
- **Open discrepancy to settle:** the method map derives the cap `ell <= 1/6` from Lemma 15.1's `M' >= 1/2`; the
  ledger derives `ell <= 1/5` (the 13/15 floor) from the reflected-energy range `M + ell <= 1`, `2M >= 1 + 3 ell`.
  Neither examined whether `M' >= 1/2` is essential. The survey ranks reading section 15 to settle this as its
  action #1. It changes nothing about the verdict (13/15 versus 7/8 is the difference between `Lambda <= 0.27`
  and `0.28`), but the note should not claim more precision than the two readings jointly support.
  Partial answer from the source: the proof of Prop. 15.3 uses the condition explicitly ("this is possible because
  `M' >= 1/2` and ...", paper.tex l. 8593, in the tuple-ratio step), and at the paper's point it binds exactly
  (`M' = M - 2d = 5/6 - 1/3 = 1/2` at `d = ell = 1/6`). So for the paper's proof AS WRITTEN the cap is `ell <= 1/6` and
  7/8 is exact; the ledger's `ell <= 1/5` (13/15) is what the reflected-energy range alone would allow if that
  step were re-proved without `M' >= 1/2`. Whether it can be is not known to either session.

## 8. Verdict

Agrees with the ledger's gate recommendation and is strengthened by the survey: NO-GO for any parameter or
geometry route. The sextic order is forced by Hasse-Davenport duplication (needs `k` even) plus the existence of
an explicit theta formula (needs `k/2 <= 3`), leaving `k = 6`; the only specified input that would have moved the
constant below 0.85 is now expected to be false (dFDH Conjecture 1.8); and the quartic apparatus that does exist
(DDHL 2026) carries the same `X^{5/6}` bottleneck. Replacing the sextic structure is a question about
metaplectic forms, for a specialist, not for this project. 7/8 stands; `0 <= Lambda <= 9/32` is the
kernel-checked picture; `Lambda = 0` is untouched. conjecture1_proved = False.
