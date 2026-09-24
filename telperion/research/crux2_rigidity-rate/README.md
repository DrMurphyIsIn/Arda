# Crux round 2, lens "rigidity-rate": rigidity carries no rate (builder report)

`conjecture1_proved = False`. The Riemann Hypothesis is open, and nothing in this folder or in the
companion Lean file bears on where the zeros of the Riemann zeta function lie. This is a result
about a class of arguments.

## The question

Round 1 isolated one genuinely rigid lever, "Theorem A". A positive measure `N` on `[1, ∞)` with
`N({1}) = 1` and zeta's exact functional equation (FE) must be the counting measure of the positive
integers. This is Beurling-Hamburger rigidity. The lens asked whether a quantitative version of
that rigidity could buy something zeta's classical theory cannot. The target was a zero-free region
of better than de la Vallee Poussin (dVP) quality, obtained without exponential sums.

## The answer, in one paragraph

No. Made quantitative, the rigidity is two exact window identities, and their entire output is
finite coefficient data. Finite coefficient data, even with an Euler product, nonnegative von
Mangoldt weights (P2), integer frequencies and Riemann's theta relation to 120+ digits, is
compatible with a zero at `1 - δ + it` for every `δ > 0` and every `t ≠ 0`. For `t = 0` it is
compatible with a double real zero at `1 - δ`, for every `0 < δ < 1`. The `t ≠ 0` zeros include
points inside the proven Mossinghoff-Trudgian-Yang zero-free region of zeta. The `t = 0` zero sits
on the real segment `(0, 1)`, where zeta has no zeros. The construction is the
"pole-shadow" fake:

    F(s) = ζ(s) / (ζ_{≥X}(s + δ − it) · ζ_{≥X}(s + δ + it)),   where ζ_{≥X}(w) = ζ(w) ∏_{p<X} (1 − p^{−w}).

The builder turned this into a statement about Mathlib's `riemannZeta` itself and kernel-checked it
end to end.

The build also found something the idea did not have. The idea's open "intermediate regime"
conjectured a dVP cap. The fakes that would support that conjecture cannot live in a uniform
counting class. Their counting constant must be exponentially large in `X^{1−θ−η}`, where `η` is
the depth of the zero. So the evidence now points the other way, and the question is restated
precisely below.

## What is kernel-checked

File:
`telperion/examples/li_positivity/lean/Crux/Crux2_rigidity_rate.lean` in worktree `arda-crux2`,
on the Lean v4.34.0-rc1 island.

- It contains 80 theorems and lemmas.
- Every `#print axioms` line is exactly `[propext, Classical.choice, Quot.sound]`.
- There is no `sorry`, `admit`, `native_decide` or new axiom, and no warnings.
- Transcript and sha256 are in `lean_check_transcript.txt`.

To re-run the check:

    cd telperion/examples/li_positivity/lean && <leanlock.sh> lake env lean Crux/Crux2_rigidity_rate.lean

| Block | What it says | Key names |
|---|---|---|
| A-C | The triangle/sinc² pair and the window identities. The FE defect tested on the triangle equals the sinc²-weighted non-integrality. It has stability constant `8/π²`, rigidity, a counting form, and the finite extremal point-mass inequality. | `window_defect_identity`, `window_defect_stability`, `window_defect_rigidity`, `window_defect_counting`, `atom_le_triPairHat` |
| C' | Multiplicity half. The modulated triangle reads off `a_m` exactly. | `triPairHat_mod_eq`, `triPairHat_mod_int` |
| D | Local positivity of the fakes: `a_n ≥ 0`, `a_n = 1` for `n < X`, and brackets `1 − 2p^{−kδ}cos(kt log p) ≥ 0`. | `fakeCoeff_nonneg`, `fakeCoeff_eq_one_of_lt`, `fake_vonMangoldt_bracket_nonneg` |
| E1-E3 | Identification: `a = 1 ⋆ g` with `g` multiplicative, and `Σ a_n n^{−s} = F(s)` on `Re s > 1`, with `F` built from `riemannZeta`. | `fakeCoeff_eq_zeta_mul_gFun`, `hasProd_inv_zetaTail`, `LSeries_fakeCoeff_eq_poleShadow` |
| E4 | `F → 0` at `s₀ = 1 − δ + it`, with an explicit order-one constant. `F` is holomorphic on `{Re s > 1−δ}∖{1}` and near `s₀`. It has the same zeros as ζ in `Re s > 1−δ`, and a simple pole at 1. | `poleShadow_tendsto_zero`, `poleShadow_div_tendsto`, `poleShadow_differentiableAt_of_re`, `poleShadow_eventually_differentiableAt`, `poleShadow_eq_zero_iff`, `poleShadow_residue` |
| E5 | Exact double real zero when `t = 0`. The headline, and the MTY instance. | `poleShadow_real_double_zero`, `finite_data_no_zero_free_region`, `mty_placement`, `mty_fake` |
| E6 | Expulsion estimate. Left of its zero, the real fake is exponentially large. | `norm_riemannZeta_real_bounds`, `poleShadow_real_exp_large`, `expulsion_of_transfer_bound` |
| F | Both window tests are blind to the fake below `X`. | `fake_window_tests_blind` |

The headline, informally: for every `X > 1`, `δ > 0` and `t ≠ 0` there is `X' ≥ X` with the
following properties.

- `F = poleShadow X' δ t` has nonnegative, multiplicative (Euler-product) coefficients.
- Those coefficients equal 1 for every `n < X`.
- Its local brackets are nonnegative.
- Its Dirichlet series equals `F` on `Re s > 1`.
- `F` is holomorphic on `{Re s > 1−δ}∖{1}`, with ζ's zeros there, and on a punctured neighbourhood
  of `1 − δ + it`.
- `F(s) → 0` as `s → 1 − δ + it`.

## What is paper-level (and checked by hand, not by the kernel)

1. **FE ⇔ distributional Poisson.** The step `FE ⇔ ν̂ = ν` is classical. From it, Theorem A reduces
   to the two window tests `|sinc x|²` and `|sinc(x − m)|²`, and no periodicity step is needed.
2. **P2 at the analytic level.** The identity `−F′/F = Σ Λ_F(n) n^{−s}` with
   `Λ_F(p^k) = log p (1 − 2p^{−kδ}cos(kt log p))` is paper-level. The brackets themselves are in
   the kernel.
3. **Theta relation.** Riemann's theta relation holds to precision `e^{−πX²/Y}` on `[1/Y, Y]`.
   For `X = 10⁶` and `Y = 10¹⁰` the defect is at most `2.6·10^{−128}` (rigorous; section N5).
4. **Transfer lemma.** If `N = N_Z` on `[1, X)` and `|N(x) − ⌊x⌋| ≤ K x^θ`, then
   `|ζ_N(s) − ζ(s)| ≤ K|s|X^{θ−σ}/(σ − θ)` for `σ > θ`. Precision `X^{1−θ} ≳ K t log t` therefore
   means identification with ζ at height `t`.
5. **Rate cap with growth.** This combines the rescaling and grafting lemmas with Broucke,
   arXiv:2507.13780, Theorem 1.6. The builder checked the theorem statement by reading the PDF
   (excerpt in `broucke_2507.13780_thm1.6_excerpt.txt`).
   - The hypotheses allow regular variation of index `−α` with `0 < α ≤ 1` and require
     `1/u = o(f(u))`, so `f(u) = log u / u` qualifies.
   - Broucke's own bound (1.4) gives growth exponent 2 near `σ = 1`, and rescaling by 4 gives the
     FE convexity exponent `1/2`.
   - Caveat: the source is an unrefereed preprint.
   - Precision: the phrase "nor even `σ > 1 − C loglog t / log t`" needs `f = C′ log u/u` with
     `4C′ > C`.
   - The rescaled object is a P2 measure system, not an integer-weighted Beurling system.
6. **Expulsion.** Combining E6 with the transfer inequality: if the real fake of depth `η` lay in a
   counting class `𝒞(X, θ, K)`, then `log K ≥ 2 Σ_{p<X} p^{−(σ+η)} − O(1) ≫ X^{1−θ−η−ε}/log X`.
   - The uncorrected fake has density `G(1) = ∏_{p≥X}(1 − p^{−1−η})² ≠ 1`, so it lies outside
     every such class trivially.
   - The bound matters for the density-corrected fake `F · ∏_{q∈S}(1 − q^{−s})^{−λ_q}` with
     `q ≥ X` and `λ_q ≥ 0`. This correction keeps P2, the coefficients below `X`, and the zero.
   - On the real segment the correction only increases `|F|`, because each factor is at least 1
     there. So the same lower bound on `K` applies.
   - Under RH, `F · H − ζ` has no poles in `σ > 1/2` and grows polynomially, so the corrected fake
     plausibly lies in some class `𝒞(X, 1/2 + ε, K)`. That would make the bound a real constraint
     rather than a vacuous one. This membership claim is HEURISTIC and not proved here.

## Corrections to the idea (none kills a claim)

- **Order of the zero.** "Simple zero" is really order `1 + ord_{s₀}ζ`. The zero is simple iff
  `ζ(s₀) ≠ 0`, which is kernel-checked as a criterion. All numerical instances have
  `|ζ(s₀)| ∈ [0.24, 1.46]`.
- **Theta bound.** The round-1 theta bound `2.3·10^{−122}` is valid but crude. The sharper bound
  is `2.6·10^{−128}`.
- **Broucke citation.** The hypotheses were verified, and two precisions were added (item 5 above).

## The intermediate regime, restated

The regime in question has precision `X = t^A` with `A < 1/(1−θ)` and a uniform counting constant
`K`. The idea conjectured a dVP cap there. The one rigorous general fact is the transfer inequality
evaluated at the zero. Any new zero `s₀` (with `ζ(s₀) ≠ 0`) at depth `η` forces
`K ≥ (1−θ−η)|ζ(s₀)| X^{1−θ−η}/|s₀|`, which is polynomial.

A dVP cap would need P2 constructions that nearly attain this bound. Every P2 construction we know
pays exponentially instead.

- The pole shadows are the clearest case. The kernel-checked lower bound together with the
  numerics gives `log K ≥ 68.9` at `X = 10⁶`, `θ = 1/2`.
- The mechanism is a restriction to `[X, ∞)`. The zero forces a log-singularity of
  `log(ζ_N/ζ) = ∫_{[X,∞)} u^{−s} dΠ′`.
- P2 (`Π′₋ ≤ Π_Z`) forbids the concentrated negative mass of the Phragmen-Lindelof extremal. So
  `Π′` must carry a tail of density about `u^{−η}/log u` starting at `X`.
- The continuation of that tail is of size `X^{1−η−σ}/log X`, and exponentiating it is what makes
  the counting constant exponential.

The competing conjecture is **restricted-support rigidity**: P2 forces
`log K ≳ X^{1−θ−η}/log X` for every new zero at depth `η`. If it is true, then precision `t^A`, for
any `A > 0` and uniform `K`, is identification rather than a dVP cap. Both statements are
conjectures. The evidence favours the competing one. Neither is proved.

## Numerics (`rigidity_rate_numerics.py` → `rigidity_rate_numerics_out.json`)

These are float64/mpmath computations, not interval-certified. The script runs in about 6 s.

- **N1: the zero and its order.** The kernel's order-one constant matches finite differences to
  5 or more significant digits, at four settings:

  | X | δ | t | kernel constant | finite difference |
  |---|---|---|---|---|
  | 50 | 0.2 | 10 | 10.5338 | 10.53375 (referee: 10.5337507) |
  | 50 | log2/log50 | 14 | 1.73634 | 1.73634 |
  | 200 | log2/log200 | 40 | 9.83384 | 9.83378 |
  | 10⁶ | log2/log10⁶ | 10 | 34.6266 | 34.6261 |

  The winding number of `F` around `s₀` is 1.000 in every case, and ζ's is 0.

- **N2: the double zero at `t = 0`.** `F/h² → ζ(0.8)/P₁² = 230.655`, and the winding number is
  2.000.
- **N3: Dirichlet series against the closed form** at `2 + 3i` (`N = 2·10⁵`). The difference is
  `1.6·10^{−6}`, below the tail bound of `7·10^{−5}`.
- **N4: MTY instance** with `T = 14`, `A = 3.86`.
  - `X = 26549` (2913 primes) and `δ = 0.068044`.
  - The zero is at `0.931956 + 14i`, which lies to the right of MTY's boundary `0.931832` at that
    height. The winding number is 1.
  - Every `a_n = 1` for `n < X`.
- **N5: theta relation.** The rigorous bound is `|D(y)| ≤ 2.6·10^{−128}` on `[10^{−10}, 10^{10}]`.
- **N6: expulsion** (`t = 0`, `θ = 1/2`, `σ = 0.6`). The kernel bound gives
  `log K_min = 0.5, 3.8, 8.0, 17.3, 34.6, 68.9` for `X = 50, 200, 10³, 10⁴, 10⁵, 10⁶`.
- **N7: `t ≠ 0` heuristic.** `log|F(σ + it)| ≈ Σ_{p<X} p^{−(σ+η)}`. For example, at `X = 10⁶`,
  `t = 10`, `σ = 0.6` the values are 35.9 and 35.5.

## Negative controls and circularity

- **Circularity.** No step is equivalent to RH, and no claim is made about zeta's zeros.
- **Why DH and Epstein are not the controls here.** The no-go is a statement about the class
  "P2 + Euler product + integer frequencies". Davenport-Heilbronn and Epstein lack P2 or the Euler
  product, so they are outside the class.
- **What the controls are.** The fakes themselves are the controls. They pass exactly the finite
  tests that the lens identifies as rigidity's whole output (`fake_window_tests_blind`).

## Files here

- `README.md`: this file.
- `rigidity_rate_numerics.py` and `rigidity_rate_numerics_out.json`: sections N1 to N7.
- `lean_check_transcript.txt`: the kernel check (`#print axioms` for all 80 theorems and lemmas),
  with the file's sha256.
- `broucke_2507.13780_thm1.6_excerpt.txt`: verbatim statement of the external input.

The working notes, including the full expulsion derivation, are in
`/private/tmp/claude-0/crux2/rigidity-rate/NOTES.md` (builder section at the end).
