# `preordering_multiplier` -- positivity on a semialgebraic set by a positive multiplier (2026-09-22)

`conjecture1_proved = False`. Everything below is a finite real polynomial inequality on an explicit
semialgebraic set. The dogfood proves `0 <= Re Q_N(z)` on a disk for `N <= 5`; Li's criterion needs
every `N`, and `N = 6` already fails termwise on that disk (a located, kernel-checked refutation).
Nothing here is a step toward RH.

Source: `SHAPES_AUDIT_48H_2026-09-22.md` section 2, rank 3 ("value per line"), merging
`SHAPES_AUDIT_D_LI_FACE_2026-09-22.md` 3.1 (shape A) with its dogfood family 3.3 (`li_box_rung`),
`SHAPES_AUDIT_B_WEIL_WALL_2026-09-22.md` C3 (three box `nlinarith` positivities) and
`SHAPES_AUDIT_C_B7_PARTIAL_FRACTION_2026-09-22.md` 5.3 item 1 (the strip-inequality backfill where
Polya-after-shift is not enough).

## The shape that had no certificate type

The Li rungs certify `0 <= Re Q_N(z)` on the disk `(Re z)^2 + (Im z)^2 <= Re z` by an identity in
three quantities, each nonnegative on the disk: `d = Re z - |z|^2` (the disk hypothesis),
`B = (Im z)^2` and `s = |z|^2`. For `N = 4, 5` the identity only exists after multiplying the
target by a positive multiplier (`14 s`, `s^2`), and the multiplier's zero set (`s = 0`, i.e.
`z = 0`) needs its own branch. Four neighbouring kinds each miss one ingredient:

| kind | generators | constants on products | multiplier |
|---|---|---|---|
| `handelman` | LINEAR forms only | yes | no |
| `polya_zeros` | the simplex | yes | `(sum x)^N`, homogeneous forms only |
| `rational_sos` | none (no hypotheses) | SOS, not constants | an Artin denominator |
| `constrained_sos` | polynomial, degree 1 in the generators | SOS multipliers (an SDP) | no |
| **`preordering_multiplier`** | **POLYNOMIAL** | **yes** | **`kappa g_j^e`, zero locus certified** |

## Statement family

For base variables `x = (x_1, ..., x_k)` and polynomial generators `g_1, ..., g_m`:

    theorem nm (x_1 ... x_k : R) (h_i : lhs_i <= rhs_i) ... : 0 <= p(x)

Each generator is tagged:

* `hyp` -- carried as a hypothesis `lhs_i <= rhs_i` whose content `rhs_i - lhs_i` must EXACTLY equal
  `g_i` (default `0 <= g_i`); the Li disk is `x^2 + y^2 <= x` for `d = x - x^2 - y^2`;
* `structural` -- no hypothesis; `0 <= g_i` is closed by `positivity`. Admitted only when the
  EXPANDED rendering is a nonnegative-rational combination of even-exponent monomials (conservative:
  `(x - y)^2` renders with a negative cross term and is refused; tag it `hyp` instead).

An optional **complex face** restates the real core as the island's claim `0 <= (<target>).re` about
`z : C`, with coordinates `x -> z.re`, `y -> z.im` and one caller-supplied
`simp only [<island unfold list>]` + `ring` step (the `complex_re_im_split` shape; `simp_closes`
drops the `ring` when the unfolding alone closes it, as for `Q_1 z = z`).

## The certificate

`PreorderingMultiplierCert`, every number an exact rational:

* the multiplier `M = kappa * g_j^e` (`kappa > 0`, `1 <= e <= 3`) or a positive constant;
* terms `(c_alpha, alpha)` with `c_alpha >= 0` and the EXACT identity in the base variables
  `M * p = sum_alpha c_alpha * prod_i g_i^{alpha_i}` (`sympy.expand`, residual 0);
* for a non-constant `M`, a `LocusCertificate`: `g_j = sum_i w_i (x_i - a_i)^2` exactly, every
  `w_i > 0`, so `{M = 0}` is the single point `a`; and `p(a) >= 0` exactly.

**Finder.** `terms=None` searches: an exact rational phase-1 simplex (Bland's rule, `Fraction`s, so
"infeasible" is a proof of infeasibility for that column set) over the products of total generator
degree `<= D`, inner loop `D = 0, 1, ..., max_total_degree` (the first feasible degree gives the
smallest certificate), outer loop over the multiplier candidates in order (`"auto"`: the constant 1,
then `g_j^1, g_j^2, g_j^3` for every generator that admits a single-point locus). The locus can be
derived (`locus="auto"`, `derive_locus`). The finder is untrusted: whatever it returns is re-verified
exactly, and the certificate is run through `nonvacuity.assert_certificate_sensitive` (bumping a
coefficient or dropping a product must break the identity).

## Tactic skeleton (a parameterised copy of `LiBoxRungs.lean:144-169`)

    theorem nm (x y : R) (hz : x ^ 2 + y ^ 2 <= x) :
        0 <= p := by
      obtain <d, hd0, hde> : exists d : R, 0 <= d /\ d = x - x ^ 2 - y ^ 2 :=
        <_, by linarith, rfl>                          -- hyp generator
      obtain <s, hs0, hse> : exists s : R, 0 <= s /\ s = x ^ 2 + y ^ 2 :=
        <_, by positivity, rfl>                        -- structural generator
      generalize hP : p = P
      have key : 14 * s * P = <sum c_alpha g^alpha in d, B, s> := by
        rw [<- hP, hde, hBe, hse]
        ring
      have hcert : 0 <= 14 * s * P := by rw [key]; positivity
      rcases eq_or_lt_of_le hs0 with hs' | hs'
      . -- locus: s = 0 forces x = 0, y = 0, where the target is 0
        have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
        have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]
        rw [<- hP, hlocx, hlocy]
        norm_num
      . exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : R) < 14 * s)).mp hcert

`M = 1` collapses the tail to `have key : p = <cone> := by rw [...]; ring; rw [key]; positivity` (the
`re_Q3_nonneg` form); a constant `M != 1` cancels with `(by norm_num : (0 : R) < kappa)`.

Three deliberate deviations from the hand proof, each for robustness, none weakening anything:

1. `generalize hP : p = P` instead of `set P := p with hP`. `set` rewrites EVERY hypothesis in which
   `p` occurs as a subterm; for `p = x` (`Re Q_1`) it would turn `hz` into `P ^ 2 + y ^ 2 <= P` and
   the `d` alias into `P - P ^ 2 - y ^ 2`. `generalize` touches only the goal.
2. Only the generators the certificate uses are bound (`rw [h<a>e]` fails on an absent alias), and
   only the coordinates the target contains are rewritten in the locus branch.
3. `nlinarith only [...]` in the locus branch: the hypotheses it needs are named, so the call does not
   depend on (or slow down with) the degree-10 `key` / `hcert` in context.

## Refusals (the forge face; every one has a test)

`preordering_multiplier_certificate` raises `PreorderingRefusal` (a `ValueError`, so `certify()`
records it) and never repairs:

| refusal | audit phantom |
|---|---|
| LP infeasible up to the degree cap: `PreorderingObstruction` (OBSTRUCTED_AND_LOCATED, with the exact witness and a `ProbeVerdict`) when the exact grid scan finds `p < 0` on the set; otherwise "no certificate up to the cap", explicitly NOT a verdict on the claim | LP infeasible, `Q_6` located |
| any `c_alpha < 0`; an identity that does not reconstruct; duplicate / malformed exponent vectors | any `c_alpha < 0` |
| a `hyp` generator with no binder, or whose stated `lhs <= rhs` is not exactly the generator | not literally a hypothesis |
| a `structural` generator outside the even-monomial class, or carrying a binder / stated form | `positivity` cannot close |
| a non-constant `M` without a locus certificate, a locus that is not an exact positive-weight sum of squared offsets of the multiplier's generator (a circle, a line), a locus point with `p < 0` (located if in the set) | uncertified zero locus |
| `kappa <= 0`, an undeclared generator, a power outside `1..3`, a product of several generators | multiplier not in the cone |
| identity degree above 24, more than 512 terms, more than 8 generators, an LP above 4000 columns, a scan above 250000 points | cost cliffs |
| floats, non-rational or non-polynomial input, a constant target, a name that is not a plain Lean identifier or collides with a name the proof binds (`P`, `hP`, `key`, `hcert`, `hre`, `h<a>0`, `h<a>e`, `h<a>'`, `hloc<v>`, keywords, called lemmas, face namespaces) | -- |

## Negative control (`negctrl_adapters/adapter_preordering_multiplier.py`)

FALSE twin: `0 <= x - x^2 - 2 y^2` on the disk `x^2 + y^2 <= x`, "certified" by the EXACT identity
`p = d - B`, whose coefficient on `B` is `-1`. The claim is false at `(1/2, 1/2)` (a point of the
disk, `p = -1/4`). Layer 1 refuses it (negative coefficient; with a scan box, located); the adapter
hand-mints the dataclass, `ring` accepts the identity, and the kernel rejects at the cone fold:

    error: failed to prove positivity/nonnegativity/nonzeroness

TRUE twin: `0 <= x - x^2 = d + B`, the same script, compiles clean
(`[propext, Classical.choice, Quot.sound]`). The rendered header of a hand-minted certificate states
its facts as computed ("coefficients of MIXED sign", "hand-minted ... Layer 1 bypassed"), never the
certifier's claims.

## Dogfood (`examples/li_positivity/lean/Probes/Dogfood_preordering_multiplier.lean`)

Generated by `examples/li_positivity/dogfood_preordering_multiplier.py` (a test pins the bytes),
registered as the lean_lib `DogfoodPreorderingMultiplier` and anchored in `AxiomGuardLiPositivity`.

| theorem (core `_real` + complex face) | source | multiplier | terms | found by |
|---|---|---|---|---|
| `re_Q1_nonneg_regen` | `LiBoxRungs.lean:115-117` (`nlinarith`) | 1 | 2 (`d + s`) | LP, degree 1 |
| `re_Q2_nonneg_regen` | `:119-124` (`nlinarith`) | 1 | 3 (`4 d + 2 B + 3 s`) | LP, degree 1 |
| `re_Q3_nonneg_regen` | `:126-142` (audit `:139-155`) | 1 | 8 | the hand certificate, verbatim |
| `re_Q4_nonneg_regen` | `:144-169` (audit `:157-182`) | `14 s` | 14 | the hand certificate, verbatim |
| `re_Q5_nonneg_regen` | `:171-199` (audit `:184-212`) | `s^2` | 18 | the hand certificate, verbatim |
| `re_Q4_nonneg_lp` | same rung | `s` | 12 (integral) | LP, degree 4 |
| `re_Q5_nonneg_lp` | same rung | `s^2` | 19 | LP, degree 5 |

Facts established exactly along the way: `chebyshev_pair_polynomial(N)` equals the island's `Q_N`
(`N <= 5`) and satisfies the inhomogeneous recurrence `Q_{N+1} = (2 - z) Q_N - Q_{N-1} + 2 z`
(audit D 2.6); `li_box_rung_target(N)` equals the island's `hre` polynomials; the LP with `M = 1`
re-finds the hand `Re Q_3` certificate term for term; `M = 1` is LP-infeasible for `Q_4` and `Q_5`
(and `M = s` for `Q_5`) at every product degree `<= 7`, so the hand multipliers are needed, not
decorative.

**`N = 6` is refused, and the refusal is kernel-checked.** The exact grid scan (60 steps per axis of
`[0, 1] x [-1/2, 1/2]`) locates `Re Q_6 = -27772/15625 < 0` at `(x, y) = (4/5, -2/5)`, a point of the
closed disk (on its boundary: `z = 4/5 - 2i/5`, `rho (1 - rho) = 1 + i/2`,
`rho ~ 0.2249 + 0.9087 i`). `obstruction_refutation_lean` states the refutation and the kernel checks
it:

    theorem re_Q6_disk_claim_false :
        ¬ ∀ x y : R, x ^ 2 + y ^ 2 <= x → 0 <= <Re Q_6> := by
      intro h
      have hw := h (4 / 5) (-(2 / 5)) (by norm_num)
      norm_num at hw

(The audit's located point `(0.303, 0.931)` is in rho coordinates; it maps to `z ~ 0.8314 - 0.2829 i`
in the disk with `Re Q_6 ~ -0.7158`, the audit's "-0.715". Floats here are display only.)

The generator appends kernel cross-checks: each regenerated face proves the original
`LowHeightBox.re_Q<N>_nonneg` statement and vice versa, and the island's termwise dispatch
`liPairedSummand_re_nonneg` is re-assembled from the regenerated lemmas alone. All 15 theorems print
`[propext, Classical.choice, Quot.sound]`.

## What it does NOT do

* No SOS multipliers and no SDP (`constrained_sos`); the multiplier is one generator power and the
  certificate coefficients are constants.
* No multiplier whose zero set is more than one point: a circle or a line needs a lower-dimensional
  sub-certificate, which is not built (refused as an uncertified zero locus).
* No products of several generators as the multiplier (the audit's general `prod g_i^{mu_i}`).
* No complex real-part algebra: the face's `simp only` list is the island's own, checked by the
  kernel, not by Python.
* No decision of positivity: the scan can only refuse, never accept; a plain LP infeasibility is
  reported as "no certificate up to the cap", not as a verdict on the inequality.
* The `E6Bridge28.lean:815-866` rvm rungs 2..4 (generators `beta`, `1 - beta`, `gamma^2 - 3/4`), the
  Box 2 degree-1 instance and the B C3 / C 5.3 backfill sites are NOT regenerated here; they are the
  next dogfood targets for this kind.
