# Discharging the analytic inputs of Zhu's window reduction (arXiv:2608.24827, Thm 1.1)

Date: 2026-09-23. Branch `rh/zhu-inputs`. Island: `telperion/examples/rvm_bridge/lean` (Lean
v4.33.0-rc2 / Mathlib 51e6992e via the Zeta23 pin). Node:
`missions/rh/nodes/RH_weil_window_floor_of_certified_block.toml` (DRAFT, re-specified today).
Prior memos: `ZHU_WINDOW_POSITIVITY_IMPORT_2026-09-19.md` (the import and its seam analysis),
`DESIGN_RH_weil_window_floor_of_certified_block_2026-09-22.md` (why the node was opaque).

**conjecture1_proved = False.** Nothing here is about the zeros of zeta. Two of Zhu's four
analytic inputs are now kernel theorems and a third is half a theorem; the Riemann Hypothesis is
exactly as open as it was this morning. A positive window floor at fixed `L` is a finite fragment
that RH predicts; certifying one confirms nothing, and the pointwise-envelope route to the
RH-equivalent clause `forall L, WindowFloor L 0` is closed by Zhu's own Theorem 1.4.

## 0. What changed, in one paragraph

Until today the node carried four `opaque ... : Prop` hypotheses (eq. 2, Lemma 3.1, eqs. 6/12,
and the Arb head floor) and was, by the 2026-09-22 memo's argument, unprovable by construction. The
team lead authorised re-specifying the three ANALYTIC ones as concrete definitions while leaving
the numerical trust seam `ReducedHeadFloor` opaque. That is what this branch does: the definitions
now live on the rvm_bridge island in four new modules and are mirrored verbatim into RHDefs; the
symbol representation (eq. 2) and the digamma envelope (Lemma 3.1) are **proved** and therefore no
longer appear as hypotheses; the Legendre localization is a concrete predicate on Zhu's actual
reduced matrix whose analytic inputs (eqs. 6 and 12) are **proved** and whose tail sums (the
paper's numerically evaluated `eps_D`, `eps_B`) remain a hypothesis; `ReducedHeadFloor` is
untouched. A certified NUMBER still cannot masquerade as a proved THEOREM: `hhead` is opaque, no
proof term can use it, and the node stays DRAFT.

## 1. Per input: proved / reduced / not started

| Zhu input | registry name (RHDefs `WeilWindow`) | island module | status |
|---|---|---|---|
| eq. (2), symbol representation `Q(f) = 2F(i/2)^2 + (1/2pi) int |F|^2 Psi_L` | `SymbolRepresentation L`, `weilSymbol L t` (eq. 3) | `ZhuSymbol.lean` | **PROVED** for every `L`: `RvMBridgeZhu.symbolRepresentation` (ZhuSymbol.lean:353); core computation `symbol_representation_ofReal` (:144) |
| Lemma 3.1, envelope `Re psi(1/4+it/2) - log pi >= log(t/2pi) - 1/t`, `t >= 15/4` | `EnvelopeBound` | `ZhuEnvelope.lean` | **PROVED**: `RvMBridgeZhu.envelopeBound` (:256), via `psiR_ge_envelope` (:230) |
| eq. (6), Legendre-mode transform `hat T_{2k}(t) = (-1)^k 2 sqrt(L(2k+1/2)) j_{2k}(tL)` | `legendreP`, `sphericalBessel`, `legendreMode`, `legendreModeFT` | `ZhuLegendre.lean` | **PROVED**: `legendreModeFT_eq` (:338), core `integral_legendreP_mul_cos` (:304) |
| eq. (12), `|j_n(x)| <= x^n/(2n+1)!!` | `sphericalBessel` | `ZhuLegendre.lean` | **PROVED**: `sphericalBessel_abs_le` (:166), from `integral_one_sub_sq_pow` (:146); entry decay `legendreModeFT_abs_le` (:364) |
| eq. (13) tail data `eps_D`, `eps_B` (Gershgorin / Schur sums on the tail of `M_R = beta* I + 2pp^T + C`) | `poleVec`, `combMatrix`, `reducedMat`, `LegendreLocalization L T# N epsD epsB` | `ZhuLegendre.lean` | **REDUCED, defined concretely, NOT proved.** The tail sums are Zhu Section 5.3's numerically evaluated constants (both `< 1e-100`). Stays the hypothesis `hloc`. |
| Arb head floor `lambda_min(A) >= lam0` | `ReducedHeadFloor` | none | **UNTOUCHED, opaque by design** (`hhead`). |
| parity (Lemma 6.1 / Cor. 6.3), odd sector | `OddSectorFloor`, `EvenSectorFloor` | `ZhuParity.lean` | **DEFINED**; only the trivial directions proved. Carried as the new hypothesis `hodd` (section 3). |

Guard: `AxiomGuardRvMBridge.lean` prints axioms for 13 new anchors (3 envelope, 3 symbol, 5
Legendre, 2 parity); every one reports `[propext, Classical.choice, Quot.sound]`. Island `lake build`
8893 jobs green; no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the new modules.

## 2. How each proof goes (and what it reuses)

### 2.1 Lemma 3.1 (`ZhuEnvelope.lean`, 269 lines)

Zhu proves it from Binet's second formula, which neither Mathlib nor Zeta23 has. The island proof
uses two ranges:

* `t >= 25/2`: Zeta23's Stirling remainder `StirlingVert.digamma_stirling`,
  `|psi(w) - log w + 1/(2w)| <= 3/(Im w)^2`, at `w = 1/4 + it/2`. `Re log w >= log(t/2)` since
  `|w| >= Im w`, and `Re(1/(2w)) = (1/8)/(1/16 + t^2/4) <= 1/(2t^2)`, so the deficit is
  `25/(2t^2) <= 1/t` exactly when `t >= 25/2`.
* `15/4 <= t <= 25/2`: eleven bands. `Re psi(1/4 + it/2)` is monotone in `|t|`
  (`RvMBridge30.psiR_mono`, from Zeta23's vertical-line series), and the right-hand side is
  increasing, so on a band `[a, b]` it suffices that a rational floor at `a` beats
  `log(b/2) - 1/b`. Floors come from `RvMBridge30.psiR_ge_rational` (40 series terms, an integral
  tail, `gamma <= 0.58112`) closed by `norm_num`; the log is bounded above through the degree-11
  Taylor polynomial of `exp` (`Real.sum_le_exp_of_nonneg`). Band edges (multiples of 1/20, margin
  `>= 0.002`) were chosen by a script; the true margin is `0.26` at `t = 15/4` and `0.08` at `25/2`.

### 2.2 Eq. (2) (`ZhuSymbol.lean`, 364 lines)

A rearrangement of the E8 primes-side functional `archSide g - primeSide g` for
`g = autocorr f`, `f` real even smooth with `tsupport f` in `[-L, L]`:

* pole terms: `weilKernel g 0 = weilKernel g 1 = |F(i/2)|^2` by Zeta23's transform factorisation
  `EF.paperFT_weilTest` (`h_{f*f~}(z) = h_f(z) conj h_f(conj z)`) and evenness
  (`Taper.paperFT_neg_of_even`); `F(i/2) = weilKernel f 0`;
* archimedean integral: `weilKernel g (1/2 + it) = |F(t)|^2` (E6Bridge5 `weilKernel_autocorr_line`);
* the `-g(0) log pi` term: `g(0) = ||f||_2^2 = (1/2pi) int |F|^2` (Plancherel as Fourier inversion
  of `g` at `0`, E6Bridge4 `inversion_zero`);
* prime side: `g(log n) = (1/2pi) int |F(t)|^2 cos(t log n) dt` (Fourier inversion, cosine form,
  Zeta23 `Taper.integral_mul_cos_of_paperFT_eq`), `g` even, and `g(log n) = 0` once
  `log n >= 2L` because `supp g` is in `[-2L, 2L]` (`autocorr_eq_zero_of_two_mul_le`: the
  equality case is the null set `{L, -L}`); the comb is a finite sum (`n < e^{2L}`) and passes
  through the integral.

No Fubini is done here (it sits inside `paperFT_weilTest`), and no L^2 Plancherel is needed:
inversion at a point suffices because `hat g = |F|^2` is integrable.

### 2.3 Eqs. (6) and (12) (`ZhuLegendre.lean`, 373 lines)

* `legendreP n := (1/(2^n n!)) D^n (X^2-1)^n` (Rodrigues); `sphericalBessel n x :=
  x^n/(2^{n+1} n!) int_{-1}^1 (1-u^2)^n cos(xu) du` (Poisson, cosine form; the sine part is odd).
* eq. (12): `|int (1-u^2)^n cos(xu)| <= int (1-u^2)^n = 2^{n+1} n!/(2n+1)!!`, the last by the
  recurrence `(2n+3) I_{n+1} = (2n+2) I_n` (differentiate `u (1-u^2)^{n+1}`).
* eq. (6): `D^j (X^2-1)^n = (X^2-1)^{n-j} r_j`, so `D^j (X^2-1)^n` vanishes at `+-1` for `j < n`;
  one integration by parts moves a derivative off the polynomial onto `cos`/`sin` with no
  boundary term (`ibp_step`), two of them give `int D^{j+2} q cos = -x^2 int D^j q cos`, and
  induction gives `int D^{2k} q cos(x.) = (-x^2)^k int (1-u^2)^{2k} cos(x.)`; scale by `L`.
* the entry decay `|hat T_{2k}(t)| <= 2 sqrt(L(2k+1/2)) (tL)^{2k}/(4k+1)!!` for `t >= 0`.

### 2.4 What `LegendreLocalization` says, exactly

With `M_R(k, j) := beta* delta_{kj} + 2 p_{2k} p_{2j} + C_{2k,2j}` on the even modes:

* Gershgorin: for every tail row `k >= N`, the absolute row sum over the tail of `M_R - beta* I`
  is summable and `<= eps_D` (so `lambda_min(D) >= beta* - eps_D`);
* Schur: for every leading column `j < N` the absolute tail-column sum is summable and `<= eps_B`,
  and for every tail row `k >= N` the absolute leading-row sum is `<= eps_B` (so `||B|| <= eps_B`).

Summability is stated explicitly so that Lean's `tsum` cannot return a junk `0`. This is the data
Zhu's Section 4 feeds into the two-block bound; Section 5.3 evaluates it from the entry bounds of
2.3 and finds both constants below `1e-100`. Proving the sums in-kernel would need the explicit
sup of `|Psi_L - beta*|` on `[0, T#]` (available from `psiR_mono` + Stirling) and a closed-form
majorant for `sum_{j >= N} (T#L)^{2j}/(4j+1)!!`; neither was attempted.

## 3. The statement surgery, recorded

The node is DRAFT, so re-specifying its vocabulary is allowed; it changes the statement's
provenance hash (old `8d0bdb0b971ec222`, new in the file header). What changed in
`RH_weil_window_floor_of_certified_block.lean`:

* dropped `hQrep : SymbolRepresentation L` and `henv : EnvelopeBound` -- both are now theorems on
  the island (`symbolRepresentation`, `envelopeBound`), so carrying them would be carrying `True`;
* `hloc : LegendreLocalization L Tsharp N epsD epsB` kept, now concrete (section 2.4);
* `hhead : ReducedHeadFloor L Tsharp lam0 N` kept, opaque, untouched;
* ADDED `hT : 0 < Tsharp`: the opaque draft did not force the split height positive, and
  `betaStar` with `Tsharp < 0` is `log(|Tsharp|/2pi) + 1/|Tsharp| - A_L`, which can be positive;
* ADDED `hodd : OddSectorFloor L (min lam0 (beta - epsD) - epsB)`: Theorem 1.1 and the certified
  even-mode Legendre block cover REAL EVEN `f`; `WindowFloor` quantifies over complex `f`. Zhu's
  Lemma 6.1 gives `Q(f) = Q(Re f_e) + Q(Im f_e) + Q(Re f_o) + Q(Im f_o)` (the even/odd cross term
  is an odd function whose Weil form vanishes; the real/imaginary cross term is `Im(F_r F_i)`, odd
  in `t`), so the complex-`f` floor is `min` of the two sector floors, and the ODD sector needs its
  own block with the pole sign reversed (eq. 14: `8.2e-15` at `L = 0.8`). Without `hodd` the
  statement would let an even-mode certificate speak for complex `f`. The decoupling itself
  (`WindowFloor <- EvenSectorFloor /\ OddSectorFloor`) is NOT proved on this branch; only the
  trivial converse directions are;
* conclusion `WindowFloor L (min lam0 (beta - epsD) - epsB)` UNCHANGED; the proof is still `by sorry`.

In `RHDefs.lean` the three `opaque` declarations were replaced by the verbatim island definitions
(`weilSymbol`, `SymbolRepresentation`, `EnvelopeBound`, `legendreP`, `sphericalBessel`,
`legendreMode`, `legendreModeFT`, `poleVec`, `combMatrix`, `reducedMat`, `LegendreLocalization`,
`OddSectorFloor`, `EvenSectorFloor`); the seam comment block was rewritten to say which links are
proved. The mirror-drift scan (`telperion.missions.mirrors`) reports all 17 Zhu rows in sync.
Two tooling touches, both small: `mirrors.py` now treats `opaque`/`axiom` as declaration
terminators (a `def` followed by an `opaque` used to swallow the opaque's text and report a false
drift), and the `autocorr` bare-name collision between MMDefs's `WeilExplicit.autocorr` and the
WeilForm block re-declared in `ZhuSymbol.lean` is exempted like the existing WeilFormDefs entry.
The `window_form_floor` emitter dogfood (`generate.py --check`) is unaffected: its instances use
only `WindowFloor` and the rounding lemma, and regenerate byte-for-byte.

The 2026-09-22 memo argued against replacing opaques with definitions on the ground that a fake
definition could close the node for the wrong reason. The definitions here are the paper's own
objects, two of them are proved, and the seam that actually carries the certified number is
still opaque, so the node cannot close at all; the memo's concern is honoured, not overridden.

## 4. What remains for a proof of the node (not attempted)

1. The frequency split, eq. (4): from `SymbolRepresentation` and `EnvelopeBound`, with
   `Psi_L(t) >= beta*` for `t >= T#` (needs `combMass` to bound the comb, `log(t/2pi) - 1/t`
   increasing, and `T# >= 15/4`, which follows from `beta* > 0` and `A_L >= 0`). Elementary.
2. The Legendre-basis representation of `R`: orthonormality and completeness of the Legendre
   modes in `L^2_even[-L, L]` (Rodrigues + integration by parts for orthogonality; Weierstrass
   density for completeness), `R(f) = c^T M_R c` for the coefficient sequence. Substantial; not in
   Mathlib.
3. The two-block bound, eq. (13), on `l^2`: pure linear algebra (the 2026-09-22 memo's Option 2).
4. Parity decoupling, Lemma 6.1, to reach complex `f` from `EvenSectorFloor` and `hodd`.
5. Structurally: `hhead` is opaque, so no proof term can use it. The node stays DRAFT until a
   registry trust-seam policy exists; that is by design and unchanged.

## 5. Numbers that are NOT theorems

`9e-18`, `8.9e-18`, `8.2e-15`, `1e-100`, `T# = 200`, `N = 200` appear in comments only. The kernel
asserts none of them. Grants are frozen campaign-wide; no `mission grant` or `mission audit` was
run and no node status was changed.
