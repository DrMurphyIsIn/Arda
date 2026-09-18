# Campaign spec: Route P as diffraction — the Bragg-moment form of the Li inequality

**Date:** 2026-09-11
**For:** the RH session (owner of `telperion/examples/li_positivity/` and the RvM core)
**Origin:** maintainer proposal, reviewed against main; every named ingredient verified present.
**Status:** spec only — nothing below is built. `conjecture1_proved = False` and this campaign
does not change that (see the wall, section 5).

---

## 0. The idea in one paragraph

Route P (#465, `rh_iff_companion_ge`) relocates RH onto one inequality per n: the companion
coefficient `(taylorCoeff zetaPoleCompanion n).re` never drops below the explicit archimedean
floor `−(1 + (taylorCoeff Γℝ n).re)`. Since
`logDeriv zetaPoleCompanion = 1/(s−1) − Σ Λ(m)·m^(−s)` on `Re s > 1` (compose #461's
`logDeriv_zeta_eq_companion_sub_pole` with `logDeriv_zeta_eq_neg_LSeries_vonMangoldt`),
Route P's arithmetic carrier is a **von Mangoldt moment** — a log-prime Bragg amplitude.
The diffraction reading of the iff:

> the diffraction spectrum lies on the critical line
> ⟺ every order-n log-prime Bragg moment of the companion clears the explicit archimedean floor.

That is the Guinand–Weil / Dyson picture made into a positivity statement on `{log p^k}` —
and it ties Route P directly to the RvM/diffraction core, closing the loop between the
project's three RH storylines (Route P, the RvM count, the finite explicit formula).

## 1. Verified ingredients (all on main today; file references checked 2026-09-11)

- `zetaPoleCompanion` — `RvMDiffractionCore.lean:1691`:
  `Function.update (fun z => (z−1)·ζ(z)) 1 1`, with `zetaPoleCompanion_apply_of_ne` and
  `zetaPoleCompanion_one`.
- `logDeriv_zeta_eq_companion_sub_pole` — `RvMDiffractionCore.lean:2112`
  (hypotheses `z ≠ 1`, `ζ(z) ≠ 0`).
- `logDeriv_zeta_eq_neg_LSeries_vonMangoldt` — `RvMDiffractionCore.lean:472`
  (hypothesis `1 < s.re`; wraps Mathlib's `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).
  Note the file's own docstring (line 271) already gestures at "prime sums — the Bragg peaks";
  this campaign is that comment, taken seriously through Route P.
- `rh_iff_companion_ge` (#465) — the Route P iff, kernel-clean.
- `taylorCoeff_riemannXi_split_explicit` (#463) + the archimedean coefficient as an explicit
  polygamma-at-1/2 combination (#464) — the floor is fully computed.
- The weighted argument-principle engine (#429–#431): `N(T)` and the finite Li-sum as one
  functional under two weights; `li_finite_explicit_formula` (finite Bombieri–Lagarias
  skeleton); `liCoeff_isLimit_partialSums` (exhaustion limit, conditional on its named
  genus-1/Hadamard hypotheses).
- `rect_explicit_formula` + `integral_vonMangoldt_term` + `left_edge_prime_reflection` +
  the Binet engine `norm_digamma_sub_log_le` — the finite-height diffraction identity and its
  archimedean quantitative side.
- #434's divisor ↔ NontrivialZero index-match and #427's `xiTele_eq_riemannXi` — the seams
  that let the count, the Li object, and the box machinery talk about one `riemannXi`.

## 2. The campaign, in five steps

**Step 1 (mechanical, do first).** `logDeriv_companion_eq_pole_sub_vonMangoldt`:
for `1 < s.re`,
`logDeriv zetaPoleCompanion s = 1/(s−1) − LSeries Λ s`.
Pure composition of the two verified lemmas (`ζ(s) ≠ 0` is automatic on `Re s > 1`;
`s ≠ 1` likewise). Estimated ~10 lines. This is the campaign's cornerstone and is free.

**Step 2 (moderate).** Moment identities at `σ > 1`: for each k,
`iteratedDeriv k (logDeriv zetaPoleCompanion) σ`
`= (−1)^k · k! / (σ−1)^(k+1) + (−1)^(k+1) · Σ Λ(m)·(log m)^k · m^(−σ)`.
The pole side is elementary; the series side needs termwise iterated differentiation of
`LSeries Λ` — check Mathlib's `LSeries` derivative/analyticity API first (WebFetch the
pinned-version docs; do not guess lemma names from training data). These are genuine,
convergent, unconditional prime-power moments — the Bragg amplitudes at frequencies
`log m`, in the kernel.

**Step 2.5 (certificate shape — optional but cheap).** At fixed rational `σ > 1`, truncation
`m ≤ M` plus an elementary tail bound (`Λ(m) ≤ log m` + integral comparison) makes each
moment a certifiable finite computation: a candidate `bragg_moment` emitter kind
(exact-rational partial sum, explicit tail majorant, Arb only if transcendental constants
enter). Honesty: the RH-relevant regime is `σ → 1⁺`, where these blow up against the pole
term — a `σ > 1` certificate is unconditional arithmetic, NOT progress on the inequality.
Wire per standing policy: sensitivity declaration, negative control, guard + `defaultTargets`
(per the #448/#451/#462 lessons).

**Step 3 (the substantive build — no limits, unconditional).** The finite-box Bragg form:
run the weighted engine with the Li weight `1 − (1−1/ρ)^n` on a box whose right edge lies in
`Re s > 1`, and expand that edge term-by-term via the Step-1 identity (the Li-weight analogue
of `integral_vonMangoldt_term`). Target statement `li_finite_bragg_form`: the finite Li-sum
over the box's zeros equals prime-side Bragg integrals (frequency `log m`, explicit
amplitude) plus archimedean edge terms plus an explicit remainder. Combined with
`rh_iff_companion_ge`, this is the diffraction reading at finite height, with the remainder
standing as an explicit term, exactly parallel to `rect_explicit_formula`'s posture.

**Step 4 (the research seam — named hypotheses only).** Connect
`taylorCoeff zetaPoleCompanion n` (which lives at `s = 1`, the boundary of convergence) to
the `σ → 1⁺` limits of Step 2's moments. The coefficients equal REGULARIZED von Mangoldt
moments (generalized Stieltjes-type constants); the unregularized limit is PNT-strength
analysis. Enter it the way this project always does: Abel-summation / corridor-bound
statements as named hypotheses, never claimed. If Step 3 lands, much of the motivation for
Step 4 can be deferred — the finite-box form already delivers the diffraction reading.

**Step 5 (paper — staged, HOLD for maintainer).** A subsection in the #433 voice:
"Route P as diffraction: the Bragg-moment form of the Li inequality." Placed after the
Route P / criteria material; cites Guinand, Weil, Dyson, Bombieri–Lagarias. Same staging
discipline as #426/#433 (no auto-merge; maintainer reads first).

## 3. Phrasing caution (binding — from the Dyson triage, #395)

`telperion/docs/DYSON_QUASICRYSTAL_CERTIFICATES.md` refuted (0–3) the claim that pure-point
support on `{log p^k}` is unconditional. The slogan in section 0 is an IFF — both sides
conditional — and must stay one. Do not write, in Lean docstrings or paper text, any
unconditional "the spectrum is supported on the log prime powers." The finite-box and
`σ > 1` statements are unconditional; the spectral reading of the LIMIT is exactly as
strong as RH, no stronger and no weaker.

## 4. What this buys

- The full-circle Dyson statement: the RH criterion itself becomes a positivity statement
  on the primes — the strongest closing move available for the paper's diffraction framing.
- Kernel unification of Route P with the RvM core and the finite explicit formula: one
  engine, three weights, one `riemannXi`.
- A new certificate shape (Step 2.5) with genuinely unconditional instances.

## 5. What this does not buy — state it verbatim in every PR body

By Bombieri–Lagarias, the uniform prime-side bound is itself equivalent to RH: relocating
the obligation from zero-sums to prime-moments is a change of coordinates, not of
difficulty. No step above crosses that wall, and none claims to. RH is neither proved nor
approached. `conjecture1_proved = False`.

## 6. Footguns for the builder

- WebFetch the pinned Mathlib docs before drafting against the `LSeries` API — do not
  guess lemma names (standing footgun; agents have hung on hard drafting without it).
- Guard wiring: every new headline theorem into `AxiomGuardLiPositivity.lean` AND its lib
  into `defaultTargets` (the #448 dark-guard failure mode; see #451/#462).
- CI sorry-scan: write "no `sorry`" (backticked) in docs and docstrings; the bare
  hyphenated adjective trips the scan.
- The v4.34 island builds locally; keep new files on that island (Route P and the
  RvM diffraction core both live there) rather than the v4.32 side.
