# Stage S12 notes: the final assembly (S12a, S12b) (2026-10-11)

Branch `mm/arch-s12` (from `mm/archimedean-rung` 7dabcd045), island `telperion/examples/rvm_bridge/lean`.
Plan: `ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md`, section 1 rows 18-19, section 2.2, section 4 rows S12a and S12b.
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes were touched.

## 1. The chain, with signs

Notation (island conventions, blueprint section 2):
* g is an `IsWeilTest` with tsupport g ⊆ [−L, L] and `paperFT g (I/2) = 0`.
* h = `qLift g L` is S2's lift: g = h' − h/2, h smooth, tsupport h ⊆ [−L, L] (`poleFree_iff_exists_lift`).
* ε' = ε'(1⁺) = `D.eps1 0`, certified as 22.99647568387053 ± 1.2e-22 (S10 `eps1_enclosure`).
* B(h) = ∫∫ conj h(x) h(y) χ(y − x) dx dy, the K_I form on L²([−L, L]).
* SoninTr(g) = Σ_k ‖S ϑ(g) e_k‖² for any Hilbert basis e of L²(ℝ)_ev; it is ≥ 0.

Steps:
1. **S3** `re_weilForm_eq_archW` (2L ≤ log 2, pole-free): Re weilForm(autocorr g) = archW g.
2. **S7** `cc_thm47`: SoninTr(g) = archW g + Re E, with E = `(prolateData bR σ).Eplus (autocorr g)`.
   So archW g = SoninTr(g) − Re E.
3. **S8** `prop55_lift` (support of h in an interval of length ℓ < T = log 3):
   E = −2ε'‖h‖² + ∫∫ conj h(x) h(y) Qε(|y − x|).  With χ = Qε/(2ε'), this is E = −2ε'(‖h‖² − B(h)),
   i.e. CC's N_I = −2ε'(Id − K_I).
   So −Re E = 2ε'(‖h‖² − Re B(h)).
4. **S11** on the translated interval (bridge A1 + A2):
   * |I| = 1/2: Re B(h) ≤ 0.95921‖h‖² (`KI_half_form`), so −Re E ≥ 2ε'·0.04079‖h‖² ≥ 0.
   * |I| = log 2: Re B(h) ≤ 0.9995‖h‖² + 0.058|∫h|²/log 2 (`KI_log2_form_gamma`).
5. **Conclusion.**
   * S12a (L ≤ 1/4, one condition): Re weilForm = archW = SoninTr − Re E ≥ SoninTr + 2ε'·0.04079‖h‖² ≥ 0.
   * S12b (2L ≤ log 2, two conditions): ∫h = 0 by S2 `paperFT_zero_lift_iff`, so
     archW ≥ SoninTr + 2ε'·0.0005‖h‖² ≥ SoninTr ≥ 0.
   * 6.11 form (2L ≤ log 2, one condition): ∫h = −2 paperFT g 0 (S2 `integral_lift`), so
     archW ≥ SoninTr − c|paperFT g 0|², c = 8·0.058·ε'/log 2 = 4γ/log 2 with γ = 2ε'·0.058 ≈ 2.6676,
     so c ≈ 15.394 (CC: γ ≈ 2.944, c ≈ 16.99; CC Rem 6.12: 13 < c_best < 17).

**Numerical sign check** [N-here, float64, NOT certified]: `telperion/research/arch_rung/s12/s12_signs.py`
computes archW from the psiR integral, E from the χ double integral (S10's chiPoly), and SoninTr = archW + E,
for random lifts h.  Every sample has E < 0 and SoninTr > 0; at |I| = 1/2, B/‖h‖² ≤ 0.78; with ∫h = 0 at
|I| = log 2, B/‖h‖² ≤ 0.24; the 6.11 inequality holds with c = 15.394.  Output ends `ALL OK`.

## 2. Shared bridges

### A3 (done): the certified enumeration (`ArchS12_Index.lean`)

* `exists_certBasis_enumeration bR : ∃ σ : ℕ ≃ ι, ArchS10.CertBasis (prolateData bR σ)` for EVERY real
  prolate basis `bR`.  So the `D` of S7's `cc_thm47` (which holds for every σ) is exactly the `D` of
  S10/S11's χ theorems.  No independence-of-σ lemma is needed.
* Proof: S9's `prolate_spectrum_complete` applied to S6's family `(phiR bR, bR.μ)` (with S6's `parseval_ip`)
  gives exactly one index per window; `disjOK_eq` (`decide +kernel`) shows the 13 windows are pairwise
  disjoint, so the window indices are distinct; `exists_equiv_prefix` builds an `ℕ ≃ ι` with prescribed
  values on `{0..12}` (`Equiv.sumCompl` + `Cardinal.lift_mk_eq'` on the countably infinite complements).

### A1 + A2 (done): S11's form on [−L, L] as a function-level double integral (`ArchS12_Bridge.lean`)

* `re_inner_toLpI` (A2): for continuous F vanishing off [0, ℓ] and any continuous kernel κ,
  re⟪T_κ f, f⟫ = re ∫∫ conj F(x) κ(x, y) F(y) over ℝ², where f = `toLpI ℓ hF` is F in L²([0, ℓ]).
  Also `norm_sq_toLpI` (‖f‖² = ∫ conj F·F) and `inner_one_toLpI` (⟪1, f⟫ = ∫ F).
  Proof: S5's `inner_intOp_eq_integral`, a.e. identification through `quasiMeasurePreserving_fst/snd`,
  `volI_prod`, the vanishing off Icc², `integral_prod`.
* `double_integral_translate` (A1): ∫∫ conj h(x−L) k(y−x) h(y−L) = ∫∫ conj h(x) k(y−x) h(y)
  (`integral_sub_right_eq_self` twice).  F = h(· − L) is h moved from [−L, L] to [0, 2L].
* `double_chi_eq_chiT`: on [−L, L]² with 2L ≤ log 2, S8's χ(y − x) equals S11's clamped `chiK D`.
* Results, for `CertBasis D`, continuous h:
  * `form_chi_half`: tsupport h ⊆ [−1/4, 1/4] ⇒ re ∫∫ conj h(x) h(y) χ(y−x) ≤ 0.95921 · re ∫ conj h·h.
  * `form_chi_log2`: tsupport h ⊆ [−log2/2, log2/2] ⇒ re ∫∫ … ≤ 0.9995 · re ∫ conj h·h + 0.058‖∫h‖²/log 2.
* S8's `[α, α+ℓ]` intervals need no separate translation: `prop55_lift` is applied directly with α = −L.

## 3. S12a and S12b (done): `ArchS12_Main.lean`

Every statement uses the project definitions (`IsWeilTest`, `weilForm`, `autocorr`, `paperFT`, S3's `archW`,
S6's `soninProj`, S7's `theta`, S2's `qLift`).  The prolate data are existential inside the proofs
(`exists_certified_prolate`); the statements do not mention them, because the Sonin projection does not
depend on the basis.  In what follows SoninTr is `Σ_k ‖soninProj (theta g _ (e k))‖²` for ANY Hilbert basis e of
L²(ℝ)_ev, and h = `ArchS2.qLift g L` with ‖h‖² written `(∫ conj h · h).re`.

```lean
-- S12a: one condition (Yoshida's class), L ≤ 1/4 (|I| = 1/2)
theorem ArchS12.weil_positivity_one_condition_quarter_sonin (hg : IsWeilTest g) (hL : L ≤ 1/4)
    (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I/2) = 0) (e : HilbertBasis κ ℂ evenL2) :
    ∃ s, HasSum (fun k ↦ ‖soninProj (theta g _ (e k))‖ ^ 2) s ∧ 0 ≤ s ∧
      s + 1.87 * ‖h‖² ≤ (weilForm (autocorr g)).re
theorem ArchS12.weil_positivity_one_condition_quarter (…same hypotheses…) : 0 ≤ (weilForm (autocorr g)).re

-- S12b: CC Theorem 1, two conditions, 2L ≤ log 2 (|I| = log 2)
theorem ArchS12.cc_thm1 (hg) (hL : 2 * L ≤ log 2) (hsupp) (h0) (hz : paperFT g 0 = 0) (e) :
    ∃ s, HasSum (…) s ∧ 0 ≤ s ∧ s + 0.0229 * ‖h‖² ≤ ArchS3.archW g          -- W∞ ≥ SoninTr ≥ 0
theorem ArchS12.weil_positivity_cc_class (hg) (hL) (hsupp) (h0) (hz) : 0 ≤ (weilForm (autocorr g)).re

-- CC Theorem 6.11 form: one condition, full window
theorem ArchS12.cc_thm611 (hg) (hL : 2 * L ≤ log 2) (hsupp) (h0) (e) :
    ∃ s, HasSum (…) s ∧ 0 ≤ s ∧ s - 15.4 * ‖paperFT g 0‖ ^ 2 ≤ ArchS3.archW g
```

* **Margins.**  1.87 = 2·22.99·(1 − 0.95921) rounded down.  0.0229 = 2·22.99·(1 − 0.9995) rounded down.
* **The 6.11 constant.**  Exactly c = 8·0.058·ε'(1⁺)/log 2 = 4γ/log 2, with γ = 2ε'(1⁺)·0.058 ≈ 2.6676.
  So c ≈ 15.394.  The statement uses c = 15.4, from ε' ≤ 22.997 and log 2 > 0.6931.
  CC have γ ≈ 2.944 and c ≈ 16.99, and Rem 6.12 gives 13 < c_best < 17.
* **What is NEW against KWin.**  S12a's 0 ≤ Re weilForm is a special case of `KWin_Bridge.weil_positivity_prime_free_window`.
  The structural content is the Sonin lower bound and its proof route.
  S12b's W∞ ≥ SoninTr is not implied by KWin.
* **What is NOT proved.**  The one-condition statement (Y) at the full window is not proved by this route.
  It is covered by KWin only; see blueprint §2.2 and CC Rem 6.12.
  The conceptual one-condition route reaches 2L ≤ a* ≈ 0.558 [N-here], and only |I| = 1/2 is certified here.
  The mass identity ‖g‖² = ‖h'‖² + ¼‖h‖² (S2 open item) is not proved, so the margins are stated in ‖h‖², not ‖g‖².

Supporting theorems: `re_Eplus_lift` (−Re E = 2ε'(‖h‖² − re B), from `prop55_lift` with Qε = 2ε'χ),
`eps1_bounds` (22.99 ≤ ε'(1⁺) ≤ 22.997 from S10), `sonin_hasSum_lift` (SoninTr = archW − 2ε'(‖h‖² − re B)
for certified D), and `full_window_core`.

## 4. Files, sizes, axioms

| module | lines | content | `lake build` |
|---|---|---|---|
| ArchS12_Index | 169 | A3: window disjointness (`decide +kernel`), S9 completeness for a given bR, enumeration, `CertBasis` | ~32 s |
| ArchS12_Bridge | 226 | A1 + A2: Lp-to-function bridge, translation, χ on [−L, L], `form_chi_half`, `form_chi_log2` | ~35 s |
| ArchS12_Main | 247 | S12a, S12b, 6.11 | ~40 s |
| ArchS12_Guard | 54 | 39 `#print axioms` | |

* `lake build ArchS12_Guard` rebuilt from clean: all `ArchS12_*` oleans were deleted first, and the build finished with 8852 jobs.
* All 39 theorems print exactly `[propext, Classical.choice, Quot.sound]`.  There is no `sorry` and no `axiom`.
* **Wiring.**  `defaultTargets` and `AxiomGuardRvMBridge.lean` are untouched.
  The four `[[lean_lib]]` stanzas are at the end of `lakefile.toml`: ArchS12_Index, _Bridge, _Main, _Guard.

## 5. Lean footguns met

* **`Cardinal.eq` across universes.**  ℕ is in `Type 0`, while ι may be in any universe.
  Use `Cardinal.lift_mk_eq'` with `Cardinal.lift_aleph0` on both sides.
* **`if σ n = σ m` vs `if n = m`.**  After rewriting with `σ.injective.eq_iff`, the `Decidable` instances differ.
  Use `by_cases` with `if_neg` instead.
* **`psiS` vs `psi Data.Jd BR`.**  `simpa [ipS9, ip]` leaves one side unfolded; add `psiS` to the simp set.
* **`inner_self_eq_norm_sq_to_K` and `integral_ofReal` on ℂ.**  They use `RCLike.ofReal`, which does not match `Complex.ofReal` syntactically.
  Use `show … from by rw [inner_self_eq_norm_sq_to_K]; norm_cast`, and `integral_complex_ofReal`.
* **`HasCompactSupport.intro`.**  Give both `isCompact_Icc` factors explicit endpoints.
* **`rw [Measure.volume_eq_prod, integral_prod …]`.**  It leaves the goal with `(x, y).1` redexes; close it with `rfl`.
