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
