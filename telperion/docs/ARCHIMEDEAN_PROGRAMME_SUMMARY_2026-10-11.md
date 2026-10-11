# Archimedean Weil positivity by the Connes-Consani route: programme summary (2026-10-11)

`conjecture1_proved = False`.  Nothing here is progress on the Riemann Hypothesis.  Everything below lives
below the first prime (2L ≤ log 2) or is a statement about the archimedean place alone.

## What is now kernel-checked (rvm_bridge island, Lean v4.33.0-rc2, axioms [propext, Classical.choice, Quot.sound])

| result | Lean name | content |
|---|---|---|
| CC Theorem 1 | `ArchS12.cc_thm1` | on CC's two-condition class (ĝ(i/2) = ĝ(0) = 0), 2L ≤ log 2: W∞ ≥ SoninTr ≥ 0, with margin 0.0229‖h‖² |
| CC Theorem 6.11 | `ArchS12.cc_thm611` | one condition: W∞ ≥ SoninTr − 15.4 |ĝ(0)|² (CC: c ≈ 17) |
| Weil positivity, CC class | `ArchS12.weil_positivity_cc_class` | 0 ≤ Re weilForm(autocorr g) on that class at the full window |
| conceptual one-condition rung | `ArchS12.weil_positivity_one_condition_quarter` | pole-free class, L ≤ 1/4, by the Sonin route |
| CC Theorem 4.7, unconditional | `ArchS7.cc_thm47`, `cc_thm47_nonneg` | SoninTr(g∗g*) = W∞ + E, hence W∞ + E ≥ 0 (CC (83)) |
| CC Corollary 2.3 | `ArchS3.cc_cor_2_3` | W∞ + D ≥ 0 for every support; ℓ(t) = ∫₁^∞ |Φ_t(a)|² da/a |
| CC Lemma 4.1 | `ArchS7b.δS_eq_deltaK`, `ArchS7.…Lemma41` | δ kernel = prolate series (75); two independent proofs |
| CC Thm 3.6 (jump lemma) | `ArchS4.jump_lemma_poleFree` | D∘Q = −2 Id + K^δ |
| CC Prop 4.5, (76)-(81) | `ArchS6.sonin_prolate_structure_real` | Sonin/prolate structure on L²(ℝ)_ev |
| CC §5 (Lemmas 5.1-5.4, Prop 5.5) | `ArchS8.*` | N_I = −2ε'(1⁺)(Id − K_I) as forms |
| certified prolate spectrum | `ArchPipeline.prolate_spectrum_certified` | c = 2π, 13 windows to 6.7e-43, all other |λ| ≤ 9.7e-22 |
| certified kernel χ, ε'(1⁺) | `ArchS10.chi_enclosure`, `eps1_enclosure` | |χ − chiPoly| ≤ 1.41e-7 on [0, log 2]; ε'(1⁺) = 22.99647568387053 ± 1.2e-22 |
| spectral certificate for K_I | `ArchS11.*` | λ_max ∈ [0.95920, 0.95921] at |I| = 1/2; at log 2: λ_max ∈ [1.05156, 1.0516], λ₂ ≤ 0.6866, N_I ≤ γ|⟨ξ₀|ξ⟩|², γ ≈ 2.668 (CC 2.944) |

New general infrastructure (not specific to this problem): L²-kernel integral operators (bounded, compact, self-adjoint,
Rayleigh top eigenvalue, min-max/Weyl, Hilbert-Schmidt identity, rank counting; `ArchS5_*`); L² Fourier transform =
Fourier integral on L¹ ∩ L² (`ArchS6.fourier_ae_eq`); Mellin transform of cos on the critical strip (`ArchS3_Mellin`).

## Where this goes beyond the source paper

* CC's Corollary 2.3 rests on a formal principal-value computation and a result quoted from Connes-Marcolli; S3 gives a
  rigorous route (damping by e^{−εs}, an exact identity for each ε, then ε → 0) with ℓ as a manifest squared norm.
* CC's §6 Toeplitz guesses, downloaded data and the floating-point bound ε₁ ≈ 0.00122 are replaced by kernel-checked
  certificates (S9-S11); the published constants are reproduced or improved (γ 2.944 → 2.668, c 17 → 15.4).
* Lemma 4.1 is proved without CC's trace manipulation (Parseval along the real eigenbasis).

## Relation to what main already had

`KWin_Bridge.weil_positivity_prime_free_window` (certificate, full IsWeilTest class, pole terms kept, 2L ≤ log 2) and
KWin2 (to 2L ≤ 1) remain the statements of record for Weil positivity on these windows.  The new content is the
conceptual proof and CC Theorem 1 itself (W∞ ≥ SoninTr, a stronger inequality than ≥ 0 on CC's class).

## What it does NOT give

* No positivity past the first prime by this route (the needed certified margins scale like e^{−(60..80)L²}).
* The one-condition statement on the full window is reachable by this route only to L ≈ 0.279 (proved here to 1/4).
* It cannot separate ζ from Davenport-Heilbronn (gate-0 Weil ladder: no rung below L ≈ 1.86 does).
* RH is not proved.

## Size and provenance

103 modules, ~24.5k Lean lines, 1,350 lines in AxiomGuardRvMBridge (all standard axioms, plus a few axiom-free data
lemmas).  Stage notes: telperion/docs/ARCH_S1_NOTES.md .. ARCH_S12_NOTES.md, ARCH_S7B_NOTES.md; blueprint:
ARCHIMEDEAN_CONCEPTUAL_BLUEPRINT_2026-10-11.md.  An independent second proof of Thm 4.7 exists on branch mm/arch-s7c
(not merged).  Work was done by Claude agents coordinated in one session; independent operator read-back and Comparator
judging have NOT been done.  No registry node has been added.
