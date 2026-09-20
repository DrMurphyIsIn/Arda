/-  LeakageNode.lean -- PROGRAM MIRRORMERE, ROUTE A item A2b: the registry node.

    Registry node: MM_leakage_composite_zero (telperion/missions/mirrormere).
    The statement is mirrored VERBATIM from
      telperion/missions/mirrormere/lean/Statements/MM_leakage_composite_zero.lean
    into this island's namespace, where `CompletelyMultiplicative`,
    `IsLogDerivCoeff` and `dhKappa` are the island's own definitions (character for
    character the statement module's) and `leak_dh_amp` is the emitter-generated
    Davenport-Heilbronn amplitude of `LeakageInstances.lean`.

    Four conjuncts:
      (i)   the dictionary -- completely multiplicative => zero COMPOSITE amplitude;
      (ii)  non-vacuity -- the hypothesis class is inhabited by a NON-zero functional;
      (iii) the certified DH instance -- the leak exists and is pinned to the
            published b(6) = +1.9364, and DH is refused complete multiplicativity;
      (iv)  the falsification twin -- (i) without its hypothesis is FALSE.

    Conjunct (iv) is what separates this node from the `rfl`-grade von Mangoldt
    support statement the roadmap flagged as a trap: a support-level reading admits
    no counterexample, and this one has an explicit kernel-checked counterexample.

    NOTHING is discharged from outside the kernel: no Arb enclosure, no hypothesis,
    no `sorry`.  conjecture1_proved = False (NOT a proof of RH).
-/
import LeakageDictionary
import LeakageInstances

namespace Quasicrystal

/-- **MM_leakage_composite_zero** -- the leakage dictionary, its non-vacuity, the
    certified Davenport-Heilbronn instance, and the falsification twin. -/
theorem leakage_composite_zero :
    (∀ a b : ℕ → ℝ, CompletelyMultiplicative a → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0)
    ∧ (∃ a b : ℕ → ℝ, CompletelyMultiplicative a ∧ IsLogDerivCoeff a b ∧
        b 2 ≠ 0 ∧ b 6 = 0)
    ∧ (∃ b : ℕ → ℝ, IsLogDerivCoeff LeakageInstances.leak_dh_amp b ∧
        (1.93635 : ℝ) < b 6 ∧ b 6 < (1.93636 : ℝ) ∧
        ¬ CompletelyMultiplicative LeakageInstances.leak_dh_amp)
    ∧ ¬ (∀ a b : ℕ → ℝ, a 1 = 1 → IsLogDerivCoeff a b →
        ∀ n : ℕ, 0 < n → ¬ IsPrimePow n → b n = 0) := by
  refine ⟨fun a b ha hb n hn hcomp => composite_bragg_amplitude_zero ha hb hn hcomp,
    exists_nondegenerate_cm_logDerivCoeff, ?_,
    LeakageInstances.leak_dh_multiplicativity_is_necessary⟩
  obtain ⟨b, hb⟩ := exists_logDerivCoeff (a := LeakageInstances.leak_dh_amp)
    (by norm_num [LeakageInstances.leak_dh_amp])
  obtain ⟨h1, h2⟩ := LeakageInstances.leak_dh_enclosure_decimal hb
  exact ⟨b, hb, by norm_num at h1 ⊢; linarith, by norm_num at h2 ⊢; linarith,
    LeakageInstances.leak_dh_not_completelyMultiplicative hb⟩

end Quasicrystal
