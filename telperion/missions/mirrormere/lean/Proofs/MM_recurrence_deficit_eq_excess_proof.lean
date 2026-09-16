/-
  Proofs.MM_recurrence_deficit_eq_excess_proof -- AUTHORED proof of node
  MM_recurrence_deficit_eq_excess (Routes-roadmap E4a).

  Kernel-verified locally on rh/routes-node-proofs against the v4.32.0 toolchain
  (leanprover/lean4:v4.32.0), CoW-cloned quasicrystal-island Mathlib.
  `#print axioms recurrence_deficit_eq_excess` = [propext, Classical.choice,
  Quot.sound], 0 sorryAx.

  Vocabulary (recurrenceDeficit, excess, Aoff, Aon) is imported VERBATIM from
  Statements.MMDefs; recurrenceDeficit/excess are the AUTHORED registry defs
  (MMDefs.lean:61-62, 133) flagged there. Aoff/Aon/excess are the verbatim
  BraggDefect vocabulary (BraggDefect.lean:53,56,60). conjecture1_proved = False.

  Content: the algebraic identity (e^δ - 1)(1 - e^(-δ)) = e^δ + e^(-δ) - 2 at
  δ = 1/10 (via Real.exp_add / e^δ·e^(-δ)=1), plus strict positivity for all
  δ > 0 (both factors strictly positive: Real.one_lt_exp_iff, Real.exp_lt_one_iff).
-/
import Mathlib
import Statements.MMDefs

open Quasicrystal BraggDefect

theorem recurrence_deficit_eq_excess :
    recurrenceDeficit (1 / 10) = excess ∧
    ∀ δ : ℝ, 0 < δ → 0 < recurrenceDeficit δ := by
  constructor
  · -- the identity at δ = 1/10
    unfold recurrenceDeficit excess Aoff Aon
    have h : Real.exp (1 / 10) * Real.exp (-(1 / 10)) = 1 := by
      rw [← Real.exp_add]; norm_num
    ring_nf
    nlinarith [h]
  · -- strict positivity for every positive displacement
    intro δ hδ
    unfold recurrenceDeficit
    have h1 : 0 < Real.exp δ - 1 := by
      have := (Real.one_lt_exp_iff (x := δ)).mpr hδ
      linarith
    have h2 : 0 < 1 - Real.exp (-δ) := by
      have : Real.exp (-δ) < 1 := (Real.exp_lt_one_iff (x := -δ)).mpr (by linarith)
      linarith
    positivity
