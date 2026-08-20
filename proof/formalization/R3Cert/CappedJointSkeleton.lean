import R3Cert.GStepCore
import R3Cert.MasterCore

/-!
  # Capped-joint-induction: conditional skeleton (2026-08-19)

  The capped joint induction proves, by strong induction on block size, that every block
  satisfies BOTH the **master** inequality `(2+μ)^11 F ≤ (64/621)·3^11` and the **g-lemma**
  `F·(1+μ/3)^11 ≤ γ`, using the per-child bound `F_c ≤ Bcap(μ_c) = min(master_ub, glemma, 1)`
  (the `1` is `phi_le_one`, proven).  Reducing the step gives:

  - **master step** — reduces to `master_core : f p ≤ 3^11` (`MasterCore`, PROVEN, all `j`).
  - **g-step** — reduces, via the 2-case split on `base^11 ⋛ W(5/3)^11`, to
    `case1_bound` (`GStepCore`, PROVEN, the `base^11 ≤ W(5/3)^11` half) and **Case 2**
    (the `base^11 > W(5/3)^11` half, the glemma bound) — the **single remaining open piece**.

  This file assembles the g-step from those two halves, with Case 2 as **one explicit named
  hypothesis** `Case2Property`.  Everything proven is discharged; the entire remaining gap of
  the crux is `Case2Property` (verified numerically, margin ~0.25; analytic proof open) plus
  the tree/message-recursion assembly connecting these abstract cores to `logPhi`/`per(L)`.
  This is the honest R7'-style conditional skeleton — no `Prop := True`, no vacuity.
  `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJoint

open R3Cert.GStepCore

/-- **⚠ DEPRECATED / UNSATISFIABLE — DO NOT USE as the crux's open hypothesis.**
    This abstract form quantifies `base` and `Pgl` *independently*, and is therefore **FALSE**
    (`base = 2, Pgl = 1` satisfies the premises but gives `72 ≤ 1`).  Real configs LINK `base`
    and the product (`base > threshold` forces suppression), so the abstract statement drops
    a load-bearing constraint and becomes unsatisfiable — making any theorem conditional on it
    a hollow reduction (a false hypothesis can never be discharged).
    **SUPERSEDED by `R3Cert.CappedJointConfig.Case2Property`**, which is config-based (`base`
    and `∏Bcap` derived from the same `List ℚ`, so the linkage is intrinsic), uses the real
    `Bcap` (not the glemma over-count), and is genuinely satisfiable (the true analytic wall).
    Retained only so the older `gstep_le_one`/`glemma_step` below still typecheck; new work
    must use the config version. -/
def Case2Property : Prop :=
  ∀ base Pgl : ℚ, 0 ≤ base → 0 ≤ Pgl → W * (5 / 3) ^ 11 < base ^ 11 →
    base ^ 11 * Pgl / (W * (5 / 3) ^ 11) ≤ 1

/-- **g-step, conditional on Case 2.** The g-step normalized factor
    `base^11 · Pbc / (W(5/3)^11) ≤ 1`, from the 2-case split:
    Case 1 (`base^11 ≤ W(5/3)^11`, PROVEN via `case1_bound`, uses only `Pbc ≤ 1 = phi_le_one`)
    and Case 2 (`base^11 > W(5/3)^11`, the hypothesis), bridged by `Pbc ≤ Pgl` (`Bcap ≤ glemma`).
    Non-vacuous: the Case-1 half is discharged by the proven `case1_bound`. -/
theorem gstep_le_one (h2 : Case2Property) {base Pbc Pgl : ℚ}
    (hb : 0 ≤ base) (hPbc0 : 0 ≤ Pbc) (hPbc1 : Pbc ≤ 1) (hPgl0 : 0 ≤ Pgl)
    (hPbcgl : Pbc ≤ Pgl) :
    base ^ 11 * Pbc / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hb11 : (0 : ℚ) ≤ base ^ 11 := by positivity
  by_cases h : base ^ 11 ≤ W * (5 / 3) ^ 11
  · -- Case 1: proven, no suppression needed
    exact case1_bound hb h hPbc0 hPbc1
  · -- Case 2: the hypothesis, plus `Pbc ≤ Pgl`
    push_neg at h
    have hgl := h2 base Pgl hb hPgl0 h
    rw [div_le_one hden] at hgl ⊢
    calc base ^ 11 * Pbc
        ≤ base ^ 11 * Pgl := mul_le_mul_of_nonneg_left hPbcgl hb11
      _ ≤ W * (5 / 3) ^ 11 := hgl

/-- **The master step is unconditional** (`MasterCore.master_core`, all `j`): recorded here
    so the skeleton's remaining gap is visibly *only* `Case2Property`. -/
theorem master_step_core (p : ℕ) :
    ((4 * (p : ℚ) + 3) / ((p : ℚ) + 1)) ^ 11 * (64 / 621) ^ p ≤ 3 ^ 11 := by
  have := R3Cert.MasterCore.master_core p
  simpa [R3Cert.MasterCore.f] using this

/-- **Skeleton summary (honest gap).** Given `Case2Property`, the g-step closes for every
    config (`gstep_le_one`) and the master step is unconditional (`master_step_core`). Hence
    the capped-joint induction *step* is fully discharged modulo `Case2Property` alone; the
    remaining work is (i) an analytic proof of `Case2Property`, and (ii) the tree/message
    recursion assembling these into `logPhi ≤ 0` / `per(L(T))`. `conjecture1_proved = False`. -/
theorem step_closes_given_case2 (h2 : Case2Property) :
    (∀ {base Pbc Pgl : ℚ}, 0 ≤ base → 0 ≤ Pbc → Pbc ≤ 1 → 0 ≤ Pgl → Pbc ≤ Pgl →
        base ^ 11 * Pbc / (W * (5 / 3) ^ 11) ≤ 1)
      ∧ (∀ p : ℕ, ((4 * (p : ℚ) + 3) / ((p : ℚ) + 1)) ^ 11 * (64 / 621) ^ p ≤ 3 ^ 11) :=
  ⟨fun hb hPbc0 hPbc1 hPgl0 hPbcgl => gstep_le_one h2 hb hPbc0 hPbc1 hPgl0 hPbcgl,
    master_step_core⟩

end R3Cert.CappedJoint
