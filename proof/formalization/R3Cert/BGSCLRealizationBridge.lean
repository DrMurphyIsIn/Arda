/-
  Gap-2 realization bridge (capstone).

  Connects the ANALYTIC Branch/logPhi world (where `phi_le_one : logPhi b ≤ 0` is proven)
  to the COMBINATORIAL real-Laplacian world (where the objective
  `per(L(T)) / ∏deg` lives), for EVERY rooted tree.

  BACKGROUND / GAP MAP.  The two worlds are already joined by a chain of CI-green lemmas that
  this file only had to *compose* into a single end-to-end statement:

    (analytic, per branch)
      `phi_le_one`                : logPhi b ≤ 0                              [PotentialFinal]
      `exp_logPhi_mul_rhoB_pow`   : exp(logPhi b)·rhoB^(Vb b) = Ztot(litRealize b)  [BridgeStep4c]
    (realization, per tree)
      `Ztot_dtSub_eq_lit`         : Ztot(dtSub t) = Ztot(litRealize (parseB t))     [R47Parse]
      `Vb_parseB`                 : Vb (parseB t) = usize t                          [R47Parse]
      ⟹ `Ztot_dtSub_le_rhoB_pow` : Ztot(dtSub t) ≤ rhoB^(usize t)                  [R47RateZBound]
    (rooting, per tree)
      `rooting_identity`          : (d+1)·Ztot(dtSub t) = d·Aobj t + Zopen(dtSub t) [R47RootRate]
      ⟹ `Aobj_le_rooting_rate`   : Aobj t ≤ (d+1)/d·rhoB^(usize t)                 [R47RootRate]
    (objective = real permanent ratio)
      `pi_utree`                  : per(L(realize(dtRealize t)))/∏deg = Aobj t      [R47Tree]

  The realization bridge that Gap 2 asks for is precisely the COMPOSITION `pi_utree` ∘
  `Aobj_le_rooting_rate`: it turns the analytic ceiling `logPhi ≤ 0` into a statement about the
  real Laplacian permanent ratio of the true-degree tree graph.  That composite is what this file
  states as a single theorem (it did not previously exist as one).  The `p → ∞` cherry-hub
  decoupling limit (`Step4.hub_rho0_limit`, BridgeStep4) is the analytic *definition* mechanism of
  the amplitude; the FINITE amplitude identity `exp_logPhi_mul_rhoB_pow` already discharges the
  amplitude-ratio identity at every branch, so the composed bound below needs no separate `O(1/p²)`
  remainder — the remainder was absorbed once and for all into that finite identity.

  HONEST SCOPE.  This is the composition of the WEAK master bound (`Φ ≤ 1`, i.e. `logPhi ≤ 0`).
  The single analytic input `phi_le_one` itself rests on the open Gap-1 valid-potential existence
  (`Reach.ValidPotential`); everything downstream of `phi_le_one` is unconditional and kernel-checked
  here.  The resulting rate `(d+1)/d·rhoB^n` (≤ `6/5·rhoB^n` at a capped root) sits ABOVE the tie
  `≈0.92·rhoB^n`, so it does NOT by itself close the Hdom domination layer / Conjecture 1 — the
  rooting/Ztot trade-off remains the open combinatorial crux.  `conjecture1_proved = False`.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.R47Tree
import R3Cert.R47RootRate

namespace R3Cert
namespace Step3

open RTree

/-- **The realization bridge (rate form).**  For every rooted tree `t = node cs` with a nonempty
    root (`d = |cs| ≥ 1` children), the REAL Laplacian permanent ratio of the true-degree tree
    graph is bounded by the analytic rate:

      `per(L(realize(dtRealize t))) / ∏deg  ≤  (d+1)/d · rhoB^(usize t)`.

    This is `pi_utree` (the ratio *is* `Aobj t`) composed with `Aobj_le_rooting_rate` (the analytic
    ceiling `logPhi ≤ 0` transported onto `Aobj`).  It is the exact object Gap 2 asks to construct:
    the analytic `Φ ≤ 1` ceiling realized as a statement about the real permanent ratio. -/
theorem perm_ratio_le_rate (cs : List UTree) (hpos : 0 < cs.length) :
    (lapl (aGraph (realize (dtRealize (UTree.node cs))))).permanent
        / (∏ v, ((aGraph (realize (dtRealize (UTree.node cs)))).degree v : ℝ))
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ)
          * rhoB ^ usize (UTree.node cs) := by
  rw [pi_utree]
  exact Aobj_le_rooting_rate cs hpos

/-- **The realization bridge (capped-root form).**  For a nonempty backbone whose root hub carries
    `≥ 5` arms (any `Capped` state — the Hdom domain), the real Laplacian permanent ratio is bounded
    by `(6/5)·rhoB^n`.  Same composition as `perm_ratio_le_rate`, specialized through
    `Aobj_backbone_le_rate` at a capped root degree `d ≥ 5` (so `(d+1)/d ≤ 6/5`). -/
theorem perm_ratio_backbone_le_rate (arms : List ℕ) (c : ℕ) (rest : List Hub)
    (hcap : 5 ≤ arms.length) :
    (lapl (aGraph (realize (dtRealize (backboneU ((arms, c) :: rest)))))).permanent
        / (∏ v, ((aGraph (realize (dtRealize (backboneU ((arms, c) :: rest))))).degree v : ℝ))
      ≤ (6 / 5 : ℝ) * rhoB ^ usize (backboneU ((arms, c) :: rest)) := by
  rw [pi_utree]
  exact Aobj_backbone_le_rate arms c rest hcap

/-- **The realization bridge, factored through the analytic ceiling explicitly.**  The same rate
    bound as `perm_ratio_le_rate`, but stated to expose that the ONLY analytic input is the ceiling
    `logPhi (parseB t) ≤ 0` (the `Φ ≤ 1` master bound = Gap 1's downstream shadow): given that
    ceiling as a hypothesis, the real permanent ratio bound follows unconditionally.  Instantiating
    the hypothesis with `phi_le_one` recovers `perm_ratio_le_rate`; isolating it here marks the exact
    analytic seam the bridge rests on. -/
theorem perm_ratio_le_rate_of_ceiling (cs : List UTree) (hpos : 0 < cs.length)
    (hceil : logPhi (parseB (UTree.node cs)) ≤ 0) :
    (lapl (aGraph (realize (dtRealize (UTree.node cs))))).permanent
        / (∏ v, ((aGraph (realize (dtRealize (UTree.node cs)))).degree v : ℝ))
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ)
          * rhoB ^ usize (UTree.node cs) := by
  -- Re-run the realization chain with the supplied ceiling in place of `phi_le_one`.
  have hZsub : Ztot (dtSub (UTree.node cs)) ≤ rhoB ^ usize (UTree.node cs) := by
    have hb : Real.exp (logPhi (parseB (UTree.node cs))) * rhoB ^ usize (UTree.node cs)
        = Ztot (litRealize (parseB (UTree.node cs))) := by
      have h := exp_logPhi_mul_rhoB_pow (parseB (UTree.node cs))
      rwa [Vb_parseB] at h
    rw [Ztot_dtSub_eq_lit (UTree.node cs), ← hb]
    have hexp : Real.exp (logPhi (parseB (UTree.node cs))) ≤ 1 :=
      Real.exp_le_one_iff.mpr hceil
    have hpow : (0 : ℝ) ≤ rhoB ^ usize (UTree.node cs) := le_of_lt (pow_pos rhoB_pos _)
    calc Real.exp (logPhi (parseB (UTree.node cs))) * rhoB ^ usize (UTree.node cs)
        ≤ 1 * rhoB ^ usize (UTree.node cs) := mul_le_mul_of_nonneg_right hexp hpow
      _ = rhoB ^ usize (UTree.node cs) := one_mul _
  -- Feed the Z-bound through the rooting identity, then to the real permanent ratio.
  have hroot : Aobj (UTree.node cs)
      ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * rhoB ^ usize (UTree.node cs) := by
    have h1 := Aobj_le_rooting cs hpos
    have hfac : (0 : ℝ) ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) := by positivity
    calc Aobj (UTree.node cs)
        ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * Ztot (dtSub (UTree.node cs)) := h1
      _ ≤ ((cs.length : ℝ) + 1) / (cs.length : ℝ) * rhoB ^ usize (UTree.node cs) :=
          mul_le_mul_of_nonneg_left hZsub hfac
  rw [pi_utree]
  exact hroot

end Step3
end R3Cert
