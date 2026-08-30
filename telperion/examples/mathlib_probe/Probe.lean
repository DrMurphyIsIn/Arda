/- PROBE 6: the three crux sublemmas for residue_logDeriv, as independent decls. -/
import Mathlib
open Filter Topology

-- (A) transfer logDeriv through a punctured-neighborhood eventual equality.
example {f h : ℂ → ℂ} {z₀ : ℂ} (H : f =ᶠ[𝓝[≠] z₀] h) :
    logDeriv f =ᶠ[𝓝[≠] z₀] logDeriv h := by
  obtain ⟨s, hs_mem, hs_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp H
  rw [mem_nhdsWithin] at hs_mem
  obtain ⟨U, hUopen, hz₀U, hUsub⟩ := hs_mem
  have hmem : U ∩ {z₀}ᶜ ∈ 𝓝[≠] z₀ := by
    rw [mem_nhdsWithin]; exact ⟨U, hUopen, hz₀U, fun x hx => hx⟩
  filter_upwards [hmem, H] with z hz hzeq
  have hopen : IsOpen (U ∩ {z₀}ᶜ) := hUopen.inter isOpen_compl_singleton
  have hlocal : f =ᶠ[𝓝 z] h :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun x hx => hs_eq (hUsub hx))
  simp only [logDeriv, hlocal.deriv_eq, hlocal.eq_of_nhds]

-- (B) the split identity.
example (g : ℂ → ℂ) (z₀ w : ℂ) (n : ℤ) (hw : w ≠ z₀)
    (hg : DifferentiableAt ℂ g w) (hgw : g w ≠ 0) :
    logDeriv (fun z => (z - z₀) ^ n • g z) w = (n : ℂ) / (w - z₀) + logDeriv g w := by
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - z₀) w := by fun_prop
  have hbne : (w - z₀) ≠ 0 := sub_ne_zero.mpr hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) ^ n) w := hsub.zpow (Or.inl hbne) n
  have hpne : (w - z₀) ^ n ≠ 0 := zpow_ne_zero _ hbne
  have hbase : (fun z : ℂ => (z - z₀) ^ n • g z) = (fun z => (z - z₀) ^ n * g z) := by
    funext z; rw [smul_eq_mul]
  rw [hbase, logDeriv_mul w hpne hgw hpow hg, logDeriv_fun_zpow hsub n]
  have hld : logDeriv (fun z : ℂ => z - z₀) w = 1 / (w - z₀) := by
    simp only [logDeriv, sub_zero]
    rw [deriv_sub_const]
    simp
  rw [hld]; field_simp

-- (C) the analytic tail: (z-z0)*logDeriv g z -> 0  for g analytic at z0, g z0 != 0.
example {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 0) := by
  have hc : ContinuousAt (logDeriv g) z₀ := by
    have : logDeriv g = fun z => deriv g z / g z := rfl
    rw [this]
    exact (hg.deriv.continuousAt).div hg.continuousAt hg0
  have h1 : Tendsto (fun z : ℂ => (z - z₀) * logDeriv g z) (𝓝[≠] z₀)
      (𝓝 ((z₀ - z₀) * logDeriv g z₀)) := by
    apply Tendsto.mul
    · exact (Continuous.tendsto (by fun_prop) z₀).mono_left nhdsWithin_le_nhds
    · exact (hc.tendsto).mono_left nhdsWithin_le_nhds
  simpa using h1
