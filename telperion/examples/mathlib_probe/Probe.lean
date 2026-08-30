/- PROBE 7: the full residue_logDeriv (order = residue of logDeriv), with 3 helper lemmas.
   If green, this is the reusable v4.32.0-gap-filling core. -/
import Mathlib
open Filter Topology

-- (A) transfer logDeriv through a punctured-neighborhood eventual equality.
theorem logDeriv_congr_punctured {f h : ℂ → ℂ} {z₀ : ℂ} (H : f =ᶠ[𝓝[≠] z₀] h) :
    logDeriv f =ᶠ[𝓝[≠] z₀] logDeriv h := by
  obtain ⟨s, hs_mem, hs_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp H
  rw [mem_nhdsWithin] at hs_mem
  obtain ⟨U, hUopen, hz₀U, hUsub⟩ := hs_mem
  have hmem : U ∩ {z₀}ᶜ ∈ 𝓝[≠] z₀ := by
    rw [mem_nhdsWithin]; exact ⟨U, hUopen, hz₀U, fun x hx => hx⟩
  filter_upwards [hmem] with z hz
  have hopen : IsOpen (U ∩ {z₀}ᶜ) := hUopen.inter isOpen_compl_singleton
  have hlocal : f =ᶠ[𝓝 z] h :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun x hx => hs_eq (hUsub hx))
  simp only [logDeriv, Pi.div_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]

-- (B) the split identity.
theorem logDeriv_zpow_smul_split (g : ℂ → ℂ) (z₀ w : ℂ) (n : ℤ) (hw : w ≠ z₀)
    (hg : DifferentiableAt ℂ g w) (hgw : g w ≠ 0) :
    logDeriv (fun z => (z - z₀) ^ n • g z) w = (n : ℂ) / (w - z₀) + logDeriv g w := by
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - z₀) w := by fun_prop
  have hbne : (w - z₀) ≠ 0 := sub_ne_zero.mpr hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) ^ n) w := hsub.zpow (Or.inl hbne)
  have hpne : (w - z₀) ^ n ≠ 0 := zpow_ne_zero _ hbne
  have hbase : (fun z : ℂ => (z - z₀) ^ n • g z) = (fun z => (z - z₀) ^ n * g z) := by
    funext z; rw [smul_eq_mul]
  have hld : logDeriv (fun z : ℂ => z - z₀) w = 1 / (w - z₀) := by
    have hd : deriv (fun z : ℂ => z - z₀) w = 1 := by simp
    show deriv (fun z : ℂ => z - z₀) w / (w - z₀) = 1 / (w - z₀)
    rw [hd]
  have hzp : logDeriv (fun z : ℂ => (z - z₀) ^ n) w = (n : ℂ) / (w - z₀) := by
    rw [logDeriv_fun_zpow hsub n, hld]; ring
  rw [hbase, logDeriv_mul w hpne hgw hpow hg, hzp]

-- (C) the analytic tail.
theorem tendsto_sub_mul_logDeriv_zero {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 0) := by
  have hc : ContinuousAt (logDeriv g) z₀ :=
    (hg.deriv.continuousAt).div hg.continuousAt hg0
  have h1 : Tendsto (fun z : ℂ => (z - z₀) * logDeriv g z) (𝓝[≠] z₀)
      (𝓝 ((z₀ - z₀) * logDeriv g z₀)) :=
    Tendsto.mul ((Continuous.tendsto (by fun_prop) z₀).mono_left nhdsWithin_le_nhds)
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using h1

-- THE LEMMA: residue of logDeriv = meromorphic order.
theorem residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    Tendsto (fun z => (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  have hcong : logDeriv f =ᶠ[𝓝[≠] z₀] logDeriv (fun z => (z - z₀) ^ n • g z) :=
    logDeriv_congr_punctured hfg
  have hgne : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hgdiff : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    filter_upwards [(hg.eventually_analyticAt).filter_mono nhdsWithin_le_nhds] with z hz
      using hz.differentiableAt
  have hev : (fun z => (z - z₀) * logDeriv f z)
      =ᶠ[𝓝[≠] z₀] (fun z => (n : ℂ) + (z - z₀) * logDeriv g z) := by
    filter_upwards [hcong, self_mem_nhdsWithin, hgne, hgdiff] with z hz hzne hgz hgd
    have hzne' : z ≠ z₀ := hzne
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne'
    rw [hz, logDeriv_zpow_smul_split g z₀ z n hzne' hgd hgz]
    field_simp
  rw [tendsto_congr' hev]
  simpa using (tendsto_const_nhds.add (tendsto_sub_mul_logDeriv_zero hg hg0))
