/-  Probes/ArbEconomics_T100.lean -- KERNEL-CHECKED enclosure of zeta(1/2 + 100 i) (GENERATED; do not edit).

    `zeta_re`, `zeta_im` bound Re / Im of riemannZeta (1/2 + 100 i) with NO hypotheses:
      * the Dirichlet sum over n = 1..499 is kernel-evaluated in 1 `decide +kernel` chunks
        (parts P0..P0) and composed by `ArbEcon.chunk_sound` (ArbEconomics_Sound);
      * the EM order-3 tail at N = 500 is `EMZetaTail.em_zeta_critical_line3_enclosure`
        (via `ArbEcon.em3_remainder_le`, E = Q / (180 N^2 r), Q = 500218743/500, r = 22);
      * `ArbEcon.zeta_re_bounds` / `zeta_im_bounds` (ArbEconomics_Zeta) assemble the result.
    Certified: Re in [2.69160959, 2.69363068], Im in [-0.02139701, -0.01937591] (width dominated by E).
    conjecture1_proved = False.  One height, finite interval arithmetic; nothing about RH.
-/
import Probes.ArbEconomics_Zeta
import Probes.ArbEconomics_T100_P0

namespace ArbEcon.I_T100

theorem valid : ArbEcon.Valid cfg (100 : ℝ) 9 where
  one_eq := by decide
  two1_eq := by decide
  oneSq_eq := by decide
  t_eq := by show (100 : ℝ) = ((100 : ℕ) : ℝ) / 2 ^ (0 : ℕ); norm_num
  pi_ball := by
    show |Real.pi / 2 * 2 ^ (64 : ℕ) - ((28976077832308491369 : ℕ) : ℝ)| ≤ ((2 : ℕ) : ℝ)
    have h1 := Real.pi_gt_d20
    have h2 := Real.pi_lt_d20
    rw [abs_le]; constructor <;> norm_num <;> linarith
  umax_le := by decide
  dcos_eq := by decide
  dsin_eq := by decide
  tau_ok := by
    show (2 : ℝ) ^ (64 : ℕ) * ArbEcon.taylorBnd 9 ≤ ((1 : ℕ) : ℝ)
    unfold ArbEcon.taylorBnd; norm_num [Nat.factorial]
  hc_eq := fun _ => rfl
  hs_eq := fun _ => rfl
  lnf_eq := fun _ => rfl

theorem inv_0 : ArbEcon.Inv cfg (100 : ℝ) 1 s0 := ArbEcon.inv_init cfg _ valid.one_eq
theorem inv_1 : ArbEcon.Inv cfg (100 : ℝ) 499 s1 :=
  ArbEcon.chunk_sound cfg _ 9 valid 498 1 s0 s1 inv_0 chunk_0
theorem inv_N : ArbEcon.Inv cfg (100 : ℝ) 500 sN :=
  ArbEcon.chunk_sound cfg _ 9 valid 1 499 s1 sN inv_1 chunk_N

theorem remainder :
    ‖riemannZeta (ArbEcon.sOf 100) - ZetaReflection.emZetaFinite3 (ArbEcon.sOf 100) 500‖
      ≤ ((500218743 : ℝ) / 500) / (180 * (500 : ℝ) ^ 2 * (22 : ℕ)) :=
  ArbEcon.em3_remainder_le 100 500 (by norm_num) _ (by norm_num) (by norm_num) 22 (by norm_num) (by norm_num)

/-- **Re zeta(1/2 + 100 i)**, kernel-checked, no hypotheses. -/
theorem zeta_re : ((269160959 : ℝ) / 100000000) ≤ (riemannZeta ((1 / 2 : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re ∧
    (riemannZeta ((1 / 2 : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re ≤ ((67340767 : ℝ) / 25000000) :=
  ArbEcon.zeta_re_bounds cfg 100 500 (by norm_num) s1 sN inv_1 inv_N _ remainder ((228046001 : ℝ) / 480012000) ((11959999 : ℝ) / 2400060) ((269160959 : ℝ) / 100000000) ((67340767 : ℝ) / 25000000)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by norm_num [s1, sN, cfg]) (by norm_num [s1, sN, cfg])

/-- **Im zeta(1/2 + 100 i)**, kernel-checked, no hypotheses. -/
theorem zeta_im : ((-2139701 : ℝ) / 100000000) ≤ (riemannZeta ((1 / 2 : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).im ∧
    (riemannZeta ((1 / 2 : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).im ≤ ((-1937591 : ℝ) / 100000000) :=
  ArbEcon.zeta_im_bounds cfg 100 500 (by norm_num) s1 sN inv_1 inv_N _ remainder ((228046001 : ℝ) / 480012000) ((11959999 : ℝ) / 2400060) ((-2139701 : ℝ) / 100000000) ((-1937591 : ℝ) / 100000000)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by norm_num [s1, sN, cfg]) (by norm_num [s1, sN, cfg])

end ArbEcon.I_T100
