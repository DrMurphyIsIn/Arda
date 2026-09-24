/-  Probes/ArbEconomics_T1000.lean -- KERNEL-CHECKED enclosure of zeta(1/2 + 1000 i) (GENERATED; do not edit).

    `zeta_re`, `zeta_im` bound Re / Im of riemannZeta (1/2 + 1000 i) with NO hypotheses:
      * the Dirichlet sum over n = 1..7999 is kernel-evaluated in 16 `decide +kernel` chunks
        (parts P0..P0) and composed by `ArbEcon.chunk_sound` (ArbEconomics_Sound);
      * the EM order-3 tail at N = 8000 is `EMZetaTail.em_zeta_critical_line3_enclosure`
        (via `ArbEcon.em3_remainder_le`, E = Q / (180 N^2 r), Q = 1000004374999/1000, r = 89);
      * `ArbEcon.zeta_re_bounds` / `zeta_im_bounds` (ArbEconomics_Zeta) assemble the result.
    Certified: Re in [0.35535899, 0.3573097], Im in [0.9310225, 0.9329732] (width dominated by E).
    conjecture1_proved = False.  One height, finite interval arithmetic; nothing about RH.
-/
import Probes.ArbEconomics_Zeta
import Probes.ArbEconomics_T1000_P0

namespace ArbEcon.I_T1000

theorem valid : ArbEcon.Valid cfg (1000 : ℝ) 9 where
  one_eq := by decide
  two1_eq := by decide
  oneSq_eq := by decide
  t_eq := by show (1000 : ℝ) = ((1000 : ℕ) : ℝ) / 2 ^ (0 : ℕ); norm_num
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

theorem inv_0 : ArbEcon.Inv cfg (1000 : ℝ) 1 s0 := ArbEcon.inv_init cfg _ valid.one_eq
theorem inv_1 : ArbEcon.Inv cfg (1000 : ℝ) 501 s1 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 1 s0 s1 inv_0 chunk_0
theorem inv_2 : ArbEcon.Inv cfg (1000 : ℝ) 1001 s2 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 501 s1 s2 inv_1 chunk_1
theorem inv_3 : ArbEcon.Inv cfg (1000 : ℝ) 1501 s3 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 1001 s2 s3 inv_2 chunk_2
theorem inv_4 : ArbEcon.Inv cfg (1000 : ℝ) 2001 s4 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 1501 s3 s4 inv_3 chunk_3
theorem inv_5 : ArbEcon.Inv cfg (1000 : ℝ) 2501 s5 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 2001 s4 s5 inv_4 chunk_4
theorem inv_6 : ArbEcon.Inv cfg (1000 : ℝ) 3001 s6 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 2501 s5 s6 inv_5 chunk_5
theorem inv_7 : ArbEcon.Inv cfg (1000 : ℝ) 3501 s7 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 3001 s6 s7 inv_6 chunk_6
theorem inv_8 : ArbEcon.Inv cfg (1000 : ℝ) 4001 s8 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 3501 s7 s8 inv_7 chunk_7
theorem inv_9 : ArbEcon.Inv cfg (1000 : ℝ) 4501 s9 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 4001 s8 s9 inv_8 chunk_8
theorem inv_10 : ArbEcon.Inv cfg (1000 : ℝ) 5001 s10 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 4501 s9 s10 inv_9 chunk_9
theorem inv_11 : ArbEcon.Inv cfg (1000 : ℝ) 5501 s11 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 5001 s10 s11 inv_10 chunk_10
theorem inv_12 : ArbEcon.Inv cfg (1000 : ℝ) 6001 s12 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 5501 s11 s12 inv_11 chunk_11
theorem inv_13 : ArbEcon.Inv cfg (1000 : ℝ) 6501 s13 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 6001 s12 s13 inv_12 chunk_12
theorem inv_14 : ArbEcon.Inv cfg (1000 : ℝ) 7001 s14 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 6501 s13 s14 inv_13 chunk_13
theorem inv_15 : ArbEcon.Inv cfg (1000 : ℝ) 7501 s15 :=
  ArbEcon.chunk_sound cfg _ 9 valid 500 7001 s14 s15 inv_14 chunk_14
theorem inv_16 : ArbEcon.Inv cfg (1000 : ℝ) 7999 s16 :=
  ArbEcon.chunk_sound cfg _ 9 valid 498 7501 s15 s16 inv_15 chunk_15
theorem inv_N : ArbEcon.Inv cfg (1000 : ℝ) 8000 sN :=
  ArbEcon.chunk_sound cfg _ 9 valid 1 7999 s16 sN inv_16 chunk_N

theorem remainder :
    ‖riemannZeta (ArbEcon.sOf 1000) - ZetaReflection.emZetaFinite3 (ArbEcon.sOf 1000) 8000‖
      ≤ ((1000004374999 : ℝ) / 1000) / (180 * (8000 : ℝ) ^ 2 * (89 : ℕ)) :=
  ArbEcon.em3_remainder_le 1000 8000 (by norm_num) _ (by norm_num) (by norm_num) 89 (by norm_num) (by norm_num)

/-- **Re zeta(1/2 + 1000 i)**, kernel-checked, no hypotheses. -/
theorem zeta_re : ((35535899 : ℝ) / 100000000) ≤ (riemannZeta ((1 / 2 : ℂ) + ((1000 : ℝ) : ℂ) * Complex.I)).re ∧
    (riemannZeta ((1 / 2 : ℂ) + ((1000 : ℝ) : ℂ) * Complex.I)).re ≤ ((3573097 : ℝ) / 10000000) :=
  ArbEcon.zeta_re_bounds cfg 1000 8000 (by norm_num) s16 sN inv_16 inv_N _ remainder ((380932096001 : ℝ) / 768000192000) ((3067999999 : ℝ) / 384000096) ((35535899 : ℝ) / 100000000) ((3573097 : ℝ) / 10000000)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by norm_num [s16, sN, cfg]) (by norm_num [s16, sN, cfg])

/-- **Im zeta(1/2 + 1000 i)**, kernel-checked, no hypotheses. -/
theorem zeta_im : ((372409 : ℝ) / 400000) ≤ (riemannZeta ((1 / 2 : ℂ) + ((1000 : ℝ) : ℂ) * Complex.I)).im ∧
    (riemannZeta ((1 / 2 : ℂ) + ((1000 : ℝ) : ℂ) * Complex.I)).im ≤ ((2332433 : ℝ) / 2500000) :=
  ArbEcon.zeta_im_bounds cfg 1000 8000 (by norm_num) s16 sN inv_16 inv_N _ remainder ((380932096001 : ℝ) / 768000192000) ((3067999999 : ℝ) / 384000096) ((372409 : ℝ) / 400000) ((2332433 : ℝ) / 2500000)
    (by rw [abs_le]; constructor <;> norm_num) (by rw [abs_le]; constructor <;> norm_num)
    (by norm_num [s16, sN, cfg]) (by norm_num [s16, sN, cfg])

end ArbEcon.I_T1000
