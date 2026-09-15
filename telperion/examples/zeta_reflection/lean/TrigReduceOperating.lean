/-  TrigReduceOperating.lean -- ANDÚRIL instrument (A): OPERATING-POINT CERTIFICATES.

    The four kernel-checked cos/sin boxes at the EXACT points the zero-hypothesis reflected-band
    evaluator hits (`FullyReflectedBand_t14`): `t = 14`, `n ∈ {2, 200}`, arguments `θ = t·log n` up
    to ≈ 74.23 -- nearly 12 full `2π` wraps, far outside Mathlib's `|x| ≤ 1` base brackets.

    Each certificate is built by the π-free double-angle route (`TrigReduce`):
      1. `θ` enters as a VERIFIED DYADIC ENCLOSURE `|θ − c| ≤ w` (`thetaT*`), from Mathlib's `log`
         d9 bounds via `log 200 = 3 log 2 + 2 log 5` -- the corpus expLo/expHi-style algebraic check.
      2. the sample `c = 2^M·y` is reduced to `|y| ≤ 1`, base-bracketed (`base*`), and the argument
         DOUBLED back up `M` times (`climb*`, M = 22 for n=2, 26 for n=200) with the paired
         `cos_double_interval` / `sin_double_interval` recurrence.
      3. the argument-box width `w` is absorbed by Lipschitz (`cos_encl_bracket` / `sin_encl_bracket`).

    ACHIEVED WIDTHS (all ≤ 1e-4, the acceptance target):
      * cos(14·log 2)   width ≈ 5.93e-07     sin(14·log 2)   width ≈ 2.42e-06
      * cos(14·log 200) width ≈ 6.61e-05     sin(14·log 200) width ≈ 8.86e-05

    Everything guarded (no sorry; AxiomGuardTrigReduce prints the 3-axiom set).
    conjecture1_proved = False.  Certified interval arithmetic for cos/sin at large arguments.
-/
import TrigReduce
import Mathlib.Analysis.Complex.ExponentialBounds

open TrigReduce Real

namespace TrigReduceOperating

/-! ### Operating point T2: θ = 14·log 2 ≈ 9.704061  (argument ≈ 9.70). -/
section T2
/-- reduced argument `y = c/2^22` with `c = 682862552768086/2^46` (exact dyadic rational), `|y| ≤ 1`. -/
private noncomputable def yT2 : ℝ := (341431276384043 / 147573952589676412928)
private theorem hyT2 : |yT2| ≤ 1 := by unfold yT2; rw [abs_le]; constructor <;> norm_num
/-- base cos/sin brackets at `y` (order-4/5 Taylor, `|y| ≤ 1`). -/
private theorem baseT2 :
    ((1152921504603761253 / 1152921504606846976) : ℝ) ≤ Real.cos yT2 ∧ Real.cos yT2 ≤ (576460752301880627 / 576460752303423488) ∧
    ((2667431846747 / 1152921504606846976) : ℝ) ≤ Real.sin yT2 ∧ Real.sin yT2 ≤ (666857961687 / 288230376151711744) := by
  have hc := cos_base_interval (y := yT2) hyT2 (clo := (1152921504603761253 / 1152921504606846976)) (chi := (576460752301880627 / 576460752303423488)) (by unfold yT2; norm_num) (by unfold yT2; norm_num)
  have hs := sin_base_interval (y := yT2) hyT2 (slo := (2667431846747 / 1152921504606846976)) (shi := (666857961687 / 288230376151711744)) (by unfold yT2; norm_num) (by unfold yT2; norm_num)
  exact ⟨hc.1, hc.2, hs.1, hs.2⟩
/-- **π-free double-angle climb** (22 steps): cos/sin of `2^22·y = c`. -/
private theorem climbT2 :
    ((-554125208006725529 / 576460752303423488) : ℝ) ≤ Real.cos ((2:ℝ)^22 * yT2) ∧ Real.cos ((2:ℝ)^22 * yT2) ≤ (-138531218710871479 / 144115188075855872) ∧
    ((-158910864482060217 / 576460752303423488) : ℝ) ≤ Real.sin ((2:ℝ)^22 * yT2) ∧ Real.sin ((2:ℝ)^22 * yT2) ≤ (-79454738382511901 / 288230376151711744) := by
  obtain ⟨hc0lo, hc0hi, hs0lo, hs0hi⟩ := baseT2
  have hcd1 := cos_double_interval (y := yT2) (clo := (1152921504603761253 / 1152921504606846976)) (chi := (576460752301880627 / 576460752303423488)) (clo' := (288230376148626021 / 288230376151711744)) (chi' := (1152921504594504089 / 1152921504606846976)) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := sin_double_interval (y := yT2) (clo := (1152921504603761253 / 1152921504606846976)) (chi := (576460752301880627 / 576460752303423488)) (slo := (2667431846747 / 1152921504606846976)) (shi := (666857961687 / 288230376151711744)) (slo' := (5334863693479 / 1152921504606846976)) (shi' := (2667431846741 / 576460752303423488)) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*yT2 = (2:ℝ)^1 * yT2 by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := cos_double_interval (y := ((2:ℝ)^1 * yT2)) (clo := (288230376148626021 / 288230376151711744)) (chi := (1152921504594504089 / 1152921504606846976)) (clo' := (72057594034842213 / 72057594037927936)) (chi' := (1152921504557475429 / 1152921504606846976)) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := sin_double_interval (y := ((2:ℝ)^1 * yT2)) (clo := (288230376148626021 / 288230376151711744)) (chi := (1152921504594504089 / 1152921504606846976)) (slo := (5334863693479 / 1152921504606846976)) (shi := (2667431846741 / 576460752303423488)) (slo' := (10669727386843 / 1152921504606846976)) (shi' := (5334863693425 / 576460752303423488)) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * yT2) = (2:ℝ)^2 * yT2 by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := cos_double_interval (y := ((2:ℝ)^2 * yT2)) (clo := (72057594034842213 / 72057594037927936)) (chi := (1152921504557475429 / 1152921504606846976)) (clo' := (18014398506396261 / 18014398509481984)) (chi' := (1152921504409360789 / 1152921504606846976)) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := sin_double_interval (y := ((2:ℝ)^2 * yT2)) (clo := (72057594034842213 / 72057594037927936)) (chi := (1152921504557475429 / 1152921504606846976)) (slo := (10669727386843 / 1152921504606846976)) (shi := (5334863693425 / 576460752303423488)) (slo' := (5334863693193 / 288230376151711744)) (shi' := (21339454772787 / 1152921504606846976)) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * yT2) = (2:ℝ)^3 * yT2 by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := cos_double_interval (y := ((2:ℝ)^3 * yT2)) (clo := (18014398506396261 / 18014398509481984)) (chi := (1152921504409360789 / 1152921504606846976)) (clo' := (4503599624284773 / 4503599627370496)) (chi' := (1152921503816902229 / 1152921504606846976)) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := sin_double_interval (y := ((2:ℝ)^3 * yT2)) (clo := (18014398506396261 / 18014398509481984)) (chi := (1152921504409360789 / 1152921504606846976)) (slo := (5334863693193 / 288230376151711744)) (shi := (21339454772787 / 1152921504606846976)) (slo' := (42678909538233 / 1152921504606846976)) (shi' := (5334863692283 / 144115188075855872)) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * yT2) = (2:ℝ)^4 * yT2 by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  have hcd5 := cos_double_interval (y := ((2:ℝ)^4 * yT2)) (clo := (4503599624284773 / 4503599627370496)) (chi := (1152921503816902229 / 1152921504606846976)) (clo' := (1152921501447066625 / 1152921504606846976)) (chi' := (576460750723533995 / 576460752303423488)) hc4lo hc4hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd5 := sin_double_interval (y := ((2:ℝ)^4 * yT2)) (clo := (4503599624284773 / 4503599627370496)) (chi := (1152921503816902229 / 1152921504606846976)) (slo := (42678909538233 / 1152921504606846976)) (shi := (5334863692283 / 144115188075855872)) (slo' := (85357819017981 / 1152921504606846976)) (shi' := (21339454754511 / 288230376151711744)) hc4lo hc4hi hs4lo hs4hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^4 * yT2) = (2:ℝ)^5 * yT2 by ring] at hcd5 hsd5
  obtain ⟨hc5lo, hc5hi⟩ := hcd5
  obtain ⟨hs5lo, hs5hi⟩ := hsd5
  have hcd6 := cos_double_interval (y := ((2:ℝ)^5 * yT2)) (clo := (1152921501447066625 / 1152921504606846976)) (chi := (576460750723533995 / 576460752303423488)) (clo' := (1152921491967725589 / 1152921504606846976)) (chi' := (576460745983865525 / 576460752303423488)) hc5lo hc5hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd6 := sin_double_interval (y := ((2:ℝ)^5 * yT2)) (clo := (1152921501447066625 / 1152921504606846976)) (chi := (576460750723533995 / 576460752303423488)) (slo := (85357819017981 / 1152921504606846976)) (shi := (21339454754511 / 288230376151711744)) (slo' := (85357818784043 / 576460752303423488)) (shi' := (170715637568213 / 1152921504606846976)) hc5lo hc5hi hs5lo hs5hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^5 * yT2) = (2:ℝ)^6 * yT2 by ring] at hcd6 hsd6
  obtain ⟨hc6lo, hc6hi⟩ := hcd6
  obtain ⟨hs6lo, hs6hi⟩ := hsd6
  have hcd7 := cos_double_interval (y := ((2:ℝ)^6 * yT2)) (clo := (1152921491967725589 / 1152921504606846976)) (chi := (576460745983865525 / 576460752303423488)) (clo' := (1152921454050361705 / 1152921504606846976)) (chi' := (576460727025191775 / 576460752303423488)) hc6lo hc6hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd7 := sin_double_interval (y := ((2:ℝ)^6 * yT2)) (clo := (1152921491967725589 / 1152921504606846976)) (chi := (576460745983865525 / 576460752303423488)) (slo := (85357818784043 / 576460752303423488)) (shi := (170715637568213 / 1152921504606846976)) (slo' := (170715635696583 / 576460752303423488)) (shi' := (341431271393423 / 1152921504606846976)) hc6lo hc6hi hs6lo hs6hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^6 * yT2) = (2:ℝ)^7 * yT2 by ring] at hcd7 hsd7
  obtain ⟨hc7lo, hc7hi⟩ := hcd7
  obtain ⟨hs7lo, hs7hi⟩ := hsd7
  have hcd8 := cos_double_interval (y := ((2:ℝ)^7 * yT2)) (clo := (1152921454050361705 / 1152921504606846976)) (chi := (576460727025191775 / 576460752303423488)) (clo' := (1152921302380910325 / 1152921504606846976)) (chi' := (576460651190498853 / 576460752303423488)) hc7lo hc7hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd8 := sin_double_interval (y := ((2:ℝ)^7 * yT2)) (clo := (1152921454050361705 / 1152921504606846976)) (chi := (576460727025191775 / 576460752303423488)) (slo := (170715635696583 / 576460752303423488)) (shi := (341431271393423 / 1152921504606846976)) (slo' := (682862512842289 / 1152921504606846976)) (shi' := (682862512842817 / 1152921504606846976)) hc7lo hc7hi hs7lo hs7hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^7 * yT2) = (2:ℝ)^8 * yT2 by ring] at hcd8 hsd8
  obtain ⟨hc8lo, hc8hi⟩ := hcd8
  obtain ⟨hs8lo, hs8hi⟩ := hsd8
  have hcd9 := cos_double_interval (y := ((2:ℝ)^8 * yT2)) (clo := (1152921302380910325 / 1152921504606846976)) (chi := (576460651190498853 / 576460752303423488)) (clo' := (576460347851585657 / 576460752303423488)) (chi' := (1152920695703520839 / 1152921504606846976)) hc8lo hc8hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd9 := sin_double_interval (y := ((2:ℝ)^8 * yT2)) (clo := (1152921302380910325 / 1152921504606846976)) (chi := (576460651190498853 / 576460752303423488)) (slo := (682862512842289 / 1152921504606846976)) (shi := (682862512842817 / 1152921504606846976)) (slo' := (42678899566633 / 36028797018963968)) (shi' := (1365724786133417 / 1152921504606846976)) hc8lo hc8hi hs8lo hs8hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^8 * yT2) = (2:ℝ)^9 * yT2 by ring] at hcd9 hsd9
  obtain ⟨hc9lo, hc9hi⟩ := hcd9
  obtain ⟨hs9lo, hs9hi⟩ := hsd9
  have hcd10 := cos_double_interval (y := ((2:ℝ)^9 * yT2)) (clo := (576460347851585657 / 576460752303423488)) (chi := (1152920695703520839 / 1152921504606846976)) (clo' := (1152918268993279401 / 1152921504606846976)) (chi' := (1152918268994677501 / 1152921504606846976)) hc9lo hc9hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd10 := sin_double_interval (y := ((2:ℝ)^9 * yT2)) (clo := (576460347851585657 / 576460752303423488)) (chi := (1152920695703520839 / 1152921504606846976)) (slo := (42678899566633 / 36028797018963968)) (shi := (1365724786133417 / 1152921504606846976)) (slo' := (2731447655846447 / 1152921504606846976)) (shi' := (1365723827924799 / 576460752303423488)) hc9lo hc9hi hs9lo hs9hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^9 * yT2) = (2:ℝ)^10 * yT2 by ring] at hcd10 hsd10
  obtain ⟨hc10lo, hc10hi⟩ := hcd10
  obtain ⟨hs10lo, hs10hi⟩ := hsd10
  have hcd11 := cos_double_interval (y := ((2:ℝ)^10 * yT2)) (clo := (1152918268993279401 / 1152921504606846976)) (chi := (1152918268994677501 / 1152921504606846976)) (clo' := (576454281085368917 / 576460752303423488)) (chi' := (1152908562176330219 / 1152921504606846976)) hc10lo hc10hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd11 := sin_double_interval (y := ((2:ℝ)^10 * yT2)) (clo := (1152918268993279401 / 1152921504606846976)) (chi := (1152918268994677501 / 1152921504606846976)) (slo := (2731447655846447 / 1152921504606846976)) (shi := (1365723827924799 / 576460752303423488)) (slo' := (5462879980364509 / 1152921504606846976)) (shi' := (5462879980377437 / 1152921504606846976)) hc10lo hc10hi hs10lo hs10hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^10 * yT2) = (2:ℝ)^11 * yT2 by ring] at hcd11 hsd11
  obtain ⟨hc11lo, hc11hi⟩ := hcd11
  obtain ⟨hs11lo, hs11hi⟩ := hsd11
  have hcd12 := cos_double_interval (y := ((2:ℝ)^11 * yT2)) (clo := (576454281085368917 / 576460752303423488)) (chi := (1152908562176330219 / 1152921504606846976)) (clo' := (576434867576494065 / 576460752303423488)) (chi' := (288217433793839355 / 288230376151711744)) hc11lo hc11hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd12 := sin_double_interval (y := ((2:ℝ)^11 * yT2)) (clo := (576454281085368917 / 576460752303423488)) (chi := (1152908562176330219 / 1152921504606846976)) (slo := (5462879980364509 / 1152921504606846976)) (shi := (5462879980377437 / 1152921504606846976)) (slo' := (10925637310618259 / 1152921504606846976)) (shi' := (10925637310697113 / 1152921504606846976)) hc11lo hc11hi hs11lo hs11hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^11 * yT2) = (2:ℝ)^12 * yT2 by ring] at hcd12 hsd12
  obtain ⟨hc12lo, hc12hi⟩ := hcd12
  obtain ⟨hs12lo, hs12hi⟩ := hsd12
  have hcd13 := cos_double_interval (y := ((2:ℝ)^12 * yT2)) (clo := (576434867576494065 / 576460752303423488)) (chi := (288217433793839355 / 288230376151711744)) (clo' := (576357215720301479 / 576460752303423488)) (chi' := (1152714431530076101 / 1152921504606846976)) hc12lo hc12hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd13 := sin_double_interval (y := ((2:ℝ)^12 * yT2)) (clo := (576434867576494065 / 576460752303423488)) (chi := (288217433793839355 / 288230376151711744)) (slo := (10925637310618259 / 1152921504606846976)) (shi := (10925637310697113 / 1152921504606846976)) (slo' := (21850293436872499 / 1152921504606846976)) (shi' := (21850293437454165 / 1152921504606846976)) hc12lo hc12hi hs12lo hs12hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^12 * yT2) = (2:ℝ)^13 * yT2 by ring] at hcd13 hsd13
  obtain ⟨hc13lo, hc13hi⟩ := hcd13
  obtain ⟨hs13lo, hs13hi⟩ := hsd13
  have hcd14 := cos_double_interval (y := ((2:ℝ)^13 * yT2)) (clo := (576357215720301479 / 576460752303423488)) (chi := (1152714431530076101 / 1152921504606846976)) (clo' := (1152093286325592617 / 1152921504606846976)) (chi' := (576046643341710455 / 576460752303423488)) hc13lo hc13hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd14 := sin_double_interval (y := ((2:ℝ)^13 * yT2)) (clo := (576357215720301479 / 576460752303423488)) (chi := (1152714431530076101 / 1152921504606846976)) (slo := (21850293436872499 / 1152921504606846976)) (shi := (21850293437454165 / 1152921504606846976)) (slo' := (21846368963760275 / 576460752303423488)) (shi' := (10923184483018771 / 288230376151711744)) hc13lo hc13hi hs13lo hs13hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^13 * yT2) = (2:ℝ)^14 * yT2 by ring] at hcd14 hsd14
  obtain ⟨hc14lo, hc14hi⟩ := hcd14
  obtain ⟨hs14lo, hs14hi⟩ := hsd14
  have hcd15 := cos_double_interval (y := ((2:ℝ)^14 * yT2)) (clo := (1152093286325592617 / 1152921504606846976)) (chi := (576046643341710455 / 576460752303423488)) (clo' := (143701227675953595 / 144115188075855872)) (chi' := (8981326740921201 / 9007199254740992)) hc14lo hc14hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd15 := sin_double_interval (y := ((2:ℝ)^14 * yT2)) (clo := (1152093286325592617 / 1152921504606846976)) (chi := (576046643341710455 / 576460752303423488)) (slo := (21846368963760275 / 576460752303423488)) (shi := (10923184483018771 / 288230376151711744)) (slo' := (10915337650121637 / 144115188075855872)) (shi' := (2728834413662411 / 36028797018963968)) hc14lo hc14hi hs14lo hs14hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^14 * yT2) = (2:ℝ)^15 * yT2 by ring] at hcd15 hsd15
  obtain ⟨hc15lo, hc15hi⟩ := hcd15
  obtain ⟨hs15lo, hs15hi⟩ := hsd15
  have hcd16 := cos_double_interval (y := ((2:ℝ)^15 * yT2)) (clo := (143701227675953595 / 144115188075855872)) (chi := (8981326740921201 / 9007199254740992)) (clo' := (142461724618550503 / 144115188075855872)) (chi' := (569846901326555171 / 576460752303423488)) hc15lo hc15hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd16 := sin_double_interval (y := ((2:ℝ)^15 * yT2)) (clo := (143701227675953595 / 144115188075855872)) (chi := (8981326740921201 / 9007199254740992)) (slo := (10915337650121637 / 144115188075855872)) (shi := (2728834413662411 / 36028797018963968)) (slo' := (174143746181081045 / 1152921504606846976)) (shi' := (174143746469981681 / 1152921504606846976)) hc15lo hc15hi hs15lo hs15hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^15 * yT2) = (2:ℝ)^16 * yT2 by ring] at hcd16 hsd16
  obtain ⟨hc16lo, hc16hi⟩ := hcd16
  obtain ⟨hs16lo, hs16hi⟩ := hsd16
  have hcd17 := cos_double_interval (y := ((2:ℝ)^16 * yT2)) (clo := (142461724618550503 / 144115188075855872)) (chi := (569846901326555171 / 576460752303423488)) (clo' := (1100314202442616373 / 1152921504606846976)) (chi' := (550157112499818293 / 576460752303423488)) hc16lo hc16hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd17 := sin_double_interval (y := ((2:ℝ)^16 * yT2)) (clo := (142461724618550503 / 144115188075855872)) (chi := (569846901326555171 / 576460752303423488)) (slo := (174143746181081045 / 1152921504606846976)) (shi := (174143746469981681 / 1152921504606846976)) (slo' := (43036439711395403 / 144115188075855872)) (shi' := (172145759992838549 / 576460752303423488)) hc16lo hc16hi hs16lo hs16hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^16 * yT2) = (2:ℝ)^17 * yT2 by ring] at hcd17 hsd17
  obtain ⟨hc17lo, hc17hi⟩ := hcd17
  obtain ⟨hs17lo, hs17hi⟩ := hsd17
  have hcd18 := cos_double_interval (y := ((2:ℝ)^17 * yT2)) (clo := (1100314202442616373 / 1152921504606846976)) (chi := (550157112499818293 / 576460752303423488)) (clo' := (947293192160013741 / 1152921504606846976)) (chi' := (473646639135513877 / 576460752303423488)) hc17lo hc17hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd18 := sin_double_interval (y := ((2:ℝ)^17 * yT2)) (clo := (1100314202442616373 / 1152921504606846976)) (chi := (550157112499818293 / 576460752303423488)) (slo := (43036439711395403 / 144115188075855872)) (shi := (172145759992838549 / 576460752303423488)) (slo' := (328581646870480637 / 576460752303423488)) (shi' := (328581655796393579 / 576460752303423488)) hc17lo hc17hi hs17lo hs17hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^17 * yT2) = (2:ℝ)^18 * yT2 by ring] at hcd18 hsd18
  obtain ⟨hc18lo, hc18hi⟩ := hcd18
  obtain ⟨hs18lo, hs18hi⟩ := hsd18
  have hcd19 := cos_double_interval (y := ((2:ℝ)^18 * yT2)) (clo := (947293192160013741 / 1152921504606846976)) (chi := (473646639135513877 / 576460752303423488)) (clo' := (403757572549780893 / 1152921504606846976)) (chi' := (403757855560829699 / 1152921504606846976)) hc18lo hc18hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd19 := sin_double_interval (y := ((2:ℝ)^18 * yT2)) (clo := (947293192160013741 / 1152921504606846976)) (chi := (473646639135513877 / 576460752303423488)) (slo := (328581646870480637 / 576460752303423488)) (shi := (328581655796393579 / 576460752303423488)) (slo' := (269977752956628701 / 288230376151711744)) (shi' := (539955569664269043 / 576460752303423488)) hc18lo hc18hi hs18lo hs18hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^18 * yT2) = (2:ℝ)^19 * yT2 by ring] at hcd19 hsd19
  obtain ⟨hc19lo, hc19hi⟩ := hcd19
  obtain ⟨hs19lo, hs19hi⟩ := hsd19
  have hcd20 := cos_double_interval (y := ((2:ℝ)^19 * yT2)) (clo := (403757572549780893 / 1152921504606846976)) (chi := (403757855560829699 / 1152921504606846976)) (clo' := (-108765821978533743 / 144115188075855872)) (chi' := (-217531544845468247 / 288230376151711744)) hc19lo hc19hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd20 := sin_double_interval (y := ((2:ℝ)^19 * yT2)) (clo := (403757572549780893 / 1152921504606846976)) (chi := (403757855560829699 / 1152921504606846976)) (slo := (269977752956628701 / 288230376151711744)) (shi := (539955569664269043 / 576460752303423488)) (slo' := (189094507719125899 / 288230376151711744)) (shi' := (756378650357864899 / 1152921504606846976)) hc19lo hc19hi hs19lo hs19hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^19 * yT2) = (2:ℝ)^20 * yT2 by ring] at hcd20 hsd20
  obtain ⟨hc20lo, hc20hi⟩ := hcd20
  obtain ⟨hs20lo, hs20hi⟩ := hsd20
  have hcd21 := cos_double_interval (y := ((2:ℝ)^20 * yT2)) (clo := (-108765821978533743 / 144115188075855872)) (chi := (-217531544845468247 / 288230376151711744)) (clo' := (20058948025430061 / 144115188075855872)) (chi' := (80236390509271703 / 576460752303423488)) hc20lo hc20hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  have hsd21 := sin_double_interval (y := ((2:ℝ)^20 * yT2)) (clo := (-108765821978533743 / 144115188075855872)) (chi := (-217531544845468247 / 288230376151711744)) (slo := (189094507719125899 / 288230376151711744)) (shi := (756378650357864899 / 1152921504606846976)) (slo' := (-142712483554968599 / 144115188075855872)) (shi' := (-1141698413196633929 / 1152921504606846976)) hc20lo hc20hi hs20lo hs20hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^20 * yT2) = (2:ℝ)^21 * yT2 by ring] at hcd21 hsd21
  obtain ⟨hc21lo, hc21hi⟩ := hcd21
  obtain ⟨hs21lo, hs21hi⟩ := hsd21
  have hcd22 := cos_double_interval (y := ((2:ℝ)^21 * yT2)) (clo := (20058948025430061 / 144115188075855872)) (chi := (80236390509271703 / 576460752303423488)) (clo' := (-554125208006725529 / 576460752303423488)) (chi' := (-138531218710871479 / 144115188075855872)) hc21lo hc21hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd22 := sin_double_interval (y := ((2:ℝ)^21 * yT2)) (clo := (20058948025430061 / 144115188075855872)) (chi := (80236390509271703 / 576460752303423488)) (slo := (-142712483554968599 / 144115188075855872)) (shi := (-1141698413196633929 / 1152921504606846976)) (slo' := (-158910864482060217 / 576460752303423488)) (shi' := (-79454738382511901 / 288230376151711744)) hc21lo hc21hi hs21lo hs21hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^21 * yT2) = (2:ℝ)^22 * yT2 by ring] at hcd22 hsd22
  obtain ⟨hc22lo, hc22hi⟩ := hcd22
  obtain ⟨hs22lo, hs22hi⟩ := hsd22
  exact ⟨hc22lo, hc22hi, hs22lo, hs22hi⟩
/-- `2^22·y = c` (exact dyadic sample point). -/
private theorem scaleT2 : (2:ℝ)^22 * yT2 = (341431276384043 / 35184372088832) := by unfold yT2; norm_num
/-- **verified argument enclosure**: `|14·log 2 − c| ≤ 2^-27` (θ as a verified dyadic box,
    from Mathlib's `log` d9 bounds — the corpus expLo/expHi-style algebraic check). -/
private theorem thetaT2 : |14 * Real.log 2 - (341431276384043 / 35184372088832)| ≤ (1 / 134217728) := by
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  rw [abs_le]; constructor <;> nlinarith [h2lo, h2hi]
/-- **OPERATING-POINT CERTIFICATE (cos).**  Kernel-checked box for `cos(14·log 2)`,
    argument ≈ 9.7041, width ≤ 1e-4, argument entering as a verified dyadic enclosure. -/
theorem cos_14log2 :
    ((-554125208006725529 / 576460752303423488) - (1 / 134217728) : ℝ) ≤ Real.cos (14 * Real.log 2) ∧ Real.cos (14 * Real.log 2) ≤ (-138531218710871479 / 144115188075855872) + (1 / 134217728) := by
  obtain ⟨hclo, hchi, _, _⟩ := climbT2
  rw [scaleT2] at hclo hchi
  have hd : |14 * Real.log 2 - (341431276384043 / 35184372088832)| ≤ (1 / 134217728) := thetaT2
  have habs : |(14 * Real.log 2) - (341431276384043 / 35184372088832)| ≤ (1 / 134217728) := hd
  exact cos_encl_bracket (by norm_num) habs hclo hchi
/-- **OPERATING-POINT CERTIFICATE (sin).**  Kernel-checked box for `sin(14·log 2)`. -/
theorem sin_14log2 :
    ((-158910864482060217 / 576460752303423488) - (1 / 134217728) : ℝ) ≤ Real.sin (14 * Real.log 2) ∧ Real.sin (14 * Real.log 2) ≤ (-79454738382511901 / 288230376151711744) + (1 / 134217728) := by
  obtain ⟨_, _, hslo, hshi⟩ := climbT2
  rw [scaleT2] at hslo hshi
  have hd : |14 * Real.log 2 - (341431276384043 / 35184372088832)| ≤ (1 / 134217728) := thetaT2
  exact sin_encl_bracket (by norm_num) hd hslo hshi
end T2

/-! ### Operating point T200: θ = 14·log 200 ≈ 74.176443  (argument ≈ 74.23). -/
section T200
/-- reduced argument `y = c/2^26` with `c = 5219703150741705/2^46` (exact dyadic rational), `|y| ≤ 1`. -/
private noncomputable def yT200 : ℝ := (5219703150741705 / 4722366482869645213696)
private theorem hyT200 : |yT200| ≤ 1 := by unfold yT200; rw [abs_le]; constructor <;> norm_num
/-- base cos/sin brackets at `y` (order-4/5 Taylor, `|y| ≤ 1`). -/
private theorem baseT200 :
    ((1152921504606142701 / 1152921504606846976) : ℝ) ≤ Real.cos yT200 ∧ Real.cos yT200 ≤ (576460752303071351 / 576460752303423488) ∧
    ((39823174673 / 36028797018963968) : ℝ) ≤ Real.sin yT200 ∧ Real.sin yT200 ≤ (1274341589537 / 1152921504606846976) := by
  have hc := cos_base_interval (y := yT200) hyT200 (clo := (1152921504606142701 / 1152921504606846976)) (chi := (576460752303071351 / 576460752303423488)) (by unfold yT200; norm_num) (by unfold yT200; norm_num)
  have hs := sin_base_interval (y := yT200) hyT200 (slo := (39823174673 / 36028797018963968)) (shi := (1274341589537 / 1152921504606846976)) (by unfold yT200; norm_num) (by unfold yT200; norm_num)
  exact ⟨hc.1, hc.2, hs.1, hs.2⟩
/-- **π-free double-angle climb** (26 steps): cos/sin of `2^26·y = c`. -/
private theorem climbT200 :
    ((394219250499956115 / 1152921504606846976) : ℝ) ≤ Real.cos ((2:ℝ)^26 * yT200) ∧ Real.cos ((2:ℝ)^26 * yT200) ≤ (197147661501926961 / 576460752303423488) ∧
    ((-1083466681527763897 / 1152921504606846976) : ℝ) ≤ Real.sin ((2:ℝ)^26 * yT200) ∧ Real.sin ((2:ℝ)^26 * yT200) ≤ (-541682325062547215 / 576460752303423488) := by
  obtain ⟨hc0lo, hc0hi, hs0lo, hs0hi⟩ := baseT200
  have hcd1 := cos_double_interval (y := yT200) (clo := (1152921504606142701 / 1152921504606846976)) (chi := (576460752303071351 / 576460752303423488)) (clo' := (288230376151007469 / 288230376151711744)) (chi' := (1152921504604029881 / 1152921504606846976)) hc0lo hc0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd1 := sin_double_interval (y := yT200) (clo := (1152921504606142701 / 1152921504606846976)) (chi := (576460752303071351 / 576460752303423488)) (slo := (39823174673 / 36028797018963968)) (shi := (1274341589537 / 1152921504606846976)) (slo' := (1274341589535 / 576460752303423488)) (shi' := (2548683179073 / 1152921504606846976)) hc0lo hc0hi hs0lo hs0hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*yT200 = (2:ℝ)^1 * yT200 by ring] at hcd1 hsd1
  obtain ⟨hc1lo, hc1hi⟩ := hcd1
  obtain ⟨hs1lo, hs1hi⟩ := hsd1
  have hcd2 := cos_double_interval (y := ((2:ℝ)^1 * yT200)) (clo := (288230376151007469 / 288230376151711744)) (chi := (1152921504604029881 / 1152921504606846976)) (clo' := (72057594037223661 / 72057594037927936)) (chi' := (1152921504595578597 / 1152921504606846976)) hc1lo hc1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd2 := sin_double_interval (y := ((2:ℝ)^1 * yT200)) (clo := (288230376151007469 / 288230376151711744)) (chi := (1152921504604029881 / 1152921504606846976)) (slo := (1274341589535 / 576460752303423488)) (shi := (2548683179073 / 1152921504606846976)) (slo' := (5097366358127 / 1152921504606846976)) (shi' := (2548683179067 / 576460752303423488)) hc1lo hc1hi hs1lo hs1hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^1 * yT200) = (2:ℝ)^2 * yT200 by ring] at hcd2 hsd2
  obtain ⟨hc2lo, hc2hi⟩ := hcd2
  obtain ⟨hs2lo, hs2hi⟩ := hsd2
  have hcd3 := cos_double_interval (y := ((2:ℝ)^2 * yT200)) (clo := (72057594037223661 / 72057594037927936)) (chi := (1152921504595578597 / 1152921504606846976)) (clo' := (18014398508777709 / 18014398509481984)) (chi' := (1152921504561773461 / 1152921504606846976)) hc2lo hc2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd3 := sin_double_interval (y := ((2:ℝ)^2 * yT200)) (clo := (72057594037223661 / 72057594037927936)) (chi := (1152921504595578597 / 1152921504606846976)) (slo := (5097366358127 / 1152921504606846976)) (shi := (2548683179067 / 576460752303423488)) (slo' := (5097366358077 / 576460752303423488)) (shi' := (10194732716169 / 1152921504606846976)) hc2lo hc2hi hs2lo hs2hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^2 * yT200) = (2:ℝ)^3 * yT200 by ring] at hcd3 hsd3
  obtain ⟨hc3lo, hc3hi⟩ := hcd3
  obtain ⟨hs3lo, hs3hi⟩ := hsd3
  have hcd4 := cos_double_interval (y := ((2:ℝ)^3 * yT200)) (clo := (18014398508777709 / 18014398509481984)) (chi := (1152921504561773461 / 1152921504606846976)) (clo' := (4503599626666221 / 4503599627370496)) (chi' := (1152921504426552917 / 1152921504606846976)) hc3lo hc3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd4 := sin_double_interval (y := ((2:ℝ)^3 * yT200)) (clo := (18014398508777709 / 18014398509481984)) (chi := (1152921504561773461 / 1152921504606846976)) (slo := (5097366358077 / 576460752303423488)) (shi := (10194732716169 / 1152921504606846976)) (slo' := (10194732715755 / 576460752303423488)) (shi' := (20389465431541 / 1152921504606846976)) hc3lo hc3hi hs3lo hs3hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^3 * yT200) = (2:ℝ)^4 * yT200 by ring] at hcd4 hsd4
  obtain ⟨hc4lo, hc4hi⟩ := hcd4
  obtain ⟨hs4lo, hs4hi⟩ := hsd4
  have hcd5 := cos_double_interval (y := ((2:ℝ)^4 * yT200)) (clo := (4503599626666221 / 4503599627370496)) (chi := (1152921504426552917 / 1152921504606846976)) (clo' := (1125899906138349 / 1125899906842624)) (chi' := (1152921503885670741 / 1152921504606846976)) hc4lo hc4hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd5 := sin_double_interval (y := ((2:ℝ)^4 * yT200)) (clo := (4503599626666221 / 4503599627370496)) (chi := (1152921504426552917 / 1152921504606846976)) (slo := (10194732715755 / 576460752303423488)) (shi := (20389465431541 / 1152921504606846976)) (slo' := (20389465428321 / 576460752303423488)) (shi' := (40778930856705 / 1152921504606846976)) hc4lo hc4hi hs4lo hs4hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^4 * yT200) = (2:ℝ)^5 * yT200 by ring] at hcd5 hsd5
  obtain ⟨hc5lo, hc5hi⟩ := hcd5
  obtain ⟨hs5lo, hs5hi⟩ := hsd5
  have hcd6 := cos_double_interval (y := ((2:ℝ)^5 * yT200)) (clo := (1125899906138349 / 1125899906842624)) (chi := (1152921503885670741 / 1152921504606846976)) (clo' := (281474976006381 / 281474976710656)) (chi' := (1152921501722142037 / 1152921504606846976)) hc5lo hc5hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd6 := sin_double_interval (y := ((2:ℝ)^5 * yT200)) (clo := (1125899906138349 / 1125899906842624)) (chi := (1152921503885670741 / 1152921504606846976)) (slo := (20389465428321 / 576460752303423488)) (shi := (40778930856705 / 1152921504606846976)) (slo' := (81557861662267 / 1152921504606846976)) (shi' := (40778930831197 / 576460752303423488)) hc5lo hc5hi hs5lo hs5hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^5 * yT200) = (2:ℝ)^6 * yT200 by ring] at hcd6 hsd6
  obtain ⟨hc6lo, hc6hi⟩ := hcd6
  obtain ⟨hs6lo, hs6hi⟩ := hsd6
  have hcd7 := cos_double_interval (y := ((2:ℝ)^6 * yT200)) (clo := (281474976006381 / 281474976710656)) (chi := (1152921501722142037 / 1152921504606846976)) (clo' := (576460746534002695 / 576460752303423488)) (chi' := (1152921493068027235 / 1152921504606846976)) hc6lo hc6hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd7 := sin_double_interval (y := ((2:ℝ)^6 * yT200)) (clo := (281474976006381 / 281474976710656)) (chi := (1152921501722142037 / 1152921504606846976)) (slo := (81557861662267 / 1152921504606846976)) (shi := (40778930831197 / 576460752303423488)) (slo' := (40778930729101 / 288230376151711744)) (shi' := (163115722916659 / 1152921504606846976)) hc6lo hc6hi hs6lo hs6hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^6 * yT200) = (2:ℝ)^7 * yT200 by ring] at hcd7 hsd7
  obtain ⟨hc7lo, hc7hi⟩ := hcd7
  obtain ⟨hs7lo, hs7hi⟩ := hsd7
  have hcd8 := cos_double_interval (y := ((2:ℝ)^7 * yT200)) (clo := (576460746534002695 / 576460752303423488)) (chi := (1152921493068027235 / 1152921504606846976)) (clo' := (576460729225740431 / 576460752303423488)) (chi' := (1152921458451568243 / 1152921504606846976)) hc7lo hc7hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd8 := sin_double_interval (y := ((2:ℝ)^7 * yT200)) (clo := (576460746534002695 / 576460752303423488)) (chi := (1152921493068027235 / 1152921504606846976)) (slo := (40778930729101 / 288230376151711744)) (shi := (163115722916659 / 1152921504606846976)) (slo' := (326231442567769 / 1152921504606846976)) (shi' := (163115721284143 / 576460752303423488)) hc7lo hc7hi hs7lo hs7hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^7 * yT200) = (2:ℝ)^8 * yT200 by ring] at hcd8 hsd8
  obtain ⟨hc8lo, hc8hi⟩ := hcd8
  obtain ⟨hs8lo, hs8hi⟩ := hsd8
  have hcd9 := cos_double_interval (y := ((2:ℝ)^8 * yT200)) (clo := (576460729225740431 / 576460752303423488)) (chi := (1152921458451568243 / 1152921504606846976)) (clo' := (1152921319985386215 / 1152921504606846976)) (chi' := (288230329996433935 / 288230376151711744)) hc8lo hc8hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd9 := sin_double_interval (y := ((2:ℝ)^8 * yT200)) (clo := (576460729225740431 / 576460752303423488)) (chi := (1152921458451568243 / 1152921504606846976)) (slo := (326231442567769 / 1152921504606846976)) (shi := (163115721284143 / 576460752303423488)) (slo' := (652462859015231 / 1152921504606846976)) (shi' := (652462859016315 / 1152921504606846976)) hc8lo hc8hi hs8lo hs8hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^8 * yT200) = (2:ℝ)^9 * yT200 by ring] at hcd9 hsd9
  obtain ⟨hc9lo, hc9hi⟩ := hcd9
  obtain ⟨hs9lo, hs9hi⟩ := hsd9
  have hcd10 := cos_double_interval (y := ((2:ℝ)^9 * yT200)) (clo := (1152921319985386215 / 1152921504606846976)) (chi := (288230329996433935 / 288230376151711744)) (clo' := (288230191530265765 / 288230376151711744)) (chi' := (144115095765307645 / 144115188075855872)) hc9lo hc9hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd10 := sin_double_interval (y := ((2:ℝ)^9 * yT200)) (clo := (1152921319985386215 / 1152921504606846976)) (chi := (288230329996433935 / 288230376151711744)) (slo := (652462859015231 / 1152921504606846976)) (shi := (652462859016315 / 1152921504606846976)) (slo' := (326231377267005 / 288230376151711744)) (shi' := (1304925509070585 / 1152921504606846976)) hc9lo hc9hi hs9lo hs9hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^9 * yT200) = (2:ℝ)^10 * yT200 by ring] at hcd10 hsd10
  obtain ⟨hc10lo, hc10hi⟩ := hcd10
  obtain ⟨hs10lo, hs10hi⟩ := hsd10
  have hcd11 := cos_double_interval (y := ((2:ℝ)^10 * yT200)) (clo := (288230191530265765 / 288230376151711744)) (chi := (144115095765307645 / 144115188075855872)) (clo' := (576459275332328681 / 576460752303423488)) (chi' := (36028704708445305 / 36028797018963968)) hc10lo hc10hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd11 := sin_double_interval (y := ((2:ℝ)^10 * yT200)) (clo := (288230191530265765 / 288230376151711744)) (chi := (144115095765307645 / 144115188075855872)) (slo := (326231377267005 / 288230376151711744)) (shi := (1304925509070585 / 1152921504606846976)) (slo' := (2609849346436911 / 1152921504606846976)) (shi' := (1304924673222603 / 576460752303423488)) hc10lo hc10hi hs10lo hs10hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^10 * yT200) = (2:ℝ)^11 * yT200 by ring] at hcd11 hsd11
  obtain ⟨hc11lo, hc11hi⟩ := hcd11
  obtain ⟨hs11lo, hs11hi⟩ := hsd11
  have hcd12 := cos_double_interval (y := ((2:ℝ)^11 * yT200)) (clo := (576459275332328681 / 576460752303423488)) (chi := (36028704708445305 / 36028797018963968)) (clo' := (1152909688853225325 / 1152921504606846976)) (chi' := (1152909688875594861 / 1152921504606846976)) hc11lo hc11hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd12 := sin_double_interval (y := ((2:ℝ)^11 * yT200)) (clo := (576459275332328681 / 576460752303423488)) (chi := (36028704708445305 / 36028797018963968)) (slo := (2609849346436911 / 1152921504606846976)) (shi := (1304924673222603 / 576460752303423488)) (slo' := (5219685319293639 / 1152921504606846976)) (shi' := (5219685319335549 / 1152921504606846976)) hc11lo hc11hi hs11lo hs11hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^11 * yT200) = (2:ℝ)^12 * yT200 by ring] at hcd12 hsd12
  obtain ⟨hc12lo, hc12hi⟩ := hcd12
  obtain ⟨hs12lo, hs12hi⟩ := hsd12
  have hcd13 := cos_double_interval (y := ((2:ℝ)^12 * yT200)) (clo := (1152909688853225325 / 1152921504606846976)) (chi := (1152909688875594861 / 1152921504606846976)) (clo' := (288218560458637161 / 288230376151711744)) (chi' := (72054640120251617 / 72057594037927936)) hc12lo hc12hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd13 := sin_double_interval (y := ((2:ℝ)^12 * yT200)) (clo := (1152909688853225325 / 1152921504606846976)) (chi := (1152909688875594861 / 1152921504606846976)) (slo := (5219685319293639 / 1152921504606846976)) (shi := (5219685319335549 / 1152921504606846976)) (slo' := (10439263650356997 / 1152921504606846976)) (shi' := (5219631825321683 / 576460752303423488)) hc12lo hc12hi hs12lo hs12hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^12 * yT200) = (2:ℝ)^13 * yT200 by ring] at hcd13 hsd13
  obtain ⟨hc13lo, hc13hi⟩ := hcd13
  obtain ⟨hs13lo, hs13hi⟩ := hsd13
  have hcd14 := cos_double_interval (y := ((2:ℝ)^13 * yT200)) (clo := (288218560458637161 / 288230376151711744)) (chi := (72054640120251617 / 72057594037927936)) (clo' := (1152732457392626291 / 1152921504606846976)) (chi' := (288183114437630133 / 288230376151711744)) hc13lo hc13hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd14 := sin_double_interval (y := ((2:ℝ)^13 * yT200)) (clo := (288218560458637161 / 288230376151711744)) (chi := (72054640120251617 / 72057594037927936)) (slo := (10439263650356997 / 1152921504606846976)) (shi := (5219631825321683 / 576460752303423488)) (slo' := (10438835704014685 / 576460752303423488)) (shi' := (10438835705111225 / 576460752303423488)) hc13lo hc13hi hs13lo hs13hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^13 * yT200) = (2:ℝ)^14 * yT200 by ring] at hcd14 hsd14
  obtain ⟨hc14lo, hc14hi⟩ := hcd14
  obtain ⟨hs14lo, hs14hi⟩ := hsd14
  have hcd15 := cos_double_interval (y := ((2:ℝ)^14 * yT200)) (clo := (1152732457392626291 / 1152921504606846976)) (chi := (288183114437630133 / 288230376151711744)) (clo' := (1152165377746984955 / 1152921504606846976)) (chi' := (1152165379178327181 / 1152921504606846976)) hc14lo hc14hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd15 := sin_double_interval (y := ((2:ℝ)^14 * yT200)) (clo := (1152732457392626291 / 1152921504606846976)) (chi := (288183114437630133 / 288230376151711744)) (slo := (10438835704014685 / 576460752303423488)) (shi := (10438835705111225 / 576460752303423488)) (slo' := (10437124023903189 / 288230376151711744)) (shi' := (41748496112960049 / 1152921504606846976)) hc14lo hc14hi hs14lo hs14hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^14 * yT200) = (2:ℝ)^15 * yT200 by ring] at hcd15 hsd15
  obtain ⟨hc15lo, hc15hi⟩ := hcd15
  obtain ⟨hs15lo, hs15hi⟩ := hsd15
  have hcd16 := cos_double_interval (y := ((2:ℝ)^15 * yT200)) (clo := (1152165377746984955 / 1152921504606846976)) (chi := (1152165379178327181 / 1152921504606846976)) (clo' := (287474497239271087 / 288230376151711744)) (chi' := (287474498669674589 / 288230376151711744)) hc15lo hc15hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd16 := sin_double_interval (y := ((2:ℝ)^15 * yT200)) (clo := (1152165377746984955 / 1152921504606846976)) (chi := (1152165379178327181 / 1152921504606846976)) (slo := (10437124023903189 / 288230376151711744)) (shi := (41748496112960049 / 1152921504606846976)) (slo' := (41721115949496475 / 576460752303423488)) (shi' := (20860558009331397 / 288230376151711744)) hc15lo hc15hi hs15lo hs15hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^15 * yT200) = (2:ℝ)^16 * yT200 by ring] at hcd16 hsd16
  obtain ⟨hc16lo, hc16hi⟩ := hcd16
  obtain ⟨hs16lo, hs16hi⟩ := hsd16
  have hcd17 := cos_double_interval (y := ((2:ℝ)^16 * yT200)) (clo := (287474497239271087 / 288230376151711744)) (chi := (287474498669674589 / 288230376151711744)) (clo' := (285210825059313963 / 288230376151711744)) (chi' := (285210830765923157 / 288230376151711744)) hc16lo hc16hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd17 := sin_double_interval (y := ((2:ℝ)^16 * yT200)) (clo := (287474497239271087 / 288230376151711744)) (chi := (287474498669674589 / 288230376151711744)) (slo := (41721115949496475 / 576460752303423488)) (shi := (20860558009331397 / 288230376151711744)) (slo' := (166446812330839817 / 1152921504606846976)) (shi' := (41611703358744647 / 288230376151711744)) hc16lo hc16hi hs16lo hs16hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^16 * yT200) = (2:ℝ)^17 * yT200 by ring] at hcd17 hsd17
  obtain ⟨hc17lo, hc17hi⟩ := hcd17
  obtain ⟨hs17lo, hs17hi⟩ := hsd17
  have hcd18 := cos_double_interval (y := ((2:ℝ)^17 * yT200)) (clo := (285210825059313963 / 288230376151711744)) (chi := (285210830765923157 / 288230376151711744)) (clo' := (69053859614337473 / 72057594037927936)) (chi' := (1104861844178612835 / 1152921504606846976)) hc17lo hc17hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd18 := sin_double_interval (y := ((2:ℝ)^17 * yT200)) (clo := (285210825059313963 / 288230376151711744)) (chi := (285210830765923157 / 288230376151711744)) (slo := (166446812330839817 / 1152921504606846976)) (shi := (41611703358744647 / 288230376151711744)) (slo' := (329406173680904643 / 1152921504606846976)) (shi' := (20587886403558429 / 72057594037927936)) hc17lo hc17hi hs17lo hs17hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^17 * yT200) = (2:ℝ)^18 * yT200 by ring] at hcd18 hsd18
  obtain ⟨hc18lo, hc18hi⟩ := hcd18
  obtain ⟨hs18lo, hs18hi⟩ := hsd18
  have hcd19 := cos_double_interval (y := ((2:ℝ)^18 * yT200)) (clo := (69053859614337473 / 72057594037927936)) (chi := (1104861844178612835 / 1152921504606846976)) (clo' := (964689261082269507 / 1152921504606846976)) (chi' := (482344803707120313 / 576460752303423488)) hc18lo hc18hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd19 := sin_double_interval (y := ((2:ℝ)^18 * yT200)) (clo := (69053859614337473 / 72057594037927936)) (chi := (1104861844178612835 / 1152921504606846976)) (slo := (329406173680904643 / 1152921504606846976)) (shi := (20587886403558429 / 72057594037927936)) (slo' := (631349630171786261 / 1152921504606846976)) (shi' := (631349698620313615 / 1152921504606846976)) hc18lo hc18hi hs18lo hs18hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^18 * yT200) = (2:ℝ)^19 * yT200 by ring] at hcd19 hsd19
  obtain ⟨hc19lo, hc19hi⟩ := hcd19
  obtain ⟨hs19lo, hs19hi⟩ := hsd19
  have hcd20 := cos_double_interval (y := ((2:ℝ)^19 * yT200)) (clo := (964689261082269507 / 1152921504606846976)) (chi := (482344803707120313 / 576460752303423488)) (clo' := (230728086423983087 / 576460752303423488)) (chi' := (461457331999883963 / 1152921504606846976)) hc19lo hc19hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd20 := sin_double_interval (y := ((2:ℝ)^19 * yT200)) (clo := (964689261082269507 / 1152921504606846976)) (chi := (482344803707120313 / 576460752303423488)) (slo := (631349630171786261 / 1152921504606846976)) (shi := (631349698620313615 / 1152921504606846976)) (slo' := (1056544102579952081 / 1152921504606846976)) (shi' := (528272298217580155 / 576460752303423488)) hc19lo hc19hi hs19lo hs19hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^19 * yT200) = (2:ℝ)^20 * yT200 by ring] at hcd20 hsd20
  obtain ⟨hc20lo, hc20hi⟩ := hcd20
  obtain ⟨hs20lo, hs20hi⟩ := hsd20
  have hcd21 := cos_double_interval (y := ((2:ℝ)^20 * yT200)) (clo := (230728086423983087 / 576460752303423488)) (chi := (461457331999883963 / 1152921504606846976)) (clo' := (-783526366067720773 / 1152921504606846976)) (chi' := (-783524510265821297 / 1152921504606846976)) hc20lo hc20hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd21 := sin_double_interval (y := ((2:ℝ)^20 * yT200)) (clo := (230728086423983087 / 576460752303423488)) (chi := (461457331999883963 / 1152921504606846976)) (slo := (1056544102579952081 / 1152921504606846976)) (shi := (528272298217580155 / 576460752303423488)) (slo' := (211440586403100653 / 288230376151711744)) (shi' := (845764865451305285 / 1152921504606846976)) hc20lo hc20hi hs20lo hs20hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^20 * yT200) = (2:ℝ)^21 * yT200 by ring] at hcd21 hsd21
  obtain ⟨hc21lo, hc21hi⟩ := hcd21
  obtain ⟨hs21lo, hs21hi⟩ := hsd21
  have hcd22 := cos_double_interval (y := ((2:ℝ)^21 * yT200)) (clo := (-783526366067720773 / 1152921504606846976)) (chi := (-783524510265821297 / 1152921504606846976)) (clo' := (-687158388257601 / 9007199254740992)) (chi' := (-87951228885194753 / 1152921504606846976)) hc21lo hc21hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  have hsd22 := sin_double_interval (y := ((2:ℝ)^21 * yT200)) (clo := (-783526366067720773 / 1152921504606846976)) (chi := (-783524510265821297 / 1152921504606846976)) (slo := (211440586403100653 / 288230376151711744)) (shi := (845764865451305285 / 1152921504606846976)) (slo' := (-574782471249674103 / 576460752303423488)) (shi' := (-1149558794764967643 / 1152921504606846976)) hc21lo hc21hi hs21lo hs21hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^21 * yT200) = (2:ℝ)^22 * yT200 by ring] at hcd22 hsd22
  obtain ⟨hc22lo, hc22hi⟩ := hcd22
  obtain ⟨hs22lo, hs22hi⟩ := hsd22
  have hcd23 := cos_double_interval (y := ((2:ℝ)^22 * yT200)) (clo := (-687158388257601 / 9007199254740992)) (chi := (-87951228885194753 / 1152921504606846976)) (clo' := (-1139502692256644975 / 1152921504606846976)) (chi' := (-1139501152827920035 / 1152921504606846976)) hc22lo hc22hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  have hsd23 := sin_double_interval (y := ((2:ℝ)^22 * yT200)) (clo := (-687158388257601 / 9007199254740992)) (chi := (-87951228885194753 / 1152921504606846976)) (slo := (-574782471249674103 / 576460752303423488)) (shi := (-1149558794764967643 / 1152921504606846976)) (slo' := (21923675695042163 / 144115188075855872)) (shi' := (87700201887896277 / 576460752303423488)) hc22lo hc22hi hs22lo hs22hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^22 * yT200) = (2:ℝ)^23 * yT200 by ring] at hcd23 hsd23
  obtain ⟨hc23lo, hc23hi⟩ := hcd23
  obtain ⟨hs23lo, hs23hi⟩ := hsd23
  have hcd24 := cos_double_interval (y := ((2:ℝ)^23 * yT200)) (clo := (-1139502692256644975 / 1152921504606846976)) (chi := (-1139501152827920035 / 1152921504606846976)) (clo' := (1099552531323191923 / 1152921504606846976)) (chi' := (1099558617364556151 / 1152921504606846976)) hc23lo hc23hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inr (Or.inl (by norm_num)))
  have hsd24 := sin_double_interval (y := ((2:ℝ)^23 * yT200)) (clo := (-1139502692256644975 / 1152921504606846976)) (chi := (-1139501152827920035 / 1152921504606846976)) (slo := (21923675695042163 / 144115188075855872)) (shi := (87700201887896277 / 576460752303423488)) (slo' := (-43339731180045687 / 144115188075855872)) (shi' := (-21668477540667457 / 72057594037927936)) hc23lo hc23hi hs23lo hs23hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^23 * yT200) = (2:ℝ)^24 * yT200 by ring] at hcd24 hsd24
  obtain ⟨hc24lo, hc24hi⟩ := hcd24
  obtain ⟨hs24lo, hs24hi⟩ := hsd24
  have hcd25 := cos_double_interval (y := ((2:ℝ)^24 * yT200)) (clo := (1099552531323191923 / 1152921504606846976)) (chi := (1099558617364556151 / 1152921504606846976)) (clo' := (944386532945146563 / 1152921504606846976)) (chi' := (3689100587025147 / 4503599627370496)) hc24lo hc24hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd25 := sin_double_interval (y := ((2:ℝ)^24 * yT200)) (clo := (1099552531323191923 / 1152921504606846976)) (chi := (1099558617364556151 / 1152921504606846976)) (slo := (-43339731180045687 / 144115188075855872)) (shi := (-21668477540667457 / 72057594037927936)) (slo' := (-330670039220288947 / 576460752303423488)) (shi' := (-330647028226058663 / 576460752303423488)) hc24lo hc24hi hs24lo hs24hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^24 * yT200) = (2:ℝ)^25 * yT200 by ring] at hcd25 hsd25
  obtain ⟨hc25lo, hc25hi⟩ := hcd25
  obtain ⟨hs25lo, hs25hi⟩ := hsd25
  have hcd26 := cos_double_interval (y := ((2:ℝ)^25 * yT200)) (clo := (944386532945146563 / 1152921504606846976)) (chi := (3689100587025147 / 4503599627370496)) (clo' := (394219250499956115 / 1152921504606846976)) (chi' := (197147661501926961 / 576460752303423488)) hc25lo hc25hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have hsd26 := sin_double_interval (y := ((2:ℝ)^25 * yT200)) (clo := (944386532945146563 / 1152921504606846976)) (chi := (3689100587025147 / 4503599627370496)) (slo := (-330670039220288947 / 576460752303423488)) (shi := (-330647028226058663 / 576460752303423488)) (slo' := (-1083466681527763897 / 1152921504606846976)) (shi' := (-541682325062547215 / 576460752303423488)) hc25lo hc25hi hs25lo hs25hi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (2:ℝ)*((2:ℝ)^25 * yT200) = (2:ℝ)^26 * yT200 by ring] at hcd26 hsd26
  obtain ⟨hc26lo, hc26hi⟩ := hcd26
  obtain ⟨hs26lo, hs26hi⟩ := hsd26
  exact ⟨hc26lo, hc26hi, hs26lo, hs26hi⟩
/-- `2^26·y = c` (exact dyadic sample point). -/
private theorem scaleT200 : (2:ℝ)^26 * yT200 = (5219703150741705 / 70368744177664) := by unfold yT200; norm_num
/-- **verified argument enclosure**: `|14·log 200 − c| ≤ 2^-24` (θ as a verified dyadic box,
    from Mathlib's `log` d9 bounds — the corpus expLo/expHi-style algebraic check). -/
private theorem thetaT200 : |14 * Real.log 200 - (5219703150741705 / 70368744177664)| ≤ (1 / 16777216) := by
  have hdecomp : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (200:ℝ) = 2^3 * 5^2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]; push_cast; ring
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h5lo : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  have h5hi : Real.log 5 < (1.6094379126 : ℝ) := Real.log_five_lt_d9
  rw [hdecomp, abs_le]; constructor <;> nlinarith [h2lo, h2hi, h5lo, h5hi]
/-- **OPERATING-POINT CERTIFICATE (cos).**  Kernel-checked box for `cos(14·log 200)`,
    argument ≈ 74.1764, width ≤ 1e-4, argument entering as a verified dyadic enclosure. -/
theorem cos_14log200 :
    ((394219250499956115 / 1152921504606846976) - (1 / 16777216) : ℝ) ≤ Real.cos (14 * Real.log 200) ∧ Real.cos (14 * Real.log 200) ≤ (197147661501926961 / 576460752303423488) + (1 / 16777216) := by
  obtain ⟨hclo, hchi, _, _⟩ := climbT200
  rw [scaleT200] at hclo hchi
  have hd : |14 * Real.log 200 - (5219703150741705 / 70368744177664)| ≤ (1 / 16777216) := thetaT200
  have habs : |(14 * Real.log 200) - (5219703150741705 / 70368744177664)| ≤ (1 / 16777216) := hd
  exact cos_encl_bracket (by norm_num) habs hclo hchi
/-- **OPERATING-POINT CERTIFICATE (sin).**  Kernel-checked box for `sin(14·log 200)`. -/
theorem sin_14log200 :
    ((-1083466681527763897 / 1152921504606846976) - (1 / 16777216) : ℝ) ≤ Real.sin (14 * Real.log 200) ∧ Real.sin (14 * Real.log 200) ≤ (-541682325062547215 / 576460752303423488) + (1 / 16777216) := by
  obtain ⟨_, _, hslo, hshi⟩ := climbT200
  rw [scaleT200] at hslo hshi
  have hd : |14 * Real.log 200 - (5219703150741705 / 70368744177664)| ≤ (1 / 16777216) := thetaT200
  exact sin_encl_bracket (by norm_num) hd hslo hshi
end T200

end TrigReduceOperating
