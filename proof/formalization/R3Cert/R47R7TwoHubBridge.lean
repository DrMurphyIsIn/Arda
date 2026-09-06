/-
  R3Cert.R47R7TwoHubBridge -- M4 of the BG closure plan: wire the abstract two-hub Positivstellensatz
  certificates (`two_hub_gap_pos_c0..c5`, R47R7KelmansTwoHubCert) to the actual objective `Aobj`.

  The certs prove `0 < poly(x,y)` on `x,y >= 0` -- the integer-cleared numerator of `pi(T) - pi(S2)`
  after `pA = 1+x, pB = 1+y`, per receiver load `cA in {0..5}`.  This file supplies the missing bridge:

    * `twoHub_Aobj_eq` -- the EXACT `Aobj` of the stuck two-hub configuration
        `S2 = hub A (load cA, pA load-5 arms) -- hub B (load 0, pB load-5 arms)`,
      obtained by specializing the proven two-hub head identity `Aobj_head_before_raw` (R47HeadId).
    * `twoHub_le_tie` -- `Aobj(S2) <= Aobj(T)` for the same-size single-hub downgrade template
        `T = hubState (K+1-m) m 0`, m = 5-cA, K = pA+pB, dispatched per `cA` to the matching cert.

  The `pi <-> Aobj` normalization is C = 1 (Aobj = per(L)/prod(deg) on the realized tree, `pi_utree`;
  cross-checked exactly in proof/verification/two_hub_bridge_certcheck.py -- the Lean cert IS the sympy
  numerator, factor 1, over a per-cell all-positive-coefficient denominator).

  This is the LENGTH-2 slice of `SharpRateNF`/`Hdom`.  It does NOT close Hdom: the m>=3 multi-hub case
  and the length-1 single-hub 2-D envelope (M3) remain.  `conjecture1_proved = False`.  Self-contained
  leaf: imported by nothing; built as an explicit CI target.
-/
import Mathlib
import R3Cert.R47HeadId
import R3Cert.R47BackboneAmp
import R3Cert.R47TieBroadened
import R3Cert.R47R7KelmansTwoHubCert

namespace R3Cert
namespace Step3

open RTree

/-- **Exact `Aobj` of the stuck two-hub configuration** `S2(pA,pB,cA)`: hub A (load `cA`, `pA` load-5
    arms) adjacent to a de-loaded hub B (`pB` load-5 arms).  Specializes `Aobj_head_before_raw` with
    `armsA = replicate pA 5`, `armsB = replicate pB 5`, `cb = 0`, `rest = []`.  The common arm block is
    `(621/64)^pA·(621/64)^pB = V^K`; the bracket is the `pi_two_hub_closed` form. -/
theorem twoHub_Aobj_eq (pA pB cA : ℕ) :
    Aobj (backboneU [(List.replicate pA 5, cA), (List.replicate pB 5, 0)])
      = (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        * (Fw ((pA + 1 : ℕ) : ℝ) cA
            * ((1 + zw ((pA + 1 : ℕ) : ℝ) cA * ((pA : ℝ) * (3 / 23)))
                * (1 + zw ((pB + 1 : ℕ) : ℝ) 0 * ((pB : ℝ) * (3 / 23)))
              + zw ((pA + 1 : ℕ) : ℝ) cA * zw ((pB + 1 : ℕ) : ℝ) 0)) := by
  have h := Aobj_head_before_raw (List.replicate pA 5) cA (List.replicate pB 5) 0 []
  simp only [List.length_replicate, tailU, List.length_nil,
    qSum, List.map_nil, List.sum_nil, add_zero, Fw_zero, mul_one] at h
  rw [h, Kblock, armProd_replicate, armProd_replicate, Ztot_armU_five,
    sigmaArms_replicate, sigmaArms_replicate, zw_one_five, tailU, List.map_nil, List.prod_nil,
    mul_one]

/-- Reduced two-hub inequality, `cA = 0` (the `V^K`-divided form).  `(513/80)^5·T − (621/64)^4·S`
    equals `531441 · cert_c0(pA−1,pB−1)` over a positive denominator, so it is nonnegative. -/
theorem twoHub_reduced_c0 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (621 / 64 : ℝ) ^ 4 * ((1 + 3 / (3 * (pA + 1)) * (pA * (3 / 23)))
          * (1 + 3 / (3 * (pB + 1)) * (pB * (3 / 23))) + 3 / (3 * (pA + 1)) * (3 / (3 * (pB + 1))))
      ≤ (513 / 80) ^ 5 * (1 + ((pA + pB - 4) * (3 / ((pA + pB + 1) * 23))
          + 5 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c0 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (513 / 80 : ℝ) ^ 5 * (1 + ((pA + pB - 4) * (3 / ((pA + pB + 1) * 23))
          + 5 * (3 / ((pA + pB + 1) * 19))))
      - (621 / 64) ^ 4 * ((1 + 3 / (3 * (pA + 1)) * (pA * (3 / 23)))
          * (1 + 3 / (3 * (pB + 1)) * (pB * (3 / 23))) + 3 / (3 * (pA + 1)) * (3 / (3 * (pB + 1))))
      = 531441 * (2108756468 * (pA - 1) * (pB - 1) ^ 2 + 2108756468 * (pA - 1) ^ 2 * (pB - 1)
          + 7183219186 * (pB - 1) ^ 2 + 24070628096 * (pA - 1) * (pB - 1) + 7183219186 * (pA - 1) ^ 2
          + 28147580320 * (pB - 1) + 28147580320 * (pA - 1) + 13037927646)
        / (1205862400000 * (pA + 1) * (pB + 1) * (pA + pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]

theorem twoHub_reduced_c1 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (621 / 64 : ℝ) ^ 3 * (((3 / 2 : ℝ) ^ 1 + 1 / (2 * ((pA + 1) + 1)) * (3 / 2) ^ 0) * ((1 + (3 / (3 * (pA + 1) + 4 * 1)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 1)) * (3 / (3 * (pB + 1) + 4 * 0))))
      ≤ (513 / 80 : ℝ) ^ 4 * (1 + (((pA + pB - 4) + 1) * (3 / ((pA + pB + 1) * 23)) + 4 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c1 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (513 / 80 : ℝ) ^ 4 * (1 + (((pA + pB - 4) + 1) * (3 / ((pA + pB + 1) * 23)) + 4 * (3 / ((pA + pB + 1) * 19)))) - ((621 / 64 : ℝ) ^ 3 * (((3 / 2 : ℝ) ^ 1 + 1 / (2 * ((pA + 1) + 1)) * (3 / 2) ^ 0) * ((1 + (3 / (3 * (pA + 1) + 4 * 1)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 1)) * (3 / (3 * (pB + 1) + 4 * 0)))))
      = 19683 * (61375236*(pA - 1)*(pB - 1)^2 + 61375236*(pA - 1)^2*(pB - 1) + 141144458*(pB - 1)^2 + 596501000*(pA - 1)*(pB - 1) + 200116722*(pA - 1)^2 + 631420876*(pB - 1) + 737223556*(pA - 1) + 410620170) / (7536640000*(pA + 2)*(pB + 1)*(pA + pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]

theorem twoHub_reduced_c2 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (621 / 64 : ℝ) ^ 2 * (((3 / 2 : ℝ) ^ 2 + 2 / (2 * ((pA + 1) + 2)) * (3 / 2) ^ 1) * ((1 + (3 / (3 * (pA + 1) + 4 * 2)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 2)) * (3 / (3 * (pB + 1) + 4 * 0))))
      ≤ (513 / 80 : ℝ) ^ 3 * (1 + (((pA + pB - 4) + 2) * (3 / ((pA + pB + 1) * 23)) + 3 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c2 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (513 / 80 : ℝ) ^ 3 * (1 + (((pA + pB - 4) + 2) * (3 / ((pA + pB + 1) * 23)) + 3 * (3 / ((pA + pB + 1) * 19)))) - ((621 / 64 : ℝ) ^ 2 * (((3 / 2 : ℝ) ^ 2 + 2 / (2 * ((pA + 1) + 2)) * (3 / 2) ^ 1) * ((1 + (3 / (3 * (pA + 1) + 4 * 2)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 2)) * (3 / (3 * (pB + 1) + 4 * 0)))))
      = 729 * (1768572*(pA - 1)*(pB - 1)^2 + 1768572*(pA - 1)^2*(pB - 1) + 2813538*(pB - 1)^2 + 15078216*(pA - 1)*(pB - 1) + 5555394*(pA - 1)^2 + 14558712*(pB - 1) + 19977144*(pA - 1) + 12740022) / (47104000*(pA + 3)*(pB + 1)*(pA + pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]

theorem twoHub_reduced_c3 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (621 / 64 : ℝ) ^ 1 * (((3 / 2 : ℝ) ^ 3 + 3 / (2 * ((pA + 1) + 3)) * (3 / 2) ^ 2) * ((1 + (3 / (3 * (pA + 1) + 4 * 3)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 3)) * (3 / (3 * (pB + 1) + 4 * 0))))
      ≤ (513 / 80 : ℝ) ^ 2 * (1 + (((pA + pB - 4) + 3) * (3 / ((pA + pB + 1) * 23)) + 2 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c3 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (513 / 80 : ℝ) ^ 2 * (1 + (((pA + pB - 4) + 3) * (3 / ((pA + pB + 1) * 23)) + 2 * (3 / ((pA + pB + 1) * 19)))) - ((621 / 64 : ℝ) ^ 1 * (((3 / 2 : ℝ) ^ 3 + 3 / (2 * ((pA + 1) + 3)) * (3 / 2) ^ 2) * ((1 + (3 / (3 * (pA + 1) + 4 * 3)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 3)) * (3 / (3 * (pB + 1) + 4 * 0)))))
      = 27 * (50544*(pA - 1)*(pB - 1)^2 + 50544*(pA - 1)^2*(pB - 1) + 59670*(pB - 1)^2 + 389664*(pA - 1)*(pB - 1) + 153738*(pA - 1)^2 + 349920*(pB - 1) + 558252*(pA - 1) + 389610) / (294400*(pA + 4)*(pB + 1)*(pA + pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]

theorem twoHub_reduced_c4 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (((3 / 2 : ℝ) ^ 4 + 4 / (2 * ((pA + 1) + 4)) * (3 / 2) ^ 3) * ((1 + (3 / (3 * (pA + 1) + 4 * 4)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 4)) * (3 / (3 * (pB + 1) + 4 * 0))))
      ≤ (513 / 80 : ℝ) ^ 1 * (1 + (((pA + pB - 4) + 4) * (3 / ((pA + pB + 1) * 23)) + 1 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c4 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (513 / 80 : ℝ) ^ 1 * (1 + (((pA + pB - 4) + 4) * (3 / ((pA + pB + 1) * 23)) + 1 * (3 / ((pA + pB + 1) * 19)))) - ((((3 / 2 : ℝ) ^ 4 + 4 / (2 * ((pA + 1) + 4)) * (3 / 2) ^ 3) * ((1 + (3 / (3 * (pA + 1) + 4 * 4)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 4)) * (3 / (3 * (pB + 1) + 4 * 0)))))
      = 1 * (32994*(pA - 1)*(pB - 1)^2 + 32994*(pA - 1)^2*(pB - 1) + 32994*(pB - 1)^2 + 237006*(pA - 1)*(pB - 1) + 97578*(pA - 1)^2 + 204012*(pB - 1) + 367956*(pA - 1) + 270378) / (42320*(pA + 5)*(pB + 1)*(pA + pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]


theorem twoHub_reduced_c5 (pA pB : ℝ) (hu : 1 ≤ pA) (hv : 1 ≤ pB)
    (hx : 0 ≤ pA - 1) (hy : 0 ≤ pB - 1) :
    (((3 / 2 : ℝ) ^ 5 + 5 / (2 * ((pA + 1) + 5)) * (3 / 2) ^ 4) * ((1 + (3 / (3 * (pA + 1) + 4 * 5)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 5)) * (3 / (3 * (pB + 1) + 4 * 0))))
      ≤ (621 / 64 : ℝ) ^ 1 * (1 + ((pA + pB + 1) * (3 / ((pA + pB + 1) * 23)) + 0 * (3 / ((pA + pB + 1) * 19)))) := by
  have hc := two_hub_gap_pos_c5 (pA - 1) (pB - 1) hx hy
  have hpA1 : pA + 1 ≠ 0 := by positivity
  have hpB1 : pB + 1 ≠ 0 := by positivity
  have hsum : pA + pB + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  have hkey : (621 / 64 : ℝ) ^ 1 * (1 + ((pA + pB + 1) * (3 / ((pA + pB + 1) * 23)) + 0 * (3 / ((pA + pB + 1) * 19)))) - ((((3 / 2 : ℝ) ^ 5 + 5 / (2 * ((pA + 1) + 5)) * (3 / 2) ^ 4) * ((1 + (3 / (3 * (pA + 1) + 4 * 5)) * (pA * (3 / 23))) * (1 + (3 / (3 * (pB + 1) + 4 * 0)) * (pB * (3 / 23))) + (3 / (3 * (pA + 1) + 4 * 5)) * (3 / (3 * (pB + 1) + 4 * 0)))))
      = 1 * (21411*(pA - 1)*(pB - 1) + 21411*(pB - 1) + 61776*(pA - 1) + 61776) / (16928*(pA + 6)*(pB + 1)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg _ (by positivity)
  nlinarith [hc]


/-- **Two-hub vertex-budget domination, wired to `Aobj`.**  The stuck two-hub config `S2(pA,pB,cA)` is
    dominated by the same-size single-hub downgrade template `T = hubState (K+1-m) m 0`, `m = 5-cA`,
    `K = pA+pB`.  Per `cA` this is exactly the matching Positivstellensatz cert `two_hub_gap_pos_c<cA>`
    at `x = pA-1, y = pB-1`, over the common positive arm block `(621/64)^K`.  `hreal` excludes the
    finite small corner where the template is not a real tree. -/
theorem twoHub_le_tie (pA pB cA : ℕ) (hpA : 1 ≤ pA) (hpB : 1 ≤ pB) (hcA : cA ≤ 5)
    (hreal : 5 - cA ≤ pA + pB + 1) :
    Aobj (backboneU [(List.replicate pA 5, cA), (List.replicate pB 5, 0)])
      ≤ Aobj (backboneU (hubState (pA + pB + 1 - (5 - cA)) (5 - cA) 0)) := by
  have hu : (1 : ℝ) ≤ (pA : ℝ) := by exact_mod_cast hpA
  have hv : (1 : ℝ) ≤ (pB : ℝ) := by exact_mod_cast hpB
  have hx : (0 : ℝ) ≤ (pA : ℝ) - 1 := by linarith
  have hy : (0 : ℝ) ≤ (pB : ℝ) - 1 := by linarith
  rw [twoHub_Aobj_eq]
  interval_cases cA
  · -- cA = 0, m = 5
    have hK : 0 < (pA + pB + 1 - 5) + 5 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    set q := pA + pB + 1 - 5 with hqdef
    have hqR : (q : ℝ) = (pA : ℝ) + (pB : ℝ) - 4 := by
      have hn : q + 5 = pA + pB + 1 := by omega
      have := congrArg (Nat.cast : ℕ → ℝ) hn; push_cast at this; linarith
    have hbridge : (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        = (621 / 64 : ℝ) ^ q * (621 / 64) ^ 4 := by
      rw [← pow_add, ← pow_add]; congr 1 <;> omega
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ q := by positivity
    rw [hbridge, show ((q + 5 + 0 : ℕ) : ℝ) = (q : ℝ) + 5 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ q) ((621 / 64 : ℝ) ^ 4),
      mul_assoc ((621 / 64 : ℝ) ^ q * (513 / 80 : ℝ) ^ 5) ((3 / 2 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q) ((513 / 80 : ℝ) ^ 5)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw_zero, zw, one_mul, pow_zero, Nat.cast_zero, mul_zero, add_zero]
    push_cast
    rw [hqR]
    convert twoHub_reduced_c0 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring
  · -- cA = 1, m = 4
    have hK : 0 < (pA + pB + 1 - 4) + 4 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    set q := pA + pB + 1 - 4 with hqdef
    have hqR : (q : ℝ) = (pA : ℝ) + (pB : ℝ) - 3 := by
      have hn : q + 4 = pA + pB + 1 := by omega
      have := congrArg (Nat.cast : ℕ → ℝ) hn; push_cast at this; linarith
    have hbridge : (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        = (621 / 64 : ℝ) ^ q * (621 / 64) ^ 3 := by
      rw [← pow_add, ← pow_add]; congr 1 <;> omega
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ q := by positivity
    rw [hbridge, show ((q + 4 + 0 : ℕ) : ℝ) = (q : ℝ) + 4 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ q) ((621 / 64 : ℝ) ^ 3),
      mul_assoc ((621 / 64 : ℝ) ^ q * (513 / 80 : ℝ) ^ 4) ((3 / 2 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q) ((513 / 80 : ℝ) ^ 4)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw, zw, pow_zero, one_mul, mul_one, Nat.cast_zero, mul_zero, add_zero]
    push_cast
    rw [hqR]
    convert twoHub_reduced_c1 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring
  · -- cA = 2, m = 3
    have hK : 0 < (pA + pB + 1 - 3) + 3 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    set q := pA + pB + 1 - 3 with hqdef
    have hqR : (q : ℝ) = (pA : ℝ) + (pB : ℝ) - 2 := by
      have hn : q + 3 = pA + pB + 1 := by omega
      have := congrArg (Nat.cast : ℕ → ℝ) hn; push_cast at this; linarith
    have hbridge : (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        = (621 / 64 : ℝ) ^ q * (621 / 64) ^ 2 := by
      rw [← pow_add, ← pow_add]; congr 1 <;> omega
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ q := by positivity
    rw [hbridge, show ((q + 3 + 0 : ℕ) : ℝ) = (q : ℝ) + 3 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ q) ((621 / 64 : ℝ) ^ 2),
      mul_assoc ((621 / 64 : ℝ) ^ q * (513 / 80 : ℝ) ^ 3) ((3 / 2 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q) ((513 / 80 : ℝ) ^ 3)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw, zw, pow_zero, one_mul, mul_one, Nat.cast_zero, mul_zero, add_zero]
    push_cast
    rw [hqR]
    convert twoHub_reduced_c2 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring
  · -- cA = 3, m = 2
    have hK : 0 < (pA + pB + 1 - 2) + 2 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    set q := pA + pB + 1 - 2 with hqdef
    have hqR : (q : ℝ) = (pA : ℝ) + (pB : ℝ) - 1 := by
      have hn : q + 2 = pA + pB + 1 := by omega
      have := congrArg (Nat.cast : ℕ → ℝ) hn; push_cast at this; linarith
    have hbridge : (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        = (621 / 64 : ℝ) ^ q * (621 / 64) ^ 1 := by
      rw [← pow_add, ← pow_add]; congr 1 <;> omega
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ q := by positivity
    rw [hbridge, show ((q + 2 + 0 : ℕ) : ℝ) = (q : ℝ) + 2 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ q) ((621 / 64 : ℝ) ^ 1),
      mul_assoc ((621 / 64 : ℝ) ^ q * (513 / 80 : ℝ) ^ 2) ((3 / 2 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q) ((513 / 80 : ℝ) ^ 2)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw, zw, pow_zero, one_mul, mul_one, Nat.cast_zero, mul_zero, add_zero]
    push_cast
    rw [hqR]
    convert twoHub_reduced_c3 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring
  · -- cA = 4, m = 1
    have hK : 0 < (pA + pB + 1 - 1) + 1 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    set q := pA + pB + 1 - 1 with hqdef
    have hqR : (q : ℝ) = (pA : ℝ) + (pB : ℝ) - 0 := by
      have hn : q + 1 = pA + pB + 1 := by omega
      have := congrArg (Nat.cast : ℕ → ℝ) hn; push_cast at this; linarith
    have hbridge : (621 / 64 : ℝ) ^ pA * (621 / 64) ^ pB
        = (621 / 64 : ℝ) ^ q * (621 / 64) ^ 0 := by
      rw [← pow_add, ← pow_add]; congr 1 <;> omega
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ q := by positivity
    rw [hbridge, show ((q + 1 + 0 : ℕ) : ℝ) = (q : ℝ) + 1 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ q) ((621 / 64 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q * (513 / 80 : ℝ) ^ 1) ((3 / 2 : ℝ) ^ 0),
      mul_assoc ((621 / 64 : ℝ) ^ q) ((513 / 80 : ℝ) ^ 1)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw, zw, pow_zero, one_mul, mul_one, Nat.cast_zero, mul_zero, add_zero]
    push_cast
    rw [hqR]
    convert twoHub_reduced_c4 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring
  · -- cA = 5, m = 0 (template gains an arm; common factor (621/64)^(pA+pB))
    have hK : 0 < (pA + pB + 1 - 0) + 0 + 0 := by omega
    rw [hub_Aobj_eq _ _ _ hK]
    simp only [pow_zero, one_mul, mul_one, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [show pA + pB + 1 - 0 = pA + pB + 1 by omega, ← pow_add]
    have hbridge : (621 / 64 : ℝ) ^ (pA + pB + 1) = (621 / 64 : ℝ) ^ (pA + pB) * (621 / 64) := by
      rw [pow_succ]
    have hQ : (0 : ℝ) < (621 / 64 : ℝ) ^ (pA + pB) := by positivity
    rw [hbridge, show (((pA + pB + 1 : ℕ)) : ℝ) = (pA : ℝ) + (pB : ℝ) + 1 by push_cast; ring,
      mul_assoc ((621 / 64 : ℝ) ^ (pA + pB)) (621 / 64)]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    simp only [Fw, zw]
    push_cast
    convert twoHub_reduced_c5 (pA : ℝ) (pB : ℝ) hu hv hx hy using 2 <;> first | rfl | ring

end Step3
end R3Cert
