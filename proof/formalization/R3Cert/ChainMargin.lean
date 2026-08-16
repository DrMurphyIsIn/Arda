/-
  QUANTITATIVE FAR-REGIME MARGIN: the pure-depth `c=0` chain has `logPhi <= 0`, UNCONDITIONALLY.

  `general_children_crux.tail_decomposition`: `Psi <= 0` decomposes into a region-free NEGATIVE far regime
  plus the marginal near-tie core.  The DEPTH direction is the `c=0` chain (caterpillar); numerically its
  `logPhi = -0.01836 * n -> -inf` linearly.  This file makes that rigorous and UNCONDITIONAL.

  chainB : the `c=0` path, `chainB 0 = node 0 []`, `chainB (n+1) = node 0 [chainB n]`.

  The decomposition (all no-sorry):
  * `eroot_c0_one b : eroot 0 [b] = -Lval + log(1 + cav b / 2)`  (a `c=0` single-child node's increment).
  * `seventeen_14_lt_Lval : log(17/14) < Lval`  (i.e. `17/14 < rhoB`, from `(17/14)^11 < 621/64`).
  * `chain_incr_nonpos b (cav b <= 3/7) : eroot 0 [b] <= 0`  -- the per-node DEPTH MARGIN: once the child
    cavity is <= 3/7 (i.e. below the leaf), each extra depth level has a strictly negative increment.
  * `cav_chainB_bound n : 1/3 <= cav (chainB (n+1)) <= 3/7`  (cavity invariant, from `m -> 1/(2+m)`).
  * `logPhi_chainB n : logPhi (chainB n) <= 0`  -- base `n=1` is `-2Lval + log(3/2) <= 0` via the PROVEN
    `rhoB_sq_ge` (`3/2 <= rhoB^2`); the step `n>=1` adds a `<= 0` increment (`chain_incr_nonpos`).

  So the pure-depth tail is CLOSED, unconditionally, connecting to two proven `rhoB` cruxes
  (`rhoB_sq_ge` + `17/14 < rhoB`).  HONEST SCOPE: this is ONE far-regime direction (pure `c=0` depth); the
  branching direction and the marginal near-tie core are not closed here.  conjecture1_proved=False.
-/
import Mathlib
import R3Cert.NearStar

namespace R3Cert

open Real

/-- `17/14 < rhoB` (from `(17/14)^11 < 621/64 = rhoB^11`). -/
theorem seventeen_14_lt_rhoB : (17 / 14 : ℝ) < rhoB := by
  have h : ((17 : ℝ) / 14) ^ 11 < rhoB ^ 11 := by rw [rhoB_pow11]; norm_num
  exact lt_of_pow_lt_pow_left₀ 11 rhoB_pos.le h

/-- `log(17/14) < Lval` -- the strict per-node depth margin. -/
theorem seventeen_14_lt_Lval : Real.log (17 / 14) < Lval := by
  rw [← logRhoB]; exact Real.log_lt_log (by norm_num) seventeen_14_lt_rhoB

/-- A `c=0` single-child node's root increment: `eroot 0 [b] = -Lval + log(1 + cav b / 2)`. -/
theorem eroot_c0_one (b : Branch) : eroot 0 [b] = -Lval + Real.log (1 + cav b / 2) := by
  have hac : ac 0 1 = rhoB⁻¹ := by simp [ac]
  have hzc : zc 0 1 = 1 / 2 := by rw [zc]; norm_num
  have hlen : ([b] : List Branch).length = 1 := rfl
  have hcs : cavSum [b] = cav b := by simp [cavSum]
  unfold eroot
  rw [hlen, hcs, hac, hzc, Real.log_inv, logRhoB,
    show (1 : ℝ) + 1 / 2 * cav b = 1 + cav b / 2 from by ring]

/-- **Per-node depth margin.**  Once the child cavity has dropped to `<= 3/7` (below the leaf's `1`), each
    extra `c=0` depth level contributes a `<= 0` increment -- because `1 + (3/7)/2 = 17/14 < rhoB`. -/
theorem chain_incr_nonpos (b : Branch) (h : cav b ≤ 3 / 7) : eroot 0 [b] ≤ 0 := by
  rw [eroot_c0_one]
  have hpos : 0 < cav b := cav_pos b
  have h2 : Real.log (1 + cav b / 2) ≤ Real.log (17 / 14) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith [seventeen_14_lt_Lval]

/-- The `c=0` chain (caterpillar): `chainB 0 = node 0 []`, `chainB (n+1) = node 0 [chainB n]`. -/
def chainB : ℕ → Branch
  | 0 => Branch.node 0 []
  | (n + 1) => Branch.node 0 [chainB n]

theorem cav_chainB_succ (n : ℕ) : cav (chainB (n + 1)) = 3 / (6 + 3 * cav (chainB n)) := by
  have hcs : cavSum [chainB n] = cav (chainB n) := by simp [cavSum]
  have hlen : ([chainB n] : List Branch).length = 1 := rfl
  show cav (Branch.node 0 [chainB n]) = 3 / (6 + 3 * cav (chainB n))
  rw [cav_eq, hlen, hcs]; push_cast; ring

/-- Cavity invariant: after the leaf, all chain cavities lie in `[1/3, 3/7]`. -/
theorem cav_chainB_bound (n : ℕ) : 1 / 3 ≤ cav (chainB (n + 1)) ∧ cav (chainB (n + 1)) ≤ 3 / 7 := by
  induction n with
  | zero =>
    rw [cav_chainB_succ, show cav (chainB 0) = 1 from cav_leaf]
    norm_num
  | succ m ih =>
    rw [cav_chainB_succ]
    obtain ⟨hlo, hhi⟩ := ih
    have hpos : 0 < cav (chainB (m + 1)) := cav_pos _
    have hden : (0 : ℝ) < 6 + 3 * cav (chainB (m + 1)) := by linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hden]; linarith
    · rw [div_le_iff₀ hden]; linarith

/-- **The pure-depth chain is `<= 0`, unconditionally.**  Base `n=1` (`-2Lval+log(3/2) <= 0`) via the proven
    `rhoB_sq_ge`; the depth step adds a `<= 0` increment via `chain_incr_nonpos`. -/
theorem logPhi_chainB : ∀ n, logPhi (chainB n) ≤ 0
  | 0 => by
    show logPhi (Branch.node 0 []) ≤ 0
    rw [logPhi_leaf]
    have hL : 0 < Lval := by
      unfold Lval
      have := Real.log_pos (by norm_num : (1 : ℝ) < 621 / 64); linarith
    linarith
  | 1 => by
    show logPhi (Branch.node 0 [chainB 0]) ≤ 0
    have hstep : logPhi (Branch.node 0 [chainB 0]) = logPhi (chainB 0) + eroot 0 [chainB 0] := by
      simp only [logPhi, logPhiSum]; ring
    have h0 : logPhi (chainB 0) = -Lval := by
      show logPhi (Branch.node 0 []) = -Lval; exact logPhi_leaf
    have hc0 : cav (chainB 0) = 1 := by
      show cav (Branch.node 0 []) = 1; exact cav_leaf
    have h32 : Real.log (3 / 2) ≤ 2 * Lval := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 2) rhoB_sq_ge
      rw [Real.log_pow, logRhoB] at h; push_cast at h; linarith
    rw [hstep, h0, eroot_c0_one, hc0, show (1 : ℝ) + 1 / 2 = 3 / 2 from by norm_num]
    linarith
  | (m + 2) => by
    have ih := logPhi_chainB (m + 1)
    have he : eroot 0 [chainB (m + 1)] ≤ 0 := chain_incr_nonpos _ (cav_chainB_bound m).2
    show logPhi (Branch.node 0 [chainB (m + 1)]) ≤ 0
    have hstep : logPhi (Branch.node 0 [chainB (m + 1)])
        = logPhi (chainB (m + 1)) + eroot 0 [chainB (m + 1)] := by
      simp only [logPhi, logPhiSum]; ring
    rw [hstep]; linarith

end R3Cert
