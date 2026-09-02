/-
  BG asymptotic upper bound — the SCL price-flow layer (2026-09-02).

  Builds on `R3Cert.BGSCLInduction` (the concrete cavity `total`/`ell`/`V_μ`, the ell recursion `bell_node`,
  the concave tangent `bell_node_tangent`, the hub `y`-formula `bY_node`, and the reduction `scl_of_step`).
  The remaining obligation `SCLStep` is the per-hub decouple, which flows the price `μ ↦ μ'' =
  3(4d−1−3μ)/(4d−1)²` (telperion's `ExtremalityPriceMap`, gated leg #1) and needs the induction to carry the
  SCL for ALL prices in the invariant interval `I = [456/3703, 3/7]`.

  What is PROVED here (verified by local `lake build`, no `sorry`):
    * `inI`, `muPP` — the invariant price interval and the concavity-tangent price map.
    * `muPP_mem_I` — **the price map keeps `I` invariant for hub-degrees `2 ≤ d ≤ 6`** (leg #1), by a pure
      rational box inequality.  (For `d ≥ 7` the hub is high-degree, handled by the ceiling, not this decouple.)
    * `PSCL`, `scl_of_step'` — the price-carrying predicate `∀ μ ∈ I, V_μ(b) ≤ V_μ(cherry)` and the well-founded
      recursion driving it (reusing `scl_of_child_step`), reducing the SCL to a per-hub step whose child IH is
      available at EVERY price in `I` — so it can be instantiated at the flowed price `μ'' ∈ I`.

  REMAINING (see plan `sorted-conjuring-clock`): the per-hub decouple itself — the tangent bound at the
  all-cherry reference + the child IH at `μ''` + `hbroom` (broom-vs-cherry leg #4 via `Real.log` enclosures) —
  and the leaf-exclusion subtlety (a bare leaf child violates the SCL for `μ > 0.297 ∈ I`, so the extremality is
  over leaf-free hubs).  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

/-- The invariant price interval `I = [456/3703, 3/7]` (the largest window containing all hub prices
    `μ_d = 3/(4d−1)` and clear of the tie's low-price inversion `μ ≈ 0.038`). -/
def inI (μ : ℝ) : Prop := (456 : ℝ) / 3703 ≤ μ ∧ μ ≤ 3 / 7

/-- The concavity-tangent price map: a degree-`d` hub at price `μ` flows its children to price
    `μ'' = 3(4d−1−3μ)/(4d−1)²` (`= ν(S*)`, the tangent slope at the all-cherry reference). -/
noncomputable def muPP (d μ : ℝ) : ℝ := 3 * (4 * d - 1 - 3 * μ) / (4 * d - 1) ^ 2

/-- **Price-map invariance (leg #1).**  For hub-degrees `2 ≤ d ≤ 6`, the map `μ ↦ μ''` keeps `I` invariant:
    `μ ∈ I ⇒ μ'' ∈ I`.  Pure rational box inequality (`nlinarith`).  (`A = 456/3703` is the fixed point of the
    tightest `d = 6` map; degrees `≥ 7` are high-degree hubs handled by the ceiling, not this decouple.) -/
theorem muPP_mem_I {d μ : ℝ} (hd : 2 ≤ d) (hd6 : d ≤ 6) (h : inI μ) : inI (muPP d μ) := by
  obtain ⟨hlo, hhi⟩ := h
  have hpos : (0:ℝ) < (4 * d - 1) ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [muPP, le_div_iff₀ hpos]
    nlinarith [sq_nonneg (d - 2), sq_nonneg (d - 6),
      mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hd6)]
  · rw [muPP, div_le_iff₀ hpos]
    nlinarith [sq_nonneg (d - 2)]

/-- The price-carrying SCL predicate: `V_μ(b) ≤ V_μ(cherry)` for EVERY price `μ ∈ I`.  Carrying `∀ μ ∈ I` is
    what lets the induction instantiate the child IH at the flowed price `μ'' ∈ I` (`muPP_mem_I`). -/
def PSCL (b : Branch) : Prop := ∀ μ, inI μ → bV μ b ≤ bV μ cherry

/-- **The SCL from the per-hub step, price-flow version.**  Given the per-hub step (every hub whose children
    all satisfy `PSCL` satisfies `PSCL`), the price-carrying SCL holds for EVERY branch, by the well-founded
    recursion on `|b|`.  Reduces the SCL to the per-hub decouple with the child IH available at all `μ ∈ I`. -/
theorem scl_of_step' (hstep : ∀ cs : List Branch, (∀ c ∈ cs, PSCL c) → PSCL (Branch.node cs)) :
    ∀ b, PSCL b := by
  refine scl_of_child_step bsize bchildren PSCL bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs => exact hstep cs (fun c hc => hIH c (by simpa only [bchildren] using hc))

end BGSCL
end R3Cert
