import R3Cert.R7CollapseCompose
import R3Cert.HingeProfileFloor

/-!
  # R7/G7 rung brick — mixed `a=1` collapse floor for ARBITRARY child profiles — 2026-08-22

  The G7 assembly's mixed-`a=1` collapse floor has, on `main`, two green halves:

  * the **equal-children** floor `R3Cert.R7CollapseMono.full_slack_ge_floor`
    (`∀ m ≥ 4, y ≥ 0 : 27/5000 ≤ full_slack m y`), which minimises the slack over the
    child cavity `y` at the real knee `T0 = ρB − 1` and then invokes the certified point
    floor; and
  * the **profile→equal** hinge subadditivity `R3Cert.HingeProfileFloor.hinge_profile_floor`
    (`(Σ y i − |s|·t0)⁺ ≤ Σ (y i − t0)⁺`).

  The follow-up flagged in `R7CollapseCompose.lean` ("lifting arbitrary UNEQUAL child
  profiles to the equal case ... composed on top via `Σφ(y_c) ≥ k·φ(ȳ)`") is exactly the
  composition of these two.  This file writes it.

  The mixed-`a=1` collapse node carries `m` structural collapse children at cavities
  `{y_c}` (plus the `a=1` arm + `nl=0` leaf, so total children `k = 1+m`, `slk`-denominator
  `k+1 = m+2`).  Its full slack as a function of the profile is

      full_slack_profile s y
        = 3·Lval − log(3/2)
          − log(1 + (1/3 + Σ_{c∈s} y c)/(|s| + 2))     (log depends only on the TOTAL Σy)
          + (11/50)·Σ_{c∈s} (y c − T0)⁺                 (the per-child hinge slacks).

  Because the log term depends on the children ONLY through their sum `S = Σ y c`, it equals
  the equal-children log term at the mean `ȳ = S/|s|` (there `|s|·ȳ = S`).  The hinge term
  dominates its collapsed value by `hinge_profile_floor`.  Hence

      full_slack_profile s y  ≥  full_slack |s| (S/|s|)  ≥  27/5000     (`∀ |s| ≥ 4`).

  This is an EXACT composition of two green theorems — no new transcendental bound, no
  Jensen gap on the log (the log term is linear in the collapsed variable `S`, not strictly
  convex in the individual `y_c`).  It is a rung of G7, NOT a closure of Gap-1: the general
  branching case (arbitrary child cavities under a SINGLE monotone potential) remains open
  and is equivalent to the conjecture (`branching_folded_potential.py`).  What is closed
  here is the mixed-`a=1` per-class ledger floor for arbitrary child multiplicities.

  Name-checked against the pinned Mathlib and local `R3Cert/`; CI-pending (no local build).
  A standalone leaf (imports only the two green inputs; nothing imports it — same registration
  status as `R47RootInvariance`).  To include it in the `lake build` verification set, the
  merge owner adds `import R3Cert.R47CampaignBrick` to `R3Cert.lean` (NOT done here per the
  shared-file constraint).  `conjecture1_proved = False`.
-/

namespace R3Cert.R47CampaignBrick

open Finset R3Cert.R7CollapseMono R3Cert.HingeProfileFloor

/-- Bridge `posPart` to the `max 0 (·)` form used by `slk`/`full_slack`.
    `x⁺ = x ⊔ 0 = max x 0 = max 0 x` (the middle equality is `rfl` on `ℝ`). -/
theorem posPart_eq_max_zero (x : ℝ) : x⁺ = max 0 x := by
  rw [posPart_def]
  show max x 0 = max 0 x
  exact max_comm x 0

/-- Full slack of the mixed `a=1` collapse class with an ARBITRARY child profile `y : ι → ℝ`
    supported on `s` (`p=3`, `a=1`, `nl=0`, `k=1+|s|`, `c0=1/3`, knee `t=T0=ρB−1`).  The log
    term depends on the children only through their sum; the hinge is summed per child.  At a
    constant profile `y c = y₀` on a set of size `m` this reduces to `full_slack m y₀`. -/
noncomputable def full_slack_profile {ι : Type*} (s : Finset ι) (y : ι → ℝ) : ℝ :=
  3 * Lval - Real.log (3 / 2)
    - Real.log (1 + (1 / 3 + ∑ c ∈ s, y c) / ((s.card : ℝ) + 2))
    + (11 / 50 : ℝ) * ∑ c ∈ s, (y c - (rhoB - 1))⁺

/-- The collapsed (equal-children-at-the-mean) value the profile slack dominates: the log
    term at the total `S = Σy`, and the hinge collapsed to a single `posPart`. -/
noncomputable def full_slack_collapsed {ι : Type*} (s : Finset ι) (y : ι → ℝ) : ℝ :=
  3 * Lval - Real.log (3 / 2)
    - Real.log (1 + (1 / 3 + ∑ c ∈ s, y c) / ((s.card : ℝ) + 2))
    + (11 / 50 : ℝ) * ((∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1))⁺

/-- The profile slack dominates the collapsed value: only the hinge term differs, and
    `hinge_profile_floor` gives `(Σy − |s|·T0)⁺ ≤ Σ(y c − T0)⁺`. -/
theorem full_slack_profile_ge_collapsed {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    full_slack_collapsed s y ≤ full_slack_profile s y := by
  unfold full_slack_profile full_slack_collapsed
  have hcard : ((∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1))
      = (∑ c ∈ s, y c) - s.card • (rhoB - 1) := by
    rw [nsmul_eq_mul]
  have hh : ((∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1))⁺ ≤ ∑ c ∈ s, (y c - (rhoB - 1))⁺ := by
    rw [hcard]; exact hinge_profile_floor s y (rhoB - 1)
  have hmul : (11 / 50 : ℝ) * ((∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1))⁺
      ≤ (11 / 50 : ℝ) * ∑ c ∈ s, (y c - (rhoB - 1))⁺ :=
    mul_le_mul_of_nonneg_left hh (by norm_num)
  linarith [hmul]

/-- The collapsed value equals the equal-children `full_slack` at the mean `S/|s|` (needs
    `|s| ≠ 0`).  The `slk`-log arg matches since `|s|·(S/|s|) = S` and `(|s|+1)+1 = |s|+2`,
    and the collapsed hinge matches `(11/50)·|s|·max 0 (S/|s| − T0)` by `mul_max_of_nonneg`. -/
theorem full_slack_collapsed_eq_mean {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hne : s.Nonempty) :
    full_slack_collapsed s y
      = full_slack s.card ((∑ c ∈ s, y c) / (s.card : ℝ)) := by
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  -- abbreviations (not `set`, so post-`unfold` occurrences stay as `↑s.card`)
  have hmul : (s.card : ℝ) * ((∑ c ∈ s, y c) / (s.card : ℝ)) = ∑ c ∈ s, y c :=
    mul_div_cancel₀ (∑ c ∈ s, y c) hcpos.ne'
  -- denominator cast: `↑(1 + s.card) + 1 = ↑s.card + 2` (the `slk` `(k:ℝ)+1` shape)
  have hden : ((1 + s.card : ℕ) : ℝ) + 1 = (s.card : ℝ) + 2 := by push_cast; ring
  -- collapsed hinge = equal-children hinge: `(S − n·T0)⁺ = n · max 0 (S/n − T0)`
  have hinner : (s.card : ℝ) * ((∑ c ∈ s, y c) / (s.card : ℝ) - (rhoB - 1))
      = (∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1) := by
    rw [mul_sub, hmul]
  have hhinge : ((∑ c ∈ s, y c) - (s.card : ℝ) * (rhoB - 1))⁺
      = (s.card : ℝ) * max 0 ((∑ c ∈ s, y c) / (s.card : ℝ) - (rhoB - 1)) := by
    rw [posPart_eq_max_zero, mul_max_of_nonneg _ _ hcpos.le, mul_zero, hinner]
  unfold full_slack_collapsed full_slack slk
  -- rewrite `↑s.card·(S/↑s.card) → S` (log arg), the denom cast, and the collapsed hinge
  rw [hmul, hden, hhinge]
  ring

/-- **Mixed `a=1` collapse floor for arbitrary child profiles.**  For every nonempty child
    profile `y : ι → ℝ` on `s` with at least 4 collapse children and all cavities `≥ 0`, the
    profile slack is at least the class floor `27/5000`.  Composes
    `full_slack_profile_ge_collapsed` (hinge subadditivity, `hinge_profile_floor`) with
    `full_slack_ge_floor` (the equal-children floor) at the mean.  A G7 rung; NOT Gap-1. -/
theorem full_slack_profile_ge_floor {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hcard : 4 ≤ s.card) (hy : ∀ c ∈ s, 0 ≤ y c) :
    (27 : ℝ) / 5000 ≤ full_slack_profile s y := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hSnn : (0 : ℝ) ≤ ∑ c ∈ s, y c := Finset.sum_nonneg hy
  have hcpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hmean : (0 : ℝ) ≤ (∑ c ∈ s, y c) / (s.card : ℝ) := div_nonneg hSnn hcpos.le
  have hfloor : (27 : ℝ) / 5000 ≤ full_slack s.card ((∑ c ∈ s, y c) / (s.card : ℝ)) :=
    full_slack_ge_floor s.card hcard ((∑ c ∈ s, y c) / (s.card : ℝ)) hmean
  have heq : full_slack_collapsed s y
      = full_slack s.card ((∑ c ∈ s, y c) / (s.card : ℝ)) :=
    full_slack_collapsed_eq_mean s y hne
  have hge : full_slack_collapsed s y ≤ full_slack_profile s y :=
    full_slack_profile_ge_collapsed s y
  linarith [hfloor, heq ▸ hge]

end R3Cert.R47CampaignBrick
