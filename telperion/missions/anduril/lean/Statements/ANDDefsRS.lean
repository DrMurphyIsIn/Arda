/-
  Statements.ANDDefsRS -- vocabulary mirror for the RSC0 DRAFT nodes AND_rs_remainder_c0_sharp and
  AND_rs_remainder_c0_seam_sharp ONLY.  NOT a node statement.

  Kept OUT of Statements.ANDDefs on purpose: ANDDefs is imported by seven proved, granted nodes and lies outside every
  node's statement hash (verify.py hashes the statement body without import lines), so extending it would change what
  those statements mean without any hash noticing.  This file is imported only by the two RSC0 statement files.

  Every definition below is a VERBATIM copy from the v4.32 zeta_reflection island (each source file sits in
  `namespace RSInt` with `open Complex ...` and `open scoped Real` inside a `noncomputable section`); source module and
  line cited above each extract.  conjecture1_proved = False.
-/
import Mathlib

namespace RSInt

open Complex
open scoped Real

noncomputable section

-- ===== RS_Strip.lean:164 =====
def lineUp (c : ℝ) (F : ℂ → ℂ) : ℂ := ∫ v : ℝ, F (c + v * (1 + I)) * (1 + I)

-- ===== RS_Kernel.lean:46 =====
def rsD (x : ℂ) : ℂ := cexp (↑π * I * x) - cexp (-(↑π * I * x))

-- ===== RS_Kernel.lean:49 =====
def rsG (x : ℂ) : ℂ := cexp (↑π * I * x ^ 2) / rsD x

-- ===== RS_B3.lean:42 =====
def rsAlpha (t : ℝ) : ℝ := Real.sqrt (t / (2 * π))

-- ===== RS_B3.lean:45 =====
def rsNn (t : ℝ) : ℕ := ⌊rsAlpha t⌋₊

-- ===== RS_B3.lean:48 =====
def rsFrac (t : ℝ) : ℝ := rsAlpha t - rsNn t

-- ===== RS_B3.lean:51-52 =====
def rsThetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log t - t / 2 * Real.log (2 * Real.pi) - t / 2 - Real.pi / 8

-- ===== RS_B3.lean:55 =====
def rsPsi (p : ℝ) : ℝ := Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p)

-- ===== RS_B3.lean:58-59 =====
def rsRem (t : ℝ) : ℂ :=
  -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))

end

end RSInt
