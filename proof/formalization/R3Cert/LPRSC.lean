/-
  R3Cert.LPRSC -- the Lattice Power-Ratio Single-Crossing assembly lemma.

  A new *integrality-aware* certificate primitive for the Brualdi-Goldwasser marginal tie.  Every
  continuous (SOS / Handelman / potential) certificate fails on the BG nucleus because the extremum is a
  non-hyperbolic marginal tie whose CONTINUOUS relaxation is FALSE (the continuous near-star value dips
  to 0.99954 < 1 at the non-integer point s ~ 4.82, while the LATTICE value R(s) >= 1 with R(5) = 1
  exactly, from the integer identity 64*243*23 = 621*576).  LPRSC certifies exactly this lattice fact:
  a positive sequence that strictly decreases up to the tie index and is nondecreasing after attains its
  minimum at the tie; if that minimum equals 1, the sequence is >= 1 everywhere.

  Per-family inputs (from `verification/lprsc_emitter.py`, exact-Fraction verified): the ratio
  r n = R(n+1)/R n = C * (P n / Q n)^p, C = 529/486, p = 11, tie index n*=5.  H1 0<P<Q, H2 P/Q strictly
  increasing (a Handelman poly-positivity), H3 C>1, H4 single crossing r(n*-1)<1<=r(n*), H5 R(n*)=1
  give the strict-decrease-then-nondecrease hypotheses of `family_ge_one` below.  The two INDEPENDENTLY-
  proven BG closures -- near-star R_ns(s) and per-child base B(kp) -- are both instances (same C, same p,
  different P/Q), so this lemma unifies them.

  This file proves the ABSTRACT assembly core fully (monotone-up + antitone-down => min at tie => >= 1).
  Genuine proofs (no `sorry`).  conjecture1_proved = False -- LPRSC is the marginal-tie primitive, not
  the whole reduction.
-/
import Mathlib

namespace R3Cert.LPRSC

/-- Monotone-up: on `[ns, ∞)`, `R` is nondecreasing. -/
theorem mono_up (R : ℕ → ℚ) (ns : ℕ) (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1)) :
    ∀ a b, ns ≤ a → a ≤ b → R a ≤ R b := by
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih => exact le_trans ih (hinc m (le_trans ha hm))

/-- Antitone-down: on `[0, ns]`, `R` is nonincreasing (from the strict-decrease hypothesis). -/
theorem anti_down (R : ℕ → ℚ) (ns : ℕ) (hdec : ∀ n, n < ns → R (n + 1) < R n) :
    ∀ a b, a ≤ b → b ≤ ns → R b ≤ R a := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ m hm ih =>
      intro hb
      have hmns : m ≤ ns := Nat.le_of_succ_le hb
      have hstep : R (m + 1) < R m := hdec m (by omega)
      exact le_trans (le_of_lt hstep) (ih hmns)

/-- A positive sequence strictly decreasing on `[0, ns]` and nondecreasing on `[ns, ∞)` attains its
    minimum at `ns`. -/
theorem ge_min (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1)) :
    ∀ n, R ns ≤ R n := by
  intro n
  rcases Nat.lt_or_ge n ns with h | h
  · exact anti_down R ns hdec n ns (le_of_lt h) (le_refl ns)
  · exact mono_up R ns hinc ns n (le_refl ns) h

/-- **LPRSC conclusion.**  With the tie value `R ns = 1`, the sequence is `≥ 1` everywhere. -/
theorem family_ge_one (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1))
    (htie : R ns = 1) :
    ∀ n, 1 ≤ R n := by
  intro n
  have h := ge_min R ns hdec hinc n
  rwa [htie] at h

/-- Strict version: if the sequence is *strictly* increasing after `ns` as well, then `R n = 1` holds
    only at the tie. -/
theorem family_gt_one_off_tie (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hincS : ∀ n, ns ≤ n → R n < R (n + 1))
    (htie : R ns = 1) :
    ∀ n, n ≠ ns → 1 < R n := by
  have hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1) := fun n hn => le_of_lt (hincS n hn)
  intro n hn
  rcases lt_or_lt_iff_ne.mpr hn with h | h
  · -- n < ns
    have hstep : R (n + 1) < R n := hdec n h
    have hge : R ns ≤ R (n + 1) := ge_min R ns hdec hinc (n + 1)
    have h1 : (1 : ℚ) ≤ R (n + 1) := by rwa [htie] at hge
    exact lt_of_le_of_lt h1 hstep
  · -- ns < n
    have h1 : R ns < R (ns + 1) := hincS ns (le_refl _)
    have h2 : R (ns + 1) ≤ R n := mono_up R ns hinc (ns + 1) n (Nat.le_succ ns) h
    have h3 : R ns < R n := lt_of_lt_of_le h1 h2
    rwa [htie] at h3

end R3Cert.LPRSC
