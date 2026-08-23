/-
  R3Cert.LPRSC -- the Lattice Power-Ratio Single-Crossing assembly lemma.

  A new *integrality-aware* certificate primitive for the Brualdi-Goldwasser marginal tie.  Every
  continuous (SOS / Handelman / potential) certificate fails on the BG nucleus because the extremum is a
  non-hyperbolic marginal tie whose CONTINUOUS relaxation is FALSE (the continuous near-star value dips
  to 0.99954 < 1 at the non-integer point s ~ 4.82, while the LATTICE value R(s) >= 1 with R(5) = 1
  exactly, from the integer identity 64*243*23 = 621*576).  LPRSC certifies exactly this lattice fact:
  a positive sequence that strictly decreases up to the tie index and is nondecreasing after attains its
  minimum at the tie; if that minimum equals 1, the sequence is >= 1 everywhere.

  The per-family inputs (from `verification/lprsc_emitter.py`, exact-Fraction verified):
    ratio r n = R(n+1)/R n = C * (P n / Q n)^p,  C = 529/486, p = 11, and a tie index n*=5.
  H1 0<P<Q, H2 P/Q strictly increasing (a Handelman poly-positivity), H3 C>1, H4 single crossing
  r(n*-1)<1<=r(n*), H5 R(n*)=1.  H2+H3 make r increasing; H4 pins the crossing; together they give the
  strict-decrease-then-nondecrease hypotheses of `family_ge_one` below.  The two INDEPENDENTLY-proven BG
  closures -- near-star R_ns(s) and per-child base B(kp) -- are both instances (same C, same p, different
  P/Q), so this lemma unifies them.

  This file proves the ABSTRACT assembly core (dec-then-inc => min at tie => >= 1) fully.  The per-family
  ratio->(dec,inc) bridge is discharged by the emitter's H1-H5 certificates.  Genuine proofs (no `sorry`).
  conjecture1_proved = False -- LPRSC is the marginal-tie primitive, not the whole reduction.
-/
import Mathlib

namespace R3Cert.LPRSC

/-- A positive sequence that strictly decreases on `[0, ns]` and is nondecreasing on `[ns, ∞)` attains
    its minimum at `ns`. -/
theorem ge_min (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1)) :
    ∀ n, R ns ≤ R n := by
  -- downward part: for every `k ≤ ns`, `R ns ≤ R (ns - k)`
  have hdown : ∀ k, k ≤ ns → R ns ≤ R (ns - k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ j ih =>
        intro hk
        have hj : j ≤ ns := Nat.le_of_succ_le hk
        have h1 : R ns ≤ R (ns - j) := ih hj
        have hlt : ns - (j + 1) < ns := by omega
        have hstep : R ((ns - (j + 1)) + 1) < R (ns - (j + 1)) := hdec _ hlt
        have heq : (ns - (j + 1)) + 1 = ns - j := by omega
        rw [heq] at hstep
        exact le_of_lt (lt_of_le_of_lt h1 hstep)
  intro n
  rcases le_or_lt ns n with h | h
  · -- upward part: `ns ≤ n`
    induction n, h using Nat.le_induction with
    | base => exact le_refl _
    | succ m hm ih => exact le_trans ih (hinc m hm)
  · -- `n < ns`, so `n ≤ ns`; use the downward part at `k = ns - n`
    have hk : ns - n ≤ ns := Nat.sub_le ns n
    have := hdown (ns - n) hk
    rwa [Nat.sub_sub_self (le_of_lt h)] at this

/-- **LPRSC conclusion.**  With the tie value `R ns = 1`, the sequence is `≥ 1` everywhere. -/
theorem family_ge_one (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1))
    (htie : R ns = 1) :
    ∀ n, 1 ≤ R n := by
  intro n
  have := ge_min R ns hdec hinc n
  rwa [htie] at this

/-- Monotone-up helper: on `[ns, ∞)`, `R` is nondecreasing. -/
theorem mono_up (R : ℕ → ℚ) (ns : ℕ) (hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1)) :
    ∀ a b, ns ≤ a → a ≤ b → R a ≤ R b := by
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih => exact le_trans ih (hinc m (le_trans ha hm))

/-- Strict version: if the sequence is *strictly* increasing after `ns` as well, then equality `R n = 1`
    holds only at the tie. -/
theorem family_gt_one_off_tie (R : ℕ → ℚ) (ns : ℕ)
    (hdec : ∀ n, n < ns → R (n + 1) < R n)
    (hincS : ∀ n, ns ≤ n → R n < R (n + 1))
    (htie : R ns = 1) :
    ∀ n, n ≠ ns → 1 < R n := by
  have hinc : ∀ n, ns ≤ n → R n ≤ R (n + 1) := fun n hn => le_of_lt (hincS n hn)
  intro n hn
  rcases lt_or_gt_of_ne hn with h | h
  · -- n < ns: strict decrease gives R n > R (n+1) ≥ R ns = 1
    have hstep : R (n + 1) < R n := hdec n h
    have hge : R ns ≤ R (n + 1) := ge_min R ns hdec hinc (n + 1)
    have : (1 : ℚ) ≤ R (n + 1) := by rwa [htie] at hge
    exact lt_of_le_of_lt this hstep
  · -- n > ns: strict step at ns then monotone-up to n
    have hns1 : ns + 1 ≤ n := h
    have h1 : R ns < R (ns + 1) := hincS ns (le_refl _)
    have h2 : R (ns + 1) ≤ R n := mono_up R ns hinc (ns + 1) n (Nat.le_succ ns) hns1
    have : R ns < R n := lt_of_lt_of_le h1 h2
    rwa [htie] at this

end R3Cert.LPRSC
