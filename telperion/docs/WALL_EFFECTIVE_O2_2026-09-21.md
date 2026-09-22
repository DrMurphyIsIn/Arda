# Effective Gaussian dominance (open lemma 1 of the wall reconciliation), 2026-09-21

Module: `telperion/examples/rvm_bridge/lean/E6Bridge14.lean` (namespace `RvMBridge14`, imports
E6Bridge12). Probe: `Probes/E6Bridge14_probe.lean`. Every theorem prints
`[propext, Classical.choice, Quot.sound]`; no sorry. conjecture1_proved = False: the statements
are unconditional inequalities about a Gaussian-weighted sum over the zeros of zeta, wherever
they are.

## 1. What was wrong with the non-effective version

`RvMBridge7.gaussian_dominance` proves: an off-line zero gives some centre c and some lam with
Re S(c, lam) < 0, where S(c, lam) = Sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2).
Its lam is chosen after the zero configuration: the gap eta to the second-best exponent, the
finite window sum A and the tail sum B are extracted by existence from the finite set of nearby
zeros. A consumer cannot certify that lam. The effective version replaces those existentials by
explicit parameters and gives lam as a formula.

## 2. The theorem in words

Let rho_0 be a nontrivial zero. Take the centre c := Im rho_0 exactly. Suppose

- (distance floor) 0 < y0 <= |1/2 - Re rho_0|;
- (window) D >= 1, and rho_0 has maximal |1/2 - Re| among nontrivial zeros with
  |Im rho - Im rho_0| <= D;
- (spacing floor) every nontrivial zero in that window at a different ordinate has
  |Im rho - Im rho_0| >= xmin > 0;
- (count) the window holds at most N zeros with multiplicity
  (`∑ ρ ∈ RvMBridge12.zeroWindow (Im rho_0) D, zeroMult ρ ≤ N`);
- (tail constant) B := constB (Im rho_0), the lam = 1 local-count majorant sum of E6Bridge7.

Then for every lam >= effectiveThreshold y0 xmin N B D,

    effectiveThreshold y0 xmin N B D
      = max 1 (max (log(max 1 (4 N (D^2 + 1/4) / y0^2)) / (2 xmin^2))
                   (log(max 1 (4 B / y0^2)) / (2 y0^2))),

Re S(Im rho_0, lam) < 0. In fact Re S <= -(y0^2/2) e^{2 lam Y}, Y = (1/2 - Re rho_0)^2.

Why the centre needs no genericity: at c = Im rho_0 every zero on the same ordinate has x = 0, so
its summand is m (-(y^2) e^{2 lam y^2}) <= 0 with the phase automatically pi
(`re_term_centre`, from E6Bridge6.gaussTest_axis); rho_0 itself gives at most -Y e^{2 lam Y}
(multiplicity >= 1). A window zero at a different ordinate has |x| >= xmin and y^2 <= Y by
maximality, so |summand| <= m (D^2 + 1/4) e^{2 lam (Y - xmin^2)} (`norm_term_le_competitor`); the
window sum is a finite sum over the certified window (`tsum_winSet_eq_sum`) and is at most
-Y e^{2 lam Y} + N (D^2 + 1/4) e^{-2 lam xmin^2} e^{2 lam Y} (`re_window_sum_le`). The tail is at
most e^{2 (lam - 1)(1/4 - D^2)} B <= B (E6Bridge12.tail_bound_window, lam >= 1, D >= 1). The first
log term makes N (D^2 + 1/4) e^{-2 lam xmin^2} <= y0^2/4, the second makes B <= (y0^2/4) e^{2 lam y0^2}
<= (y0^2/4) e^{2 lam Y}; total <= -y0^2 E + y0^2 E/2 < 0. The `max 1 (...)` inside the logs keeps
the formula meaningful when N = 0 or B = 0 (log of a nonpositive number is junk in Mathlib) and
makes the threshold monotone in B (`effectiveThreshold_mono_B`).

## 3. Which hypotheses are load-bearing, and why

- Maximality of |1/2 - Re rho_0| in the window. This is the honest form of the sweep's
  "clustering control". Without it a zero rho' at ordinate distance x' with larger y' has
  exponent y'^2 - x'^2, which exceeds Y when x'^2 < y'^2 - Y, and its summand
  2 m |w'|^2 e^{2 lam (y'^2 - x'^2)} cos(2 arg w' - 4 lam x' y') is positive for a positive-density
  set of lam. No threshold of the form above can beat it. E6Bridge7 handles this by a generic
  centre and a phase choice AFTER the configuration; the effective version instead asks the
  consumer to hand over the maximal zero (the localisation instrument, section 4, finds it).
- The spacing floor xmin. The threshold scales like log(...) / (2 xmin^2) and is unbounded as
  xmin -> 0 (`effectiveThreshold_unbounded_of_small_spacing`, kernel-checked: for N >= 1,
  D >= 1, 0 < y0 <= 1/2 and any K there is xmin > 0 with threshold >= K). Mathematically, a zero
  with the same y at ordinate distance x' has |summand| = m (x'^2 + y^2) e^{2 lam (y^2 - x'^2)},
  which is within a factor e^{-2 lam x'^2} of the main term; only lam >> 1/x'^2 separates them.
- The count N and the window D. N enters only through the crude bound (D^2 + 1/4) per zero;
  D >= 1 is used for the tail envelope e^{2 (lam - 1)(1/4 - D^2)} <= 1.
- Note the competitor lemma is FALSE for negative xmin (xmin^2 could exceed x'^2); the theorem
  carries 0 < xmin.

## 4. The localisation instrument

`offline_zeros_small_or_margin`. Hypotheses on a band c in [T1, T2]: the window count bound at
every c, the spacing floor between every band ordinate and every zero within D of it, a uniform
bound Bmax on constB c, and Gaussian positivity Re S(c, lam) >= 0 for every c in the band and
every lam >= effectiveThreshold y0 xmin N Bmax D. Conclusion (a disjunction, honestly):

- every nontrivial zero with ordinate in [T1 - D, T2 + D] has |1/2 - Re| < y0; or
- some nontrivial zero in a margin [T1 - D, T1) or (T2, T2 + D] has |1/2 - Re| >= y0 and is the
  zero of maximal |1/2 - Re| over the whole widened band.

Proof: the widened band is finite (`band_finite`); take the zero of maximal |1/2 - Re| over it. If
its distance is < y0 the first branch holds. If its ordinate lies in [T1, T2], its D-window sits
inside the widened band, so it is window-maximal; the effective theorem at c = its ordinate and
lam = the threshold (monotone in B, so the threshold built from Bmax dominates the one built from
constB c) contradicts positivity. Otherwise it lies in a margin: second branch. The margin case
is genuine: the maximal zero of the widened band can sit just outside the band where positivity
is assumed, and the instrument cannot see it; the consumer slides the band.

## 5. What a consumer needs to supply

- y0: the target distance from the line (a parameter, not data).
- xmin: a local spacing floor between ordinates of zeros within D of the centre. Certified
  enclosures of the zeros in the window (Turing-method style isolation) give this directly; equal
  ordinates are allowed (they add negatively at the centre) but ordinates closer than xmin are
  not.
- N: the window count with multiplicity, `∑ ρ ∈ zeroWindow c D, zeroMult ρ`;
  `windowCount_le_Ncount` bounds it by Zeta23.Ncount (c - D - 1) (c + D), the cumulative local
  count that E6Bridge2's Riemann-von Mangoldt node certifies with an O(log T) remainder.
- B: constB c = Sum_rho m(rho) e^{1/2} (2 c^2 + 13/4) / (1 + |gamma_rho|^2); an explicit numeric
  bound follows from N(T) = O(T log T) (Zeta23.WeilEF.zero_sum_inv_sq is the summability; the
  numeric constant is not pinned in this repository yet).
- D: any D >= 1; larger D means a larger N and a weaker spacing requirement is NOT implied, so
  D = 1 or 2 is the natural choice.

Numeric sanity (kernel-checked in the probe): y0 = 1/10, xmin = 1/5, N = 20, D = 2, B = 1 gives
effectiveThreshold in [297, 300] (its value is 50 log 400 = 299.57...; the window term is
log 34000 / (2/25) = 130.4...). The tail term dominates at these values; with B pinned
numerically the threshold is a few hundred.

## 6. Lemma ledger (all kernel-checked)

- `effectiveThreshold` (def), `one_le_effectiveThreshold`, `effectiveThreshold_pos`,
  `le_exp_of_log_le`, `effectiveThreshold_mono_B`, `effectiveThreshold_unbounded_of_small_spacing`
- `tsum_winSet_eq_sum` (window tsum is a finite sum), `re_term_centre`, `re_term_centre_nonpos`
- `norm_term_le_competitor`, `re_window_sum_le` (the window estimate with explicit constants)
- `effective_gaussian_dominance` (the theorem)
- `band_finite`, `offline_zeros_small_or_margin` (the instrument), `windowCount_le_Ncount`
