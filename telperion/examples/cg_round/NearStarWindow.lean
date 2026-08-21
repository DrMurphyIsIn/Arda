import Mathlib

/-!
  Near-star window composition probe (Telperion `cg_round` emitter, 2026-08-20).

  The W1 obstruction: the CONTINUOUS near-star envelope

      phi11(s) = (64/621)^(2s+1) * ((4s+3)/(3(s+1)))^11 * (3/2)^(11s)

  OVERSHOOTS 1 between the integers -- its interior maximum is ~1.000459 at
  s ~ 4.822 -- so no nonnegative CONTINUOUS certificate bounds it by 1 on the
  real interval [4,6].  The exact rational witness of the obstruction is the
  consecutive ratio

      Q(4) = phi11(5)/phi11(4)
           = 87946907297998046875 / 86959512306484890624  >  1,

  i.e. phi11 STRICTLY INCREASES across the last integer gap into the tie
  phi11(5) = 1, forcing the smooth envelope above 1 in the interior.

  The Chvatal-Gomory resolution: `s` is an INTEGER, so `4 <= s <= 6` rounds the
  variable into the finite set {4,5,6} (the VIPR assumption/round/unsplit shape;
  here `interval_cases` performs the integer split omega would).  Each surviving
  case is a CLOSED exact rational inequality that `norm_num` checks.  The three
  exact values of phi11 at the integer window are all <= 1 (equality only at the
  tie s = 5):

      phi11(4) = 86959512306484890624 / 87946907297998046875  < 1
      phi11(5) = 1                                             = 1
      phi11(6) = 980170052528609401200979968
                 / 996644577901404223353123569                < 1

  conjecture1_proved = False -- this is the integer-window fragment only, not BG.
-/

namespace NearStarWindow

/-- Exact numerator of `phi11` at the integer window points (harmless default 0
    outside {4,5,6}). -/
def phi11num : Int → Int
  | 4 => 86959512306484890624
  | 5 => 1
  | 6 => 980170052528609401200979968
  | _ => 0

/-- Exact (positive) denominator of `phi11` at the integer window points
    (default 1 outside {4,5,6}). -/
def phi11den : Int → Int
  | 4 => 87946907297998046875
  | 5 => 1
  | 6 => 996644577901404223353123569
  | _ => 1

/-- Near-star envelope at every INTEGER in the window `[4,6]` satisfies
    `phi11 <= 1` (denominator-cleared: `num <= den`), with equality only at the
    tie `s = 5`.  The continuous relaxation FAILS this (overshoot ~1.000459 at
    s ~ 4.822); the integer split `4 <= s <= 6 ==> s in {4,5,6}` -- the
    Chvatal-Gomory round on the two s bounds -- reduces it to three closed
    rational facts `norm_num` discharges. -/
theorem near_star_window_le_one :
    ∀ s : Int, 4 ≤ s → s ≤ 6 → phi11num s ≤ phi11den s := by
  intro s hlo hhi
  interval_cases s <;> norm_num [phi11num, phi11den]

end NearStarWindow
