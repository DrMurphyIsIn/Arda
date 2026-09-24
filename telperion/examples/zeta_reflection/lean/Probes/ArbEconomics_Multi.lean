/-  Probes/ArbEconomics_Multi.lean -- COST PROXY for the "shared partial sums" optimization.

    One pass over n evaluates the Dirichlet sum at a whole uniform grid t_j = t0 + j h,
    j = 0..G-1, of a band:  n^(-1/2 - i t_j) = w_n u_n^j  with  w_n = n^(-1/2) e^(-i t0 log n)
    and the per-n ROTOR u_n = e^(-i h log n).  Per n it pays ONE log increment, ONE square root and
    TWO trig evaluations (at t0 log n and h log n, via `ArbEconomics_Eval.trig`); per grid point
    only one complex multiplication and one accumulation.

    STATUS: arithmetic only, validated against mpmath by the generator (arbecon_multi.py); the
    rotor error analysis is NOT formalized, so these kernel checks measure COST, they are not
    enclosure theorems (the single-point evaluator of ArbEconomics_Eval/Sound/Zeta is the
    certified one).  conjecture1_proved = False.
-/
import Probes.ArbEconomics_Eval

namespace ArbEcon.Multi

noncomputable section

/-- A complex value in sign-magnitude form `(sa ? a : -a) + i (sb ? b : -b)` at scale 2^P. -/
structure CV where
  a : Nat
  sa : Bool
  b : Nat
  sb : Bool

/-- `a == b` on Bool as a raw `Bool.rec` (the `BEq`/`DecidableEq` route costs ~15 us per use in
    the kernel, this costs ~1 us; measured in ArbEconomics_Micro). -/
def xnor (a b : Bool) : Bool := Bool.rec (Bool.rec true false b) (Bool.rec false true b) a

/-- `!a` as a raw `Bool.rec`. -/
def bnot (a : Bool) : Bool := Bool.rec true false a

/-- signed sum of two sign-magnitude reals, as (magnitude, sign) -/
def sadd (x : Nat) (sx : Bool) (y : Nat) (sy : Bool) : Nat × Bool :=
  Bool.rec
    -- different signs: subtract the smaller magnitude
    (Bool.rec (Nat.sub y x, sy) (Nat.sub x y, sx) (Nat.ble y x))
    (Nat.add x y, sx)
    (xnor sx sy)

/-- complex product (v * u) / 2^P in sign-magnitude form -/
def cmul (P : Nat) (v u : CV) : CV :=
  let ac := Nat.shiftRight (Nat.mul v.a u.a) P
  let bd := Nat.shiftRight (Nat.mul v.b u.b) P
  let ad := Nat.shiftRight (Nat.mul v.a u.b) P
  let bc := Nat.shiftRight (Nat.mul v.b u.a) P
  -- re = ac - bd ; im = ad + bc
  let re := sadd ac (xnor v.sa u.sa) bd (bnot (xnor v.sb u.sb))
  let im := sadd ad (xnor v.sa u.sb) bc (xnor v.sb u.sa)
  ⟨re.1, re.2, im.1, im.2⟩

/-- accumulators: per grid point (reP, reN, imP, imN) -/
abbrev Acc := Nat × Nat × Nat × Nat

def accAdd (x : Acc) (v : CV) : Acc :=
  (Bool.rec x.1 (Nat.add x.1 v.a) v.sa, Bool.rec (Nat.add x.2.1 v.a) x.2.1 v.sa,
   Bool.rec x.2.2.1 (Nat.add x.2.2.1 v.b) v.sb, Bool.rec (Nat.add x.2.2.2 v.b) x.2.2.2 v.sb)

/-- sweep the grid: add v to accumulator j, then rotate v by u -/
def sweep (P : Nat) (u : CV) (accs : List Acc) : CV → List Acc :=
  List.rec (motive := fun _ => CV → List Acc) (fun _ => [])
    (fun x _ ih v => accAdd x v :: ih (cmul P v u)) accs

structure MSt where
  n : Nat
  llo : Nat
  lhi : Nat
  g : Nat
  accs : List Acc

/-- multi-point config: the single-point config for t0 plus the step h = hn / 2^hq -/
structure MCfg where
  c : ArbEcon.Cfg
  hn : Nat
  hq : Nat

/-- one n-step for the whole grid -/
def mstep (mc : MCfg) (s : MSt) : MSt :=
  let c := mc.c
  let m := Nat.succ s.n
  let lg := ArbEcon.logInc c m
  let llo := Nat.add s.llo lg.1
  let lhi := Nat.add (Nat.add (Nat.add s.lhi lg.1) lg.2.1) (Nat.add (Nat.div c.two1 lg.2.2) 1)
  let g := ArbEcon.isqrt c m (Nat.div c.oneSq m) s.g
  let R := g
  let t0 := ArbEcon.trig c (Nat.shiftRight (Nat.mul c.tn llo) c.tq)
    (Nat.add (Nat.shiftRight (Nat.mul c.tn lhi) c.tq) 1)
  let tu := ArbEcon.trig c (Nat.shiftRight (Nat.mul mc.hn llo) mc.hq)
    (Nat.add (Nat.shiftRight (Nat.mul mc.hn lhi) mc.hq) 1)
  -- w = R (cos - i sin)(t0 log m),  u = cos - i sin (h log m)
  let w : CV := ⟨Nat.shiftRight (Nat.mul R t0.cm) c.P, t0.cs, Nat.shiftRight (Nat.mul R t0.sm) c.P, bnot t0.ss⟩
  let u : CV := ⟨tu.cm, tu.cs, tu.sm, bnot tu.ss⟩
  ⟨m, llo, lhi, g, sweep c.P u s.accs w⟩

def mrun (mc : MCfg) (count : Nat) : MSt → MSt :=
  Nat.rec (motive := fun _ => MSt → MSt) (fun s => s) (fun _ ih s => ih (mstep mc s)) count

def accBeq (x y : Acc) : Bool :=
  Nat.beq x.1 y.1 && Nat.beq x.2.1 y.2.1 && Nat.beq x.2.2.1 y.2.2.1 && Nat.beq x.2.2.2 y.2.2.2

def accsBeq : List Acc → List Acc → Bool
  | [], [] => true
  | x :: xs, y :: ys => accBeq x y && accsBeq xs ys
  | _, _ => false

def MSt.beq (a b : MSt) : Bool :=
  Nat.beq a.n b.n && Nat.beq a.llo b.llo && Nat.beq a.lhi b.lhi && Nat.beq a.g b.g && accsBeq a.accs b.accs

end

end ArbEcon.Multi
