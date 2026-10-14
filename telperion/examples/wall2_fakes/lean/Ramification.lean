/- WALL-2 / T: ramification bookkeeping for corollary_fix.md section 4 (generated; do not edit).
   Core Lean only (no Mathlib).  conjecture1_proved = False.  Kernel checks polynomial arithmetic mod p;
   Dedekind-Kummer (Z[alpha] = O_K for these generators) and disc(g) = d_K are CITED, not checked. -/

def pmod (p : Nat) (l : List Nat) : List Nat := l.map (· % p)

def addL (p : Nat) : List Nat → List Nat → List Nat
  | [], ys => pmod p ys
  | xs, [] => pmod p xs
  | x :: xs, y :: ys => ((x + y) % p) :: addL p xs ys

def scal (p c : Nat) (l : List Nat) : List Nat := l.map (fun a => (c * a) % p)

def mulL (p : Nat) : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: xs, ys => addL p (scal p x ys) (0 :: mulL p xs ys)

def powL (p : Nat) (f : List Nat) : Nat → List Nat
  | 0 => [1]
  | k + 1 => mulL p f (powL p f k)

def prodL (p : Nat) : List (List Nat × Nat) → List Nat
  | [] => [1]
  | (f, e) :: r => mulL p (powL p f e) (prodL p r)

def evalL (p a : Nat) (l : List Nat) : Nat := l.foldr (fun c acc => (c + a * acc) % p) 0

/-- drop trailing zeros -/
def trim (l : List Nat) : List Nat := (l.reverse.dropWhile (· == 0)).reverse

/-- remainder of g (low-to-high) modulo the monic quadratic x^2 + a x + b, by synthetic division
    from the top coefficient; fuel = length of g. -/
def remQ (p a b : Nat) : Nat → List Nat → List Nat
  | 0, g => g
  | fuel + 1, g =>
    let g := trim g
    if g.length ≤ 2 then g else
      let lc := g.getLast!
      let k := g.length - 3
      -- subtract lc * x^k * (x^2 + a x + b)
      let sub := (List.replicate k 0) ++ [(lc * b) % p, (lc * a) % p, lc % p]
      let g' := addL p g (scal p (p - 1) sub)
      remQ p a b fuel g'

def noRoot (p : Nat) (f : List Nat) : Bool := (List.range p).all (fun a => evalL p a f != 0)

def noQuadFactor (p : Nat) (f : List Nat) : Bool :=
  (List.range p).all (fun a => (List.range p).all (fun b => (trim (remQ p a b (f.length + 1) f)).any (· != 0)))

def irred (p : Nat) (f : List Nat) : Bool :=
  match f.length - 1 with
  | 1 => true
  | 2 => noRoot p f
  | 3 => noRoot p f
  | 4 => noRoot p f && noQuadFactor p f
  | _ => false

/-- a row: prime p and the factorisation (monic factor, multiplicity) of g mod p -/
def rowOK (g : List Int) (n : Nat) (disc : Int) (row : Nat × List (List Nat × Nat)) : Bool :=
  let p := row.1
  let fs := row.2
  let gp : List Nat := g.map (fun c => (c % (p : Int)).toNat)
  (trim (prodL p fs) == trim gp)
  && fs.all (fun fe => irred p fe.1)
  && ((fs.map (fun fe => fe.2 * (fe.1.length - 1))).foldl (· + ·) 0 == n)
  && ((fs.any (fun fe => fe.2 > 1)) == (disc % (p : Int) == 0))

def Qi_g : List Int := [1, 0, 1]
def Qi_rows : List (Nat × List (List Nat × Nat)) := [(2, [([1, 1], 2)]), (3, [([1, 0, 1], 1)]), (5, [([2, 1], 1), ([3, 1], 1)]), (7, [([1, 0, 1], 1)]), (11, [([1, 0, 1], 1)]), (13, [([5, 1], 1), ([8, 1], 1)]), (17, [([4, 1], 1), ([13, 1], 1)]), (19, [([1, 0, 1], 1)]), (23, [([1, 0, 1], 1)]), (29, [([12, 1], 1), ([17, 1], 1)])]
/-- Qi: for every prime p < 30, g mod p = prod of irreducible factors^e, sum e f = 2, and
    (ramified, some e > 1) iff p | disc(g) = -4. -/
theorem Qi_bookkeeping : Qi_rows.all (rowOK Qi_g 2 (-4)) = true := by decide

def Qsqrt5_g : List Int := [-1, -1, 1]
def Qsqrt5_rows : List (Nat × List (List Nat × Nat)) := [(2, [([1, 1, 1], 1)]), (3, [([2, 2, 1], 1)]), (5, [([2, 1], 2)]), (7, [([6, 6, 1], 1)]), (11, [([3, 1], 1), ([7, 1], 1)]), (13, [([12, 12, 1], 1)]), (17, [([16, 16, 1], 1)]), (19, [([4, 1], 1), ([14, 1], 1)]), (23, [([22, 22, 1], 1)]), (29, [([5, 1], 1), ([23, 1], 1)])]
/-- Qsqrt5: for every prime p < 30, g mod p = prod of irreducible factors^e, sum e f = 2, and
    (ramified, some e > 1) iff p | disc(g) = 5. -/
theorem Qsqrt5_bookkeeping : Qsqrt5_rows.all (rowOK Qsqrt5_g 2 (5)) = true := by decide

def Qcbrt2_g : List Int := [-2, 0, 0, 1]
def Qcbrt2_rows : List (Nat × List (List Nat × Nat)) := [(2, [([0, 1], 3)]), (3, [([1, 1], 3)]), (5, [([2, 1], 1), ([4, 3, 1], 1)]), (7, [([5, 0, 0, 1], 1)]), (11, [([4, 1], 1), ([5, 7, 1], 1)]), (13, [([11, 0, 0, 1], 1)]), (17, [([9, 1], 1), ([13, 8, 1], 1)]), (19, [([17, 0, 0, 1], 1)]), (23, [([7, 1], 1), ([3, 16, 1], 1)]), (29, [([3, 1], 1), ([9, 26, 1], 1)])]
/-- Qcbrt2: for every prime p < 30, g mod p = prod of irreducible factors^e, sum e f = 3, and
    (ramified, some e > 1) iff p | disc(g) = -108. -/
theorem Qcbrt2_bookkeeping : Qcbrt2_rows.all (rowOK Qcbrt2_g 3 (-108)) = true := by decide

def Qzeta5_g : List Int := [1, 1, 1, 1, 1]
def Qzeta5_rows : List (Nat × List (List Nat × Nat)) := [(2, [([1, 1, 1, 1, 1], 1)]), (3, [([1, 1, 1, 1, 1], 1)]), (5, [([4, 1], 4)]), (7, [([1, 1, 1, 1, 1], 1)]), (11, [([2, 1], 1), ([6, 1], 1), ([7, 1], 1), ([8, 1], 1)]), (13, [([1, 1, 1, 1, 1], 1)]), (17, [([1, 1, 1, 1, 1], 1)]), (19, [([1, 5, 1], 1), ([1, 15, 1], 1)]), (23, [([1, 1, 1, 1, 1], 1)]), (29, [([1, 6, 1], 1), ([1, 24, 1], 1)])]
/-- Qzeta5: for every prime p < 30, g mod p = prod of irreducible factors^e, sum e f = 4, and
    (ramified, some e > 1) iff p | disc(g) = 125. -/
theorem Qzeta5_bookkeeping : Qzeta5_rows.all (rowOK Qzeta5_g 4 (125)) = true := by decide

/-- negative control: a FALSE row (Q(i) at p = 5 claimed inert) is rejected -/
theorem negctrl_Qi_5_not_inert : rowOK Qi_g 2 (-4) (5, [([1, 0, 1], 1)]) = false := by decide
