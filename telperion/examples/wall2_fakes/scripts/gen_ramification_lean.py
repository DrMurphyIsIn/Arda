"""(4) Kernel-checkable bookkeeping for thmN_gap/corollary_fix.md section 4.  conjecture1_proved = False.

For K = Q(i), Q(sqrt5), Q(cbrt2), Q(zeta5), with monogenic generators g whose Z[alpha] = O_K, and every prime
p < 30, this script factors g mod p with sympy and emits a CORE-Lean file (no Mathlib, no lake; Nat arithmetic
mod p).  For each (K, p) it states a record (p, factors with multiplicities e and degrees f), and `decide` checks:
  (1) the product of factor^e equals g mod p, as coefficient lists;
  (2) each factor is irreducible mod p: degree 1 is trivial; degrees 2 and 3 have no root mod p; degree 4 has
      no root and no monic quadratic factor (remainder of g by every x^2 + a x + b is nonzero);
  (3) sum e*f = n = [K:Q];
  (4) (some e > 1) <-> p | disc(g), with disc(g) = d_K here.
What the kernel does NOT check: Dedekind-Kummer (factorisation type of g mod p = splitting of p, valid because
Z[alpha] = O_K, i.e. p does not divide the index), and disc(g) = d_K.  Those are CITED (standard).  So the kernel
facts are the polynomial arithmetic; the reading "e(P|p), f(P|p)" is via the cited theorem.
"""
import os
import sympy as sp

x = sp.symbols("x")
FIELDS = {
    "Qi": (x**2 + 1, -4),
    "Qsqrt5": (x**2 - x - 1, 5),
    "Qcbrt2": (x**3 - 2, -108),
    "Qzeta5": (x**4 + x**3 + x**2 + x + 1, 125),
}
PRIMES = list(sp.primerange(2, 30))


def coeffs(poly, p):  # low-to-high, mod p
    c = sp.Poly(poly, x).all_coeffs()[::-1]
    return [int(v) % p for v in c]


rows = {}
for name, (g, disc) in FIELDS.items():
    n = sp.degree(g, x)
    assert sp.discriminant(g, x) == disc
    rows[name] = []
    for p in PRIMES:
        _, facs = sp.Poly(g, x, modulus=p).factor_list()
        fl = [([int(v) % p for v in f.all_coeffs()[::-1]], e) for f, e in facs]
        # normalise to monic low-to-high
        fl2 = []
        for c, e in fl:
            inv = pow(c[-1], -1, p)
            fl2.append(([(v * inv) % p for v in c], e))
        ram = any(e > 1 for _, e in fl2)
        assert ram == (disc % p == 0), (name, p)
        assert sum(e * (len(c) - 1) for c, e in fl2) == n
        rows[name].append((p, fl2))

L = []
L.append("""/- WALL-2 / T: ramification bookkeeping for corollary_fix.md section 4 (generated; do not edit).
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
""")
for name, (g, disc) in FIELDS.items():
    n = sp.degree(g, x)
    gl = [int(v) for v in sp.Poly(g, x).all_coeffs()[::-1]]
    rl = ", ".join("(%d, [%s])" % (p, ", ".join("([%s], %d)" % (", ".join(map(str, c)), e) for c, e in fl))
                   for p, fl in rows[name])
    L.append(f"""
def {name}_g : List Int := {gl}
def {name}_rows : List (Nat × List (List Nat × Nat)) := [{rl}]
/-- {name}: for every prime p < 30, g mod p = prod of irreducible factors^e, sum e f = {n}, and
    (ramified, some e > 1) iff p | disc(g) = {disc}. -/
theorem {name}_bookkeeping : {name}_rows.all (rowOK {name}_g {n} ({disc})) = true := by decide
""")
L.append("""
/-- negative control: a FALSE row (Q(i) at p = 5 claimed inert) is rejected -/
theorem negctrl_Qi_5_not_inert : rowOK Qi_g 2 (-4) (5, [([1, 0, 1], 1)]) = false := by decide
""")
out = os.path.expanduser("~/rh-team/wall2/T/lean/Ramification.lean")
os.makedirs(os.path.dirname(out), exist_ok=True)
open(out, "w").write("".join(L))
for name in rows:
    print(name, [(p, [(len(c) - 1, e) for c, e in fl]) for p, fl in rows[name]])
print("wrote", out)
