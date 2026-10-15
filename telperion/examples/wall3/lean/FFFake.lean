/- WALL-3 / T: kernel check of finite facts about track E's function-field fake (E/e3_ff_fake.py, fe.md sec 3.3).
   Core Lean only (no Mathlib).  conjecture1_proved = False.
   P(T) = 1 - 2T + 9T^2 - 6T^3 + 9T^4, q = 3.  Kernel-checked by `decide`:
     * the FE coefficient relations c4 = q^2 c0 and c3 = q c1;
     * with power sums p_m of the inverse roots (Newton's identities, exact Int recurrence), N_m = q^m + 1 - p_m and
       d * n_d = sum_{e | d} mu(d/e) N_e, the place counts n_d for d = 1..12 are the listed non-negative integers
       (and d divides the Mobius sum).
   NOT checked here: that the Newton recurrence gives the power sums of P's inverse roots (standard algebra), the root
   moduli (Arb, certs/E_ff_fake.cert.json), and n_d >= 0 for d > 12 (exact Python to 1500 + elementary tail bound). -/

def c : List Int := [1, -2, 9, -6, 9]
def q : Int := 3

theorem fe_rel : c[4]! = q * q * c[0]! ∧ c[3]! = q * c[1]! := by decide

/-- e_k = (-1)^k c_k: elementary symmetric functions of the inverse roots. -/
def e (k : Nat) : Int := if k % 2 = 0 then c[k]! else -c[k]!

/-- Newton: p_m = sum_{k=1}^{min m 4} (-1)^(k-1) e_k p_{m-k}  (and the k = m term is (-1)^(m-1) m e_m). -/
def psums : Nat → List Int
  | 0 => [4]
  | m + 1 =>
    let prev := psums m
    let n := m + 1
    let get (j : Nat) : Int := prev[j]!
    let term (k : Nat) : Int :=
      let sgn : Int := if (k - 1) % 2 = 0 then 1 else -1
      if k < n then sgn * e k * get (n - k) else if k = n then sgn * (n : Int) * e k else 0
    prev ++ [term 1 + term 2 + term 3 + term 4]

def N (m : Nat) : Int := q ^ m + 1 - (psums m)[m]!

def mu : Nat → Int
  | 1 => 1 | 2 => -1 | 3 => -1 | 4 => 0 | 5 => -1 | 6 => 1 | 7 => -1 | 8 => 0 | 9 => 0 | 10 => 1 | 11 => -1 | 12 => 0
  | _ => 0

def msum (d : Nat) : Int :=
  ((List.range (d + 1)).filter (fun e => e ≥ 1 ∧ d % e = 0)).foldl (fun acc e => acc + mu (d / e) * N e) 0

def placeCounts : List Int := [2, 11, 18, 3, 0, 104, 540, 1116, 1344, 3216, 17388, 61163]

theorem place_counts_ok :
    (List.range 12).all (fun i => msum (i + 1) = ((i + 1 : Nat) : Int) * placeCounts[i]!) = true := by decide

theorem place_counts_nonneg : placeCounts.all (fun x => decide (0 ≤ x)) = true := by decide

theorem N1_N2 : N 1 = 2 ∧ N 2 = 24 := by decide
