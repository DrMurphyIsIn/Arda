# Emit the Lean instance section (log bounds, per-entry facts, certificate data, final theorems)
# for a certificate JSON produced by cert_fast.py / cert_gen.py.
import json, sys, math
from fractions import Fraction as Fr
from logbounds import compute as log_compute, factor, L2LO, L2HI, DEN
from emit_lean import tree_literal

def frac_lean(x: Fr) -> str:
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"

def log_lemmas(primes_needed):
    lo, hi, rec = log_compute()
    out = []
    out.append(f"""/-- `log 2` from Mathlib's `Real.log_two_gt_d9`, `Real.log_two_lt_d9`. -/
lemma log2_bounds : {frac_lean(L2LO)} < Real.log 2 ∧ Real.log 2 < {frac_lean(L2HI)} := by
  constructor
  · have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  · have := Real.log_two_lt_d9; norm_num at this ⊢; linarith""")
    for p in primes_needed:
        if p == 2: continue
        r = rec[p]; m = r['m']; K = r['K']; fac = sorted(r['fac'].items())
        prod = " * ".join(f"(({q} : ℝ) ^ {e})" for q, e in fac)
        nmul = len(fac) - 1
        rws = ", ".join(["Real.log_mul (by positivity) (by positivity)"] * nmul + ["Real.log_pow"] * len(fac))
        rhs = " + ".join(f"{e} * Real.log {q}" for q, e in fac)
        haves = "\n".join(f"  obtain ⟨a{q}, b{q}⟩ := log{q}_bounds" for q, _ in fac)
        out.append(f"""lemma log{p}_bounds : {frac_lean(lo[p])} < Real.log {p} ∧ Real.log {p} < {frac_lean(hi[p])} := by
{haves}
  have hm : Real.log ({m} : ℝ) = {rhs} := by
    rw [show ({m} : ℝ) = {prod} by norm_num, {rws}]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / {m})
    (by rw [abs_of_pos (by norm_num)]; norm_num) {K}
  have h1 : Real.log (1 - (1 : ℝ) / {m}) = Real.log {p} - Real.log {m} := by
    rw [show (1 : ℝ) - 1 / {m} = {p} / {m} by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / {m} by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith""")
    return "\n\n".join(out), lo, hi

def emit_instance(cert, tag):
    N = cert['N']; H = cert['H']; S = cert['S']; Lam = cert['Lam']; Wmax = cert['Wmax']
    Lp = Fr(cert['Lp'][0], cert['Lp'][1])
    h = 2 * Lp / N; q = h / H
    depth = max(1, math.ceil(math.log2(N)))
    primes = sorted(set(d['p'] for d in cert['ds']))
    logtxt, lo, hi = log_lemmas(primes)
    parts = [logtxt]
    # data
    parts.append(f"""/-- Integer weight tree ({N} cells of width {h}, depth {depth}; leaves past {N} are padding). -/
def {tag}Tree : WTree :=
  {tree_literal(cert['w'], depth)}""")
    items = ",\n    ".join(f"({d['n']}, {d['C']}, {d['A']}, {d['B']})" for d in cert['ds'])
    parts.append(f"""/-- Shift data `(n, C, A, B)`: `log n ∈ [A q, B q]`, `Λ(n)/√n ≤ C / S`, all prime powers `n < 100`. -/
def {tag}Shifts : List (ℕ × ℕ × ℕ × ℕ) :=
  [{items}]""")
    parts.append(f"""/-- The kernel evaluates the whole integer Schur test ({N} rows x {len(cert['ds'])} shifts x 2 sides). -/
theorem {tag}_check : checkRows (WTree.get {depth} {tag}Tree) {N} {H} {Lam} {Wmax} {tag}Shifts {N} = true := by
  decide +kernel""")
    # entries
    ent = []
    for i, d in enumerate(cert['ds']):
        n, p, k, A, B, C = d['n'], d['p'], d['k'], d['A'], d['B'], d['C']
        s = Fr(d['s'][0], d['s'][1])
        ent.append(f"""lemma {tag}_entry_{n} : EntryOK {frac_lean(q)} {frac_lean(Fr(S))} ({n}, {C}, {A}, {B}) :=
  entryOK_of (p := {p}) (k := {k}) (lo := {frac_lean(lo[p])}) (hi := {frac_lean(hi[p])}) (s := {frac_lean(s)})
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log{p}_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)""")
    parts.append("\n\n".join(ent))
    conj = ",\n    ".join(f"{tag}_entry_{d['n']}" for d in cert['ds'])
    parts.append(f"""lemma {tag}_entries : ∀ e ∈ {tag}Shifts, EntryOK {frac_lean(q)} {frac_lean(Fr(S))} e := by
  have hall : List.Forall (EntryOK {frac_lean(q)} {frac_lean(Fr(S))}) {tag}Shifts :=
    ⟨{conj}⟩
  exact List.forall_iff_forall_mem.mp hall""")
    return "\n\n".join(parts), dict(N=N, H=H, S=S, Lam=Lam, Wmax=Wmax, depth=depth, h=h, q=q, Lp=Lp)

if __name__ == "__main__":
    cert = json.load(open(sys.argv[1]))
    txt, meta = emit_instance(cert, sys.argv[2])
    print(txt)
