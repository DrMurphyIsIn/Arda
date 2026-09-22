# The Weil-to-Li dictionary on the rvm_bridge island: B7 convergence half PROVED, value half named (2026-09-21)

Status. `E6Bridge15.lean` (namespace `RvMBridge15`, imports E6Bridge6) proves, kernel-checked with
axioms exactly `[propext, Classical.choice, Quot.sound]` and no `sorry`:

- **the convergence half of the open node `RH_bl_explicit_formula` (B7)**: for every n the
  symmetric window sums of Li's kernel over the nontrivial zeros converge,
  `liZeroSum_tendsto (n) : Tendsto (liZeroSum n) atTop (nhds (liLimit n))`, and are real;
- **the node verbatim modulo ONE named obligation** `LiValue n` (the Bombieri-Lagarias value of
  the limit), `bl_explicit_formula_of (hn : 0 < n) (h : LiValue n)`;
- **the forward half of Li's criterion** on this island's vocabulary:
  `rh_implies_liLimit_re_nonneg : RiemannHypothesis -> 0 <= Re (liLimit n)` and the window form.

conjecture1_proved = False. Nothing here bears on whether RH holds; the converse of Li's criterion
is not on this island and is not claimed.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge15.lean` (493 lines; `lake env lean` clean)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge15_probe.lean` (axiom audit, all green)
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge15_obligation_probe.lean` (expected FAILS)
- this memo

Not touched: lakefile.toml, AxiomGuardRvMBridge.lean, every existing module. The olean was emitted
by hand (`lake env lean -o .lake/build/lib/lean/E6Bridge15.olean ...`) for the probe run; the
integrator wires `E6Bridge15` as a `lean_lib` in defaultTargets and adds the guard lines below.

## Vocabulary

The `BombieriLagarias` block of `missions/rh/lean/Statements/RHDefs.lean` is mirrored verbatim as
`RvMBridge15.BombieriLagarias` (liKernel, liZeroSum, archSide, zetaLogDerivReg, eta, finiteSide;
only Mathlib names). The node is

```lean
theorem bl_explicit_formula (n : ℕ) (hn : 0 < n) :
    Tendsto (BombieriLagarias.liZeroSum n) atTop
      (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n))
```

## What is proved and how

Write m = `WeilExplicit.zeroMult` (the E8 divisor), K_n(rho) = 1 - (1 - 1/rho)^n, and
W_T = {0 < Re rho < 1, |Im rho| <= T}. The unpaired family m(rho) K_n(rho) is NOT summable
(terms ~ n/(i gamma), and Sum 1/gamma diverges); the design memo's "symmetric order is forced"
is realised as follows.

1. `zeroMult_conj : m(conj rho) = m(rho)` for every rho : C. On the strip m is
   `(analyticOrderAt riemannZeta rho).toNat` (E6Bridge4.zeroMult_eq_of_strip) and Zeta23 has
   `analyticOrderAt_zeta_conj`; off the nontrivial zeros both sides vanish (Mathlib's
   `riemannZeta_conj` moves the zero condition across conj).
2. `liZeroSum_eq_tsum_indicator`: the finsum is a tsum of the indicator family (support finite by
   Zeta23 `zetaSeam.finite_window`).
3. `liZeroSum_eq_tsum_paired` (THE PAIRING): W_T is conjugation-closed and K_n(conj rho) =
   conj K_n(rho), so reindexing the tsum by `conjEquiv` gives Sum = conj Sum, hence
   Sum = Sum of m(rho) Re K_n(rho) =: Sum of `liPaired n`. Corollary `liZeroSum_im = 0`.
4. `abs_re_liKernel_le`: on 0 < Re rho < 1 with |rho| >= 1, |Re K_n(rho)| <= 2^n / |rho|^2. Binomial
   expansion K_n = -Sum_{m<n} C(n,m+1) (-1/rho)^{m+1}; the m = 0 term has real part
   -Re rho / |rho|^2 (this is where the pairing pays: the unpaired term is n/(i t)), the others are
   bounded by |rho|^{-(m+1)} <= |rho|^{-2}; Sum C(n,m+1) <= 2^n.
5. `norm_liPaired_le_majorant`: on a nontrivial zero with |Im rho| >= 1,
   ||liPaired n rho|| <= m(rho) (9/4) 2^n / (1 + |gamma_rho|^2), the local-count majorant of
   E6Bridge6 (`summable_mult_div_one_add_normSq`, i.e. Zeta23 `zero_sum_inv_sq`). The finitely many
   zeros with |Im rho| < 1 are absorbed into the majorant `liBound` as an indicator.
6. `summable_liPaired`, then Tannery (`tendsto_tsum_of_dominated_convergence`) for the indicator
   family: `liZeroSum_tendsto`. No hypothesis on n (at n = 0 the limit is 0).
7. Li's forward computation: on the line |1 - 1/rho| = |rho - 1|/|rho| = 1
   (`norm_one_sub_inv_of_on_line`), so Re K_n = 1 - Re w^n >= 0 with |w| = 1, and all paired terms
   are >= 0: `rh_implies_liZeroSum_re_nonneg`, `rh_implies_liLimit_re_nonneg`.

## The one obligation (value half), where it stopped and why

```lean
def LiValue (n : ℕ) : Prop := liLimit n = BombieriLagarias.archSide n + finiteSide n
theorem bl_explicit_formula_of {n : ℕ} (_hn : 0 < n) (h : LiValue n) :
    Tendsto (liZeroSum n) atTop (𝓝 (BombieriLagarias.archSide n + finiteSide n))
```

`liLimit n = Sum'_rho m(rho) Re (1 - (1 - 1/rho)^n)` is an honest absolutely convergent sum, so
LiValue n is a genuine identity between two complex numbers (not a statement about a junk tsum).
It is FALSE at n = 0 (`probe_liValue_zero_false`: 0 vs 1), exactly the node's reason for 0 < n.
Its content is Bombieri-Lagarias 1999 Theorem 2: the symmetric power sums Sum_rho rho^{-j}
(j = 1..n) expressed through the Laurent coefficients eta_{j-1} of -zeta'/zeta - 1/(s-1) at s = 1
and the digamma tower psi^{(k)}(1/2) (the zeta(j)(1 - 2^{-j}) terms). That needs the Hadamard
product / global xi'/xi partial fraction with the constant pinned (Sum_rho [1/(s-rho) + 1/rho] =
xi'/xi(s) - xi'/xi(0)). Zeta23's partial fraction (`WeilEF.zeta_logDeriv_partial_fraction`) is
Landau's LOCAL form (finitely many zeros near height t, O(log t) remainder, only for |t| >= 6): it
gives the local count the convergence half consumes, but not the global constant the value half
needs. Mathlib has neither the Hadamard factorisation of xi nor polygamma values at 1/2. A finer
split (a) power sums = xi'/xi Taylor data at 0, (b) that data = archSide + finiteSide via
Gamma-function Taylor coefficients, would be TWO obligations; both unproved, so LiValue is kept as
the single honest name. The lead's suggested route through the E8 contour with the rational kernel
(corridor bound on horizontal edges) is the natural proof of (a) and is NOT started here.

The expected-failure probe shows simp/aesop/norm_num neither prove nor refute LiValue 1 and that
the convergence theorem alone does not yield the node.

## Probe output (lake env lean Probes/E6Bridge15_probe.lean)

```
'RvMBridge15.liZeroSum_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.zeroMult_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.liZeroSum_eq_tsum_paired' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.liZeroSum_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.abs_re_liKernel_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.summable_liPaired' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.bl_explicit_formula_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.rh_implies_liZeroSum_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge15.rh_implies_liLimit_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_liValue_zero_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Lines for AxiomGuardRvMBridge (integrator)

```lean
#print axioms RvMBridge15.liZeroSum_tendsto
#print axioms RvMBridge15.zeroMult_conj
#print axioms RvMBridge15.liZeroSum_eq_tsum_paired
#print axioms RvMBridge15.summable_liPaired
#print axioms RvMBridge15.bl_explicit_formula_of
#print axioms RvMBridge15.rh_implies_liLimit_re_nonneg
```

## Deliverable (B) status

The "Li positivity <-> Gaussian positivity through RH" equivalence needs Li's criterion converse,
which lives on the v4.34 li_positivity island and cannot be imported here; not claimed. The
finite-grade content delivered instead: the window sums are the E8 zero-side functional
`Sum m(rho) H(gamma_rho)` for the entire H(gamma) = Re K_n(1/2 + i gamma) restricted to windows,
real for every window, nonnegative under RH, convergent unconditionally.

## Pin footguns hit

- `riemannZeta_conj` is ambiguous (Mathlib's `_root_` version, all s, vs Zeta23's with s ≠ 1).
- `archSide` is ambiguous with `WeilExplicit.archSide` once both namespaces are open.
- `finsum_mem_inter_support` runs support -> plain; use `←`.
- `tsum_add` is `Summable.tsum_add` on this pin.
- Set-membership hypotheses of the form `ρ ∈ {ρ | P ρ}` need `show`/`change` before `abs_le.mp`,
  and anonymous constructors for memberships need the set spelled out (`show ρ ∈ S from ⟨..⟩`).
- `positivity` does not see `0 < 1 + normSq z`; use `linarith [Complex.normSq_nonneg z]`.

## Obligation probe output (lake env lean Probes/E6Bridge15_obligation_probe.lean), all EXPECTED

```
Probes/E6Bridge15_obligation_probe.lean:10:23: error: unsolved goals          (LiValue 1 by simp)
Probes/E6Bridge15_obligation_probe.lean:18:2: warning: aesop: failed to prove the goal after exhaustive search.
Probes/E6Bridge15_obligation_probe.lean:16:44: error: unsolved goals          (LiValue n by aesop)
Probes/E6Bridge15_obligation_probe.lean:21:25: error: unsolved goals          (not LiValue 1 by simp)
Probes/E6Bridge15_obligation_probe.lean:26:25: error: unsolved goals          (not LiValue 1 by norm_num)
Probes/E6Bridge15_obligation_probe.lean:35:2: error: Type mismatch            (node from convergence alone)
```
