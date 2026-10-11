# Stage S7c notes: hypothesis-free CC Thm 4.7 (the (85) bridge) (2026-10-11)

Branch `mm/arch-s7c` (base `mm/archimedean-rung` 4f761c6e8, all of S1-S10, S7b merged), island
`telperion/examples/rvm_bridge/lean` (Lean v4.33.0-rc2).  Modules `ArchS7c_*`, guard `ArchS7c_Guard.lean`.
Source: Connes-Consani arXiv:2006.13771 ("CC"), (43)/(85), Prop 2.2(iii), Thm 4.7.
`conjecture1_proved = False`.  Nothing here is RH progress.  No registry nodes touched.

## 0. What is missing

`ArchS7.thm47_weil'` has one analytic hypothesis left (S7 O1):

```lean
h85 : HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P (theta g _ (e k)))‖ ^ 2) (archW g + Dfun g)
```

S7's notes call this "S3's stopped M2".  That is outdated: S3 proved
`Lfun_eq_integral_Nnorm : archW g + Dfun g = (1/2π) ∫ hsq g r · Nnorm r dr`, with
`Nnorm r = ∫₁^∞ |Φ_r(a)|² da/a` and `Φ_r(a) = lim_R ∫_a^R s^{-1/2+ir} 2cos(2πs) ds`.
The missing piece is the bridge: the Hilbert-Schmidt sum on the left equals S3's Mellin-diagonal integral.
The O4 data hypotheses (D, σ, hDlam, hDphi, hτ) are discharged by S6 (`exists_prolateData`,
`summable_abs_tau`).

## 1. Statement check (h85 is true as stated)

Normalisation: Mathlib's full-line inner product on `evenL2`, `θ(x) f (v) = e^{-x/2} f(e^{-x} v)`,
`ϑ(g) = ∫ g(x) θ(x) dx`, `paperFT g r = ∫ g(u) e^{iru} du`, `hsq = |paperFT|²`.
`‖P̂ P y‖ = ‖F P̂ P y‖ = ‖P F P y‖` (F unitary, `F P̂ = P F`), so the sum is ‖P F P ϑ(g)‖²_HS.
No change of statement is needed (numerical check §3).

## 2. Route (no Mellin unitary, no distributions)

Kernel.  For w, u ∈ ℝ:

```
M(w,u) = ∫ g(x) e^{x/2} 1{e^x |u| > 1} cos(2π e^x u w) dx          (even in u and in w)
```

* **(R) Row identity.**  For every y ∈ L²(ℝ)_ev, a.e. in w:
  `(P F P ϑ(g) y)(w) = 1{|w|>1} ∫ M(w,u) y(u) du`.
  First for integrable y: (ϑ(g)y)(v) = ∫ g(x) e^{-x/2} y(e^{-x}v) dx a.e. (weak form against smooth compactly
  supported tests, `ae_eq_of_integral_contDiff_smul_eq`), which is integrable; then S6 `fourier_ae_eq`, two
  Fubinis and v = e^x u; evenness of y turns e^{-2πi…} into cos.  Then all y by truncation
  y_n = 1_{[-n,n]} y and an a.e.-convergent subsequence, since M(w,·) ∈ L² for |w| > 1.
* **(P) Per-w Plancherel.**  With s = log|u|, M(w,u) = |u|^{-1/2} H_w(log|u|),
  `H_w(s) = ∫ g(x) c_w(x+s) dx`, `c_w(t) = 1{t>0} e^{t/2} cos(2π w e^t)`.
  * decay: H_w(s) = 0 for s ≤ −L, |H_w(s)| ≤ K e^{-|s|/2} (one integration by parts in x for s > L,
    using g ∈ C¹ with compact support).  So H_w ∈ L¹ ∩ L² and M(w,·) ∈ L².
  * Fourier: ∫ H_w(s) e^{irs} ds = paperFT g (−r) · w^{-1/2-ir} Φ_r(w)/2.  Proof: truncate s ≤ T, Fubini,
    shift t = x+s, so the inner integral is ∫₀^{T+x} c_w(t) e^{irt} dt = w^{-1/2-ir}/2 · ∫_w^{w e^{T+x}} pD r 0;
    this is bounded by 2K_r w^{-1/2} and tends to w^{-1/2-ir}Φ_r(w)/2 (S3 `tendsto_integral_Phi`); dominated
    convergence in x.  No damping ε is needed.
  * Plancherel on L¹ ∩ L² (Mathlib isometry + S6 `fourier_ae_eq`):
    ∫ |H_w|² = (1/2π) ∫ hsq g (−r) |Φ_r(w)|²/(4w) dr, hence
    `∫_ℝ |M(w,u)|² du = (1/4π) ∫ hsq g (−r) |Φ_r(w)|² / w dr`.
* **(HS) Assembly.**  Σ_k ‖P F P ϑ(g) e_k‖² = ∫_{|w|>1} Σ_k |⟨conj M(w,·), e_k⟩|² dw (Tonelli,
  basis countable since L²(ℝ)_ev is separable) = ∫_{|w|>1} ‖M(w,·)‖² dw (Parseval, conj M(w,·) ∈ L²(ℝ)_ev)
  = 2 ∫_{w>1} (1/4π) ∫ hsq(−r)|Φ_r(w)|²/w dr dw = (1/2π) ∫ hsq(−r) Nnorm(r) dr (Tonelli)
  = (1/2π) ∫ hsq(r) Nnorm(r) dr (Nnorm even, via `ell_eq_Nnorm`, `psiR_neg`) = archW g + Dfun g.

## 3. Numerical checks (before formalising)

`telperion/research/arch_rung/s7c_check.py` [N-here, float64 + mpmath, NOT certified], with the complex test
function g(x) = e^{-4x²}(1 + 0.3x)e^{ix/2} (complex, so sign conventions in r are tested):

| identity | parameters | left | right |
|---|---|---|---|
| PhiE closed form vs quadrature | r = 0.7, ε = 0.5, a = 1.3 | −0.1395083628 − 0.0267238883i | −0.1395083631 − 0.0267238881i |
| (R) F P ϑ(g) y (w) = ∫ M(w,u) y(u) du, y = e^{-u²} | w = 1.2 | −0.0700147090 − 0.0073946476i | −0.0700147941 − 0.0073945700i |
| same | w = 2.0 | 0.0065750411 + 0.0000566907i | 0.0065748173 + 0.0000569580i |
| Ĥ_w(r) = paperFT g(−r) w^{-1/2-ir} Φ^ε_r(w)/2 (damped) | w = 1.5, ε = 0.5, r = 1.3 | −0.005724664 + 0.005441277i | −0.005726675 + 0.005441337i |
| same | w = 1.2, ε = 0.3, r = −2.1 | −0.051170316 + 0.004408509i | −0.051169690 + 0.004408570i |
| (P) ∫\|M^ε(w,·)\|² = (1/4π)∫hsq\|Φ^ε_r(w)\|²/w | w = 1.5, ε = 0.5 | 0.0002209472 | 0.0002209547 |
| same | w = 1.2, ε = 0.3 | 0.0098357193 | 0.0098354770 |

The damped versions (ε > 0) are exact for every ε by the same Fubini; they test the constants 1/2, 1/4π and
the sign r ↦ −r with fast-converging integrals.  Agreement is at the trapezoid-rule level (1e-4 relative).

## 4. Milestones

(filled in as they land)

## 5. Lean footguns

(filled in as they are met)
