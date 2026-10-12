# Archimedean Weil positivity: a conceptual (Connes–Consani) proof blueprint (2026-10-11)

**Status.**
* Branch `mm/archimedean-rung`, island `telperion/examples/rvm_bridge/lean`.  The Lean toolchain there is v4.33.0-rc2.
* `conjecture1_proved = False`.  Nothing here is RH progress.
* **Labels.**  **[P-lit]** is proved in the literature.  **[N-CC]** is floating-point numerics in CC.  **[N-here]** is reproduced in this session in float64 or mpmath; it is NOT certified and NOT kernel-checked.  **[C]** is a claim of this blueprint that is not yet verified.
* **Scripts** (all [N-here], all in `telperion/research/arch_rung/`):
  * `prolate_cc.py`: the prolates, ε, and the spectrum of K_I.
  * `delta_route.py`: the δ route.
  * `ell_check.py`: 2θ' + δ̂.
  * `polefree_numerics.py` and `arb_polefree_check.py`: margins.
* **Sources read in full** (PDF text):
  * Connes–Consani, arXiv:2006.13771 ("CC").
  * Connes' 2026 survey, arXiv:2602.04022: §4.1 and §7.2.  It contains no simplification of the archimedean proof.  It restates CC Thm 1 with both vanishing conditions and calls Yoshida's proof "a numerical analysis".
  * `~/rh-team/B/connes_consani_reading.md`.
* **Not accessed:** Yoshida (1992), Adv. Stud. Pure Math. 21, 281-325.  It is known only through CC p. 2 and the survey §4.1.

## 0. Headline

1. **The goal statement is already kernel-proved, by different means.**
   * `KWin_Bridge.weil_positivity_prime_free_window` covers the full `IsWeilTest` class with the pole terms kept, for 2L ≤ log 2.
   * `KWin2_BridgeHeavy` extends this to 2L ≤ 1, with the p = 2 term.
   * Both are certificates: a Zhu frequency split, a piecewise-polynomial psiR minorant, and LDLᵀ by `decide +kernel`.
   * The pole-free statement is a one-line corollary.  KWin's conclusion already holds for every IsWeilTest g, and the pole-free g are a subset.
   * A conceptual proof would therefore **reprove a special case**.  Its value is structural: the decomposition W∞ = (Sonin trace) − (remainder), which CC propose to carry to the semilocal case.
2. **CC's conceptual argument proves a different class from the Lean statement.**
   * The Lean pole-free hypothesis is one condition, `paperFT g (I/2) = 0`, i.e. ∫ g(u) e^{−u/2} du = 0.  That is Yoshida's class: CC p. 2, "Fourier transform vanishes at ±i/2" for f = g∗g*.
   * **CC Thm 1 needs a second condition, ĝ(0) = 0**, which is ∫ g = 0 in our variable.
   * Thm 6.11 drops it only at the cost of −c|ĝ(0)|², with c = 4γ/log 2.  Rem. 6.12 shows 13 < c < 17, so that term cannot be removed by their method.
   * So CC's conceptual proof does **not** give Yoshida's one-condition positivity on the full window.  CC credit that result to Yoshida's "explicit computation".
3. **Numbers in our conventions** [N-here], at L = (log 2)/2:

   | class | λ_min of Q/‖g‖² |
   |---|---|
   | one condition, the Lean statement | 0.07233 (arb: [0.07233354838 ± 4.9e-12]) |
   | CC Thm 1 class (∫g e^{−u/2} = 0 and ∫g = 0) | 0.54804 |
   | ∫g e^{±u/2} = 0 | 0.54705 |

   * The one-condition statement holds up to L = 0.37161.
   * The figure 0.547 in earlier project notes, and in the `KWin_*` header comments, is a two-condition number.  It is NOT the margin of the Lean pole-free class.
4. **What the CC machinery reaches, measured** [N-here, from a reproduction that matches CC to all published digits]:

   | route (CC section) | needs prolates? | window, our half-width L |
   |---|---|---|
   | δ route, crude L¹ (Cor 3.8) | no | 0.0488 |
   | δ route, exact spectrum, λ_max(K^δ_I) ≤ 2 | no | 0.0933 |
   | Sonin/ε route, one condition, λ_max(K_I) ≤ 1 | yes | **0.2791** |
   | Sonin/ε route + conditioning on ĝ(0) (Thm 1) | yes | (log 2)/2, CC class only |

   * The prolate-free part of CC does not even reach the existing L ≤ 1/10 (`weil_positivity_window_tenth`).
5. **Verdict: FEASIBLE ONLY WITH CERTIFIED NUMERICS, and only as a staged multi-month programme.**
   * The certified numerics are prolate eigen-data and one compact-operator spectrum (section 5).
   * The cheapest independently useful stages are 1 to 3, about 3 to 4k lines.
   * The full CC theorem in Lean is realistically **12 to 18k lines**, plus a certified prolate engine.
   * A faithful formalisation of CC's §6 is NOT practical.  Its Toeplitz / q → 1 apparatus is heuristic scaffolding with downloaded data and must be replaced (section 4).

## 1. CC's proof, step by step, classified

Notation as in CC:
* ϑ(λ)ξ(v) = λ^{−1/2}ξ(v/λ) on L²(ℝ)_ev, with ⟨η|ξ⟩ = ∫₀^∞ η̄ξ (16).
* F = F_{e_ℝ} has kernel e^{−2πixy}.
* P₁ is multiplication by 1_{[−1,1]}, and P̂₁ = F P₁ F.
* S is the projection on the Sonin space S(1,1) = {ξ even : ξ = 0 and Fξ = 0 on [−1, 1]}.
* Q = −(ρ∂_ρ)² + 1/4.
* I is the g-interval.  In additive variables it is [−a/2, a/2] with a = |I| ≤ log 2, so our L = a/2.

STRUCTURAL means pure analysis or algebra.  NUMERICAL means the step relies on a computed number.

| # | CC result | content | class | Lean difficulty / remarks |
|---|---|---|---|---|
| 1 | Lemmas 1.1, 1.3, 1.4; Prop 1.5 (local trace formula) | W_R(f) = ∫ f(ρ⁻¹)τ(ρ)d*ρ with τ(ρ) = ρ^{1/2}/2·(1/(1+ρ) + 1/\|1−ρ\|) as a principal value (39), = Tr(ϑ_m(f)·½(u*đu)^g).  Proof via Schwartz kernels, areas α(t), β(t) of \|xy ≤ t\| in two squares, and F(−log\|t\|) = 1/(2\|x\|). | STRUCTURAL | Very heavy: trace-class operators (absent from Mathlib), PV distributions, Fourier transform of log\|t\|.  **Bypassable** (stage 3): only Cor 2.3 is used downstream. |
| 2 | Prop 2.2, Cor 2.3 | δ(ρ) = 4ρ^{1/2}∫_Δ cos(2πρxy)cos(2πxy) (42), closed form via Si (49), δ(ρ⁻¹) = δ(ρ).  **L := W∞ + D ≥ 0** on positive-definite f, of any support: L(f) = Tr(ϑ_m(f) P P̂ P).  Equivalently ℓ(t) := 2θ'(t) + δ̂(t) ≥ 0 pointwise (52). | STRUCTURAL (positivity is "trace of a product of positives") | P P̂ P = A*A with A = (1−P)UP, so L(g∗g*) = ‖A T_g‖²_HS.  That is an L²-norm of an explicit oscillatory-kernel integral (section 2.4), which avoids trace class.  Slack [N-here]: min_t ℓ(t) = 0.04905 at t = 0, and ℓ(10) = 0.358 (matches CC Figs 3-4). |
| 3 | Lemma 3.3, Prop 3.5 | The vanishing conditions f̂(±i/2) = 0 are exactly the range of Q on C_c^∞(I), with support preserved.  Positivity of φ on C_c^∞(I) ∩ J ⇔ positivity of φ∘Q on C_c^∞(I). | STRUCTURAL | Easy.  Our form: g = h' − h/2 (section 2.3). |
| 4 | Thm 3.6, Rem 3.7 | D∘Q(ξ∗ξ*) = −2‖ξ‖² + ⟨ξ\|K^δ_I ξ⟩.  K^δ_I is Hilbert–Schmidt with kernel (Q₊δ)(e^{\|x−y\|}).  The −2 comes from the jump of δ' at ρ = 1 (−1 → +1). | STRUCTURAL | Moderate: Rem 3.7 is an elementary integration by parts. |
| 5 | Cor 3.8, Rem 3.9 | D∘Q ≤ 0 if ∫₀^s \|Q₊δ(e^x)\| ≤ 1, with s = 0.097542 (f-support; our L = s/2 = 0.0488).  The Boas–Kac refinement gives s = 0.14043. | NUMERICAL (one integral, needs precision 1e-3) | Easily certified (Si and its derivatives).  Window below what is already proved. |
| 6 | Lemma 4.1, (62)-(63) | δ(ρ) = Tr(ϑ(ρ⁻¹)P̂₁P₁) for ρ ≥ 1. | STRUCTURAL | Needs trace class, or the HS rewrite. |
| 7 | Lemma 4.2, Def 4.3 | Pairs of projections, i.e. unitary representations of ℤ/2∗ℤ/2: 2-dim irreducibles with angle α, P₁P₂P₁ = cos²α P₁. | STRUCTURAL | Halmos two-subspace theory is absent.  **Bypass**: P₁P̂₁P₁ is compact and self-adjoint (HS kernel), so Mathlib's spectral theorem gives the needed blocks directly. |
| 8 | (66)-(70) (Slepian–Pollak) | W = −∂(1−x²)∂ + (2πx)² commutes with P₁ and F.  Even prolates PS_{2n,0}(2π,·) satisfy ∫_{−1}^{1} PS e^{2πixω} = λ(n)PS(ω) (68).  P₁P̂₁P₁ has simple spectrum λ(n)² on ran P₁. | STRUCTURAL ([P-lit]) | Commutation is a computation (moderate).  **Simplicity** of the spectrum and **completeness** of the prolates need singular Sturm–Liouville theory, which is absent from Mathlib and hard. |
| 9 | (71), App. F (Rokhlin–Xiao Thm 14; Wang Thm 3.6, (100)) | \|λ(n)\| ≤ 2^{2n}π^{2n+1/2}((2n)!)²/((4n)!Γ(2n+3/2)); \|ξ_n(1)\| ≤ √(2n+1/2); bounds on ‖D_uξ_n‖. | STRUCTURAL ([P-lit], external) | Hard to formalise as stated.  **Replacement**: a Taylor-rank bound σ_n(e^{2πixy}\|_{[−1,1]²}) ≤ 2(2π)^n/n! for the eigenvalue tail.  It is elementary (section 4). |
| 10 | Prop 4.5, Thm 4.7 | **Tr(ϑ(f)S) = W∞(f) + E(f)**, with E(f) = ∫f(ρ⁻¹)ε(ρ)d*ρ and ε(ρ) = Σ λ(n)/√(1−λ(n)²)·⟨ξ_n\|ϑ(ρ⁻¹)ζ_n⟩ (84).  The Sonin trace is ≥ 0 because S is a projection. | STRUCTURAL | The core identity.  Heavy (items 6-9). |
| 11 | Lemmas 5.1, 5.2; Prop 5.3 | Q acting on matrix coefficients, plus boundary terms at x = 1: (Qε)(ρ) = Σ λ²/(1−λ²)·C_n(ρ) (99). | STRUCTURAL | Moderate: calculus with boundary terms. |
| 12 | Lemma 5.4 | ε'(1⁺) = Σ λ²/(1−λ²)·ξ_n(1)², which is about 22.9965. | STRUCTURAL identity + NUMERICAL value | The value needs prolate eigen-data to about 1e-6. |
| 13 | Prop 5.5 | E∘Q(ξ∗ξ*) = ⟨ξ\|N_I ξ⟩ with N_I = −2ε'(1⁺)(Id − K_I).  K_I has HS kernel χ(y−x), χ(v) = (Qε)(e^{\|v\|})/(2ε'(1⁺)), valid for \|I\| ≤ log 2.  Tr K_I = 0 since Qε(1) = 0. | STRUCTURAL | Moderate. |
| 14 | §6.1-6.2 | q → 1 discretisation, Toeplitz T_q, roots of the top eigenvector on \|z\| = 1, angles α_j (109), weights d(j) (112). | NUMERICAL, heuristic only | **Not a proof step**: it is used to *guess* T.  Uses downloaded data (m = 1732 angles/weights).  Bypass entirely (section 4). |
| 15 | Fact 6.1, Lemma 6.3 | ‖K_I − T‖ ≤ ε₁ = 2∫₀^{log 2}\|τ − χ\| ≈ 0.00122 (115), where T is a 3465-term trigonometric finite-rank operator.  Lemma 6.3 (Young/Schur ‖·‖ ≤ L¹) is structural. | NUMERICAL ("computer calculation", floating point) | Needs certified χ, hence certified prolates for n ≤ 10, plus a certified L¹ norm.  Precision: ε₁ < ε₂ − margin, so absolute 1e-4 is enough. |
| 16 | Lemmas 6.2, 6.4, 6.6 | Poisson summation (6.2); the top eigenvector ψ = FT of h(z) = ∏(1 − z²/α_n²), supported in I (6.4); ‖ξ_α − P(n)ξ_α‖² via the trigamma function (6.6). | STRUCTURAL (given the α_n) | Moderate, but only serves the T-route.  Bypassed with item 14. |
| 17 | Fact 6.5; Lemma 6.8; (127) | ⟨ξ₀\|ζ⟩ ≈ 0.94865, λ_max(T) = 1.05158, λ₂ ≤ 0.772216 (via matrices N = 2000/10000, J ∈ [0.313, 1.346], ε'(N) ≈ 0.0074). | NUMERICAL | Replace with a certified Galerkin + tail for K_I directly (section 4). |
| 18 | Lemma 6.9 | A rank-one restoration criterion (2×2 matrix). | STRUCTURAL | Easy (`nlinarith` level). |
| 19 | Lemma 6.10, Thm 6.11, Thm 1 | With b = λ_max − 1 ≈ 0.05158, c = 1 − λ₂ > 0.2278, ⟨ζ\|ξ₀⟩ ≈ 0.94865 and a ≈ 0.064: ε₂ ≈ 0.00441 > ε₁, so N_I ≤ γ\|⟨ξ₀\|ξ⟩\|² with γ ≈ 2.94355.  Hence W∞ ≥ Tr(ϑSϑ*) − (4γ/log 2)\|ĝ(0)\|². | STRUCTURAL assembly of NUMERICAL inputs | The slack ε₂ − ε₁ ≈ 0.0032 is what certification must preserve. |

**Reproduction** [N-here] (`prolate_cc.py`).  It uses even prolates from the tridiagonal Legendre form of W, 80 terms and 14 prolates.

| quantity | here | CC |
|---|---|---|
| λ(0..5) | 0.9999714, −0.9794847, 0.5240859, −0.0589766, 0.0027323, −7.629e-5 | matches the values after (68) |
| Σλ(n)² | 2.237484835 | 2(Si(4π)/(4π) + 1) = 2.237484835 (Rem 4.6) |
| Σλ²ξ_n(1)² | 2.000000 | 2 (Rem 4.6) |
| ε'(1⁺) | 22.99648 | 22.9965, with t(0..4) identical |
| range of χ on [0, log 2] | [−1.70, 3.33] | Fig 10 |
| λ_max, λ₂, λ₃ of K_I at \|I\| = log 2 (Nyström, 600 nodes) | 1.05165, 0.68579, 0.03129 | 1.05158, 0.686494, 0.0288921 for their T, with ‖K_I − T‖ ≤ 0.00122 |
| λ_max(K_I) vs \|I\| = a | 0.6295 (0.30), 0.8384 (0.40), 0.9592 (0.50), 0.9952 (0.55), 1.0207 (0.60) | |
| crossing a* | **0.55827**, i.e. **L* = 0.2791** | |
| Schur/L¹ bound, 2∫₀^a\|χ\| ≤ 1 | a ≤ 0.2130 (L ≤ 0.1065) | |

**δ route without prolates** (`delta_route.py`): δ(1) = 2.2374848, δ'(1⁺) = 1.0000000 and κ = Q₊δ ∈ [−16.7, 14.6], matching CC Fig 8.  λ_max(K^δ_I) = 2 at \|I\| = 0.18662, i.e. L = 0.0933.  The crude L¹ bound gives L ≤ 0.0488, matching CC's s = 0.0975 = 2L.

**Why CC need the ĝ(0) condition (mechanism).**  K_I has exactly one eigenvalue above 1 at \|I\| = log 2.  Its eigenvector ζ has ⟨ζ\|ξ₀⟩ ≈ 0.949 with the constant ξ₀.  Under h ↦ g = h' − h/2, the constant direction of h corresponds to ĝ(0).  CC's route drops the Sonin trace (≥ 0) and keeps only −E, so it needs the extra condition to kill that direction.  Yoshida's one-condition statement is still true (margin 0.072).  Its positivity in the bad direction must then come from the Sonin trace, which CC never bound from below.

## 2. Translation into the project's conventions

### 2.1 Dictionary (checked against CC App. A/B and the reading note, item 1)

| CC | project |
|---|---|
| g ∈ C_c^∞(ℝ*_+) with the Δ^{1/2} twist (W∞(f) := W∞(Δ^{−1/2}f)); d*u = dx for x = log u | g_ours(x) = g_CC(e^x) ∈ C_c^∞(ℝ) = `IsWeilTest` (the class is equal; smoothness and compact support are preserved by exp/log) |
| supp g ⊂ [2^{−1/2}, 2^{1/2}] | tsupport g ⊆ [−L₀, L₀], L₀ = (log 2)/2 (closed interval: CC Thm 6.11) |
| ĝ(t) = ∫ g(u)u^{−it}d*u | ĝ_CC(t) = paperFT g (−t) |
| ĝ(i/2) = 0 (kills both f̂(±i/2) = pole terms) | `paperFT g (I/2) = 0` ⇔ ∫ g e^{−u/2} = 0 (E6Bridge31 `poles_vanish`).  CC Thm 6.11 writes it at −i/2.  By u ↦ −u symmetry of the form the two are equivalent, but they are different subspaces. |
| ĝ(0) = 0 (CC Thm 1 only) | `paperFT g 0 = 0` ⇔ ∫ g = 0 |
| f = g∗g*, f̂ = \|ĝ\|² | `autocorr g`, `paperFT (autocorr g) r = hsq g r` (E6Bridge31:241) |
| W∞(f) = ∫ f̂(t)(−log π + Re ψ(1/4 + it/2)) dt/2π (152)-(153) | on the pole-free class: Re archSide(autocorr g) = −log π·mass g + (1/2π)∫ hsq·psiR (E6Bridge31:699 `archSide_autocorr_poleFree`; psiR r = Re ψ(1/4 + ir/2), E6Bridge11:728) |
| the explicit formula (148)/CC2 (2.8): ψ(F) = F̂(i/2) + F̂(−i/2) − W_ℝ(F) − Σ_p W_p(F) | weilForm f = archSide f − primeSide f, with archSide = poles + W∞ and primeSide = Σ_p W_p (empty for 2L ≤ log 2: E6Bridge31 `primeSide_autocorr_eq_zero`) |
| τ(ρ) (39), W_ℝ = PV∫ f(ρ⁻¹)τ(ρ)d*ρ | **k(u) = τ(e^{\|u\|}) exactly**: for u > 0, e^{u/2}/2·(1/(1+e^u) + 1/(e^u − 1)) = e^{3u/2}/(e^{2u} − 1).  So the u-space identity Q(g) = (ψ(1/4) − log π)‖g‖² + ½∫∫\|g(v) − g(w)\|²k(v−w) is CC's principal value written as a Dirichlet form, with the constant ψ(1/4) − log π = −5.3722.  The identity is verified numerically to 1e-7 (PR #604 numerics).  It is NOT yet in Lean as an identity; E6Bridge32 has the N-truncated inequality. |
| D(f) = ∫ f(ρ⁻¹)δ(ρ)d*ρ | D(g∗g*) = ∫∫ g(v) ḡ(w) δ(e^{\|v−w\|}) dv dw (a bounded, continuous kernel) |
| Q = −(ρ∂_ρ)² + ¼ on f; Rem 6.12: g = (½ − ρ∂_ρ)h | g = h/2 − h' (CC); our earlier form g = h' − h/2 is the same up to sign.  paperFT g r = −(i r + ½)·paperFT h r, so \|ĝ\|² = (r² + ¼)\|ĥ\|². |
| L²(√I, d*ρ) on the g-interval; N_I, K_I | L²([−L, L], du) with L = \|I\|/2 |

### 2.2 The precise statements

* **(Y), Yoshida, which is the Lean target.**  IsWeilTest g, tsupport g ⊆ [−L, L], 2L ≤ log 2, paperFT g (I/2) = 0 ⇒ 0 ≤ Re weilForm(autocorr g).
  * Already a corollary of `KWin_Bridge.weil_positivity_prime_free_window`.
  * True up to L = 0.3716 with margin 0.0723 at L₀.
* **(CC1), CC Thm 1 in our conventions.**  Same hypotheses as (Y) plus `paperFT g 0 = 0`.  Then
  Re weilForm(autocorr g) ≥ SoninTr(g) := Tr(ϑ(g) S ϑ(g)*) ≥ 0,
  where ϑ(g)ξ(v) = ∫ g(x) e^{−x/2} ξ(e^{−x}v) dx on L²(ℝ)_ev.
  * In HS form, SoninTr(g) = ‖S ϑ(g)*‖²_HS.
  * Margin of the plain positivity: 0.548.
  * **This is strictly stronger than "≥ 0" (a positive lower bound by an operator trace), but on a smaller class.**  KWin does not give it.
* **(CC6.11).**  The hypotheses of (Y) give
  Re weilForm ≥ SoninTr(g) − c·‖paperFT g 0‖², with c = 4γ/log 2 ≈ 16.99 (CC: 13 < c_best < 17).
* **(S-one), the Sonin route without conditioning** [C].  For 2L ≤ a*, Thm 4.7 + Prop 5.5 + λ_max(K_I) ≤ 1 give (Y) with the lower bound SoninTr(g).
  * a* = 0.5583 [N-here].
  * A comfortable certified instance is L = 1/4 (λ_max = 0.959).

### 2.3 The Q-trick in our variable (the bridge both routes share)

g pole-free and supported in [−L, L] ⇔ g = h' − h/2 with h(u) = e^{u/2} ∫_{−∞}^{u} g(t)e^{−t/2}dt.  Here h ∈ C_c^∞, with tsupport h ⊆ [−L, L] exactly when ∫ g e^{−u/2} = 0 (CC Lemma 3.3(iii)).
* paperFT g r = −(i r + ½)·paperFT h r.
* ‖ĝ‖² = (r² + ¼)‖ĥ‖².
* paperFT g 0 = −½∫h, so CC's extra condition is ∫h = 0, the constant direction ξ₀.

### 2.4 Manifest positivity of L without the trace formula

* By Prop 2.2(iii), L(f) = Tr(ϑ_m(f) P P̂ P) with P P̂ P = A*A, A = (1−P)·U·P.
  * U is the unitary with Schwartz kernel k_u(λ, μ) = 2(μ/λ)^{1/2}cos(2πμ/λ) (27).
  * P is multiplication by 1_{[1,∞)}.
* Hence L(g∗g*) = ‖A T_g‖²_HS, which in additive variables is
  ∫_{x<0} ∫_{y∈ℝ} |∫_{w≥0} 2e^{(w−x)/2} cos(2π e^{w−x}) g(w − y) dw|² dy dx.
* This is an L²-norm of explicit oscillatory integrals.  The inner integral is absolutely convergent because g has compact support.
* The analytic content of CC §1-2 is then the single identity
  **‖A T_g‖²_HS = W∞(g∗g*) + D(g∗g*)** [P-lit, CC Prop 2.2(iii)],
  proved by Fubini on the positive quadrant split into Δ ∪ Σ (CC (34)-(39)).
  The principal value appears exactly as our Dirichlet-form kernel k.
* This is the Lean-friendly form: no trace class, and no distributions beyond the u-space Dirichlet form already handled on the island.

## 3. Mathlib inventory (island pin, `.lake/packages/mathlib`)

| needed object | status | Mathlib names / notes |
|---|---|---|
| Fourier transform on ℝ, inversion | present | `Real.fourierIntegral` / `𝓕`, `Analysis/Fourier/FourierTransform.lean`, `Inversion.lean`.  The island uses its own `paperFT` (Zeta23) with `paper_inversion`. |
| Plancherel on L² | present | `Analysis/Fourier/LpSpace.lean`: `norm_fourier_eq`, `inner_fourier_eq` (Lp 2), `SchwartzMap.toLp_fourier_eq` |
| Fourier of derivatives | present | `Analysis/Fourier/FourierTransformDeriv.lean` (`fourier_deriv`); integration by parts `integral_mul_deriv_eq_deriv_mul` |
| Poisson summation (CC Lemma 6.2) | present | `Real.tsum_eq_tsum_fourier`, `SchwartzMap.tsum_eq_tsum_fourier` (`Analysis/Fourier/PoissonSummation.lean`) |
| Fourier series on intervals + Parseval | present | `Analysis/Fourier/AddCircle.lean` (`hasSum_sq_fourierCoeff`, `tsum_sq_fourierCoeff`) |
| compact operators | present | `IsCompactOperator` (`Analysis/Normed/Operator/Compact/Basic.lean`); Fredholm alternative (`.../FredholmAlternative.lean`: `hasEigenvalue_iff_mem_spectrum`) |
| spectral theorem, compact self-adjoint | present | `Analysis/InnerProductSpace/Spectrum.lean`: `orthogonalComplement_iSup_eigenspaces_eq_bot` (compact + symmetric), `finite_dimensional_eigenspace`; Rayleigh quotient `Analysis/InnerProductSpace/Rayleigh.lean` (`norm_eq_iSup_rayleighQuotient`, `hasEigenvector_of_isLocalExtrOn`) |
| min-max / Weyl eigenvalue perturbation (\|λ_n(A) − λ_n(B)\| ≤ ‖A−B‖, CC (134)) | **absent** | must be proved (Courant–Fischer for compact self-adjoint), about 600 lines.  Only "top eigenvalue = sup of the Rayleigh quotient" is cheap. |
| Hilbert–Schmidt operators / integral operators with L² kernels | **absent** | no `HilbertSchmidt` and no generic integral-operator API.  Compactness of an L²-kernel operator on L²(I) must be built: finite-rank approximation by kernel truncation in an orthonormal basis, about 800 lines. |
| trace class, operator trace | **absent** | `TraceClass` does not exist.  **Avoid** via the HS rewrites (2.2, 2.4). |
| orthogonal projections | present | `Submodule.starProjection`, `orthogonalProjectionOnto` |
| pairs of projections / Halmos two-subspace theorem | **absent** | bypass with the spectral theorem of the compact operator P₁P̂₁P₁ |
| Sonin space | **absent** | definable: `{ξ ∈ L²_ev | ξ =ᵐ 0 on [−1,1] ∧ 𝓕ξ =ᵐ 0 on [−1,1]}`; closedness by continuity of 𝓕 on L² |
| prolate spheroidal wave functions | **absent** | build as eigenvectors of P₁FP₁ (compact self-adjoint), or of the tridiagonal Legendre matrix.  Simplicity of the spectrum and identification with Slepian's ODE solutions need singular Sturm–Liouville theory, which is absent and hard. |
| Legendre polynomials | partial | `RingTheory/Polynomial/ShiftedLegendre.lean` (shifted, on [0,1]); orthogonality on [−1,1] is not there |
| Bessel / Hankel functions | **absent** | not needed if we avoid the Hankel form of Sonin |
| sine integral Si | **absent** | define Si z = ∫₀^z sin t/t; better, use the form δ(ρ) = 4ρ^{1/2}∫₀¹cos(2πρt)cos(2πt)(−log t)dt (CC (48)), which avoids Si |
| digamma | present + island | `Complex.digamma` (`Analysis/SpecialFunctions/Gamma/Digamma.lean`: `digamma_one`, `digamma_one_half`, …); island: `psiR`, `psiR_ge_series`, `psiR_mono`, `psiR_ge_rational` (E6Bridge30), `Zeta23.MuFields.re_digamma_vertical` |
| trigamma / (log Γ)'' (CC Lemma 6.6) | absent as a named object | only needed on the bypassed T-route |
| Riemann–Siegel θ | absent | not needed: 2θ' = psiR − log π |
| Taylor bounds for exp/sin/cos | present | `Complex.exp_bound'`, `Real.sin_bound`, `sin_ge_sub_cube`, `one_sub_sq_div_two_le_cos` |
| convolution | present | `Analysis/Convolution.lean` (`MeasureTheory.convolution`); island `WeilExplicit.autocorr`, `WeilForm.crossCorr` |
| Boas–Kac / positive-definite square roots (CC Prop 3.2) | absent | not needed: our class is g, not f |

## 4. Lemma DAG, minimal path, staged plan

### 4.1 Bypasses (the minimal path)

* **B1. Trace class → HS norms.**  Every "Tr(ϑ(g) X ϑ(g)*)" with X a projection, or X = A*A, is ‖X^{1/2}ϑ(g)*‖²_HS, an explicit double integral.  The local trace formula (CC §1) collapses to the identity in 2.4.
* **B2. Halmos → compact spectral theorem.**  The pairs-of-projections decomposition (Lemma 4.2) is replaced by the spectral decomposition of the compact self-adjoint P₁P̂₁P₁ on ran P₁.  This uses Mathlib's `orthogonalComplement_iSup_eigenspaces_eq_bot`, and the Sonin space falls out as the complement.
  * Simplicity of the spectrum is NOT needed for Thm 4.7.  The proof only uses an orthonormal eigenbasis ξ_n of ran P₁ with P₁F P₁ξ_n = λ_n ξ_n.
  * The **prolate ODE is not needed** for the structural theorem.  It is needed only to *compute* λ_n and ξ_n.
* **B3. Rokhlin–Xiao / Wang → elementary tails.**  Taylor-truncate e^{2πixy} at degree n on [−1,1]².  The truncation has rank ≤ n.  So Σ_{k≥n} λ_k² ≤ ‖e^{2πixy} − T_n‖²_{L²} ≤ (2π)^{2n}·4/(n!)².  This bounds the tail of the series (84)/(97) together with ‖D_uξ_n‖-type bounds from the eigen-relation (CC App. F style, but self-contained).
* **B4. §6 Toeplitz apparatus → certified Galerkin + tail on K_I.**  Only spectral facts about the explicit HS operator K_I are needed:
  * one-condition route: λ_max(K_I) ≤ 1;
  * CC Thm 1 route: λ_max, a gap bound λ₂ ≤ 0.78, and an overlap ⟨ζ|ξ₀⟩ ≥ 0.94, then Lemma 6.9.

  Use a Legendre (or sine) Galerkin basis on I, a Schur-complement tail and Weyl perturbation, exactly the pattern of KWin_Tail.  The q → 1 discretisation, the angles α_j, the weights d(j), the product h(z) and Lemmas 6.4 and 6.6 drop out.
* **B5. The kernel χ.**  This is the only place prolates enter numerically:
  χ(v) = (Qε)(e^{|v|})/(2ε'(1⁺)) = Σ_{n≤N} λ_n²/(1−λ_n²)·C_n(e^{|v|})/(2ε'(1⁺)) + tail.
  * It needs certified λ_n, ξ_n and ξ_n' on [0, 2] for n ≤ 10.
  * Certified eigenpairs come from the truncated tridiagonal Legendre matrix, with residual + gap (Kato–Temple) bounds and a Legendre-truncation tail.
  * These are proved in Lean once, generically, for a computed rational vector checked by `decide +kernel`.

### 4.2 DAG with sizes (Lean lines, estimated by analogy with E6Bridge31-34 and KWin, about 3k each)

```
S1 u-space Weil identity ─┐
S2 Q-trick (g = h' - h/2) ─┼─► S4 jump lemma: D∘Q = -2Id + K^δ ─► S4' δ-rung (L ≤ 0.093, certified λmax(K^δ) ≤ 2)
S3 L ≥ 0 (HS rewrite) ─────┘                     │
                                                  ▼
S5 HS-kernel operators on L²(I) + compactness ─► S6 Sonin/prolate structural (B2) ─► S7 Thm 4.7: SoninTr = W∞ + E
                                                                                        │
S8 E∘Q kernel (Lemma 5.1/5.2, Prop 5.3/5.5) ◄────────────────────────────────────────────┘
       │
S9 certified prolate engine (B5) ──► S10 certified χ ──► S11 spectral certificate for K_I (B4) ──► S12a (S-one) at L = 1/4
                                                                                                  └► S12b CC Thm 1 at (log 2)/2
```

| stage | content | new / reuse | est. lines | ends in a kernel-checked theorem that is useful on its own |
|---|---|---|---|---|
| **S1** | Re archSide(autocorr g) = poles + (ψ(1/4) − log π) mass + ½∫∫\|g(v) − g(w)\|²k(v−w) for IsWeilTest g; k = Σ_n e^{−(2n+½)\|u\|} = τ(e^{\|u\|}) | reuse E6Bridge32 (`pairing`, `integral_hsq_mul_lor`, `re_arch_integral_ge`), E6Bridge33 (`Eb_eq_half`); new: the N → ∞ limit (monotone convergence on both sides, `re_digamma_vertical` series = psiR exactly) | 500-800 | yes: the **exact** u-space Weil identity (named in the memory note as "not yet in Lean").  It is CC's PV formula (39) in Dirichlet form. |
| **S2** | pole-free ⇔ g = h' − h/2 with h ∈ C_c^∞ supported in [−L, L]; \|ĝ\|² = (r² + ¼)\|ĥ\|²; ∫g ↔ ∫h | new (integration by parts, support of an antiderivative) | 300-400 | yes: parametrisation of the pole-free class (CC Lemma 3.3) |
| **S3** | δ(e^{\|u\|}) via CC (48) (no Si); ‖A T_g‖²_HS = Q(g) + ⟨g, K_δ g⟩; hence L ≥ 0 for every g of any support | new; the hardest structural analysis (oscillatory kernels, Fubini on Δ ∪ Σ, matching the PV with k) | 2500-4000 | yes: **CC Cor 2.3**, positivity of W∞ + D for all supports.  A Lean-checked conceptual positivity.  Alternative S3': prove ℓ(t) = psiR(t) − log π + δ̂(t) ≥ 0 pointwise by certified numerics plus large-t asymptotics (slack 0.049 at t = 0), about 1500 lines + certificate.  Non-conceptual. |
| **S4** | D∘Q(ξ∗ξ*) = −2‖ξ‖² + ⟨ξ, K^δ_I ξ⟩ (Thm 3.6, via Rem 3.7 integration by parts) | new, moderate | 400-600 | yes |
| S4' | δ-rung: certified λ_max(K^δ_I) ≤ 2 ⇒ (Y) for L ≤ 0.093; or the L¹ version for L ≤ 0.0488 (no matrix) | certificate (Si/cos-integral enclosures) | 400 + data | weak: below the proved L ≤ 1/10.  It is the **first end-to-end conceptual rung**, so it is useful as a pipeline test. |
| **S5** | integral operators with L²(I×I) kernels: boundedness (Schur/HS), compactness, self-adjointness, Rayleigh; Weyl perturbation \|λ_k(A) − λ_k(B)\| ≤ ‖A − B‖ | new infrastructure (Mathlib gap) | 1200-1800 | yes: reusable Mathlib-grade API |
| **S6** | P₁, P̂₁ on L²(ℝ)_ev; P₁P̂₁P₁ compact; eigenbasis ξ_n; η_n, ψ_n, ζ_n (Prop 4.5); Sonin space = eigenspace for 1 of P P̂ P (B2) | new, uses S5 + Mathlib L² Fourier | 2000-3000 | yes: the Sonin/prolate structure theorem (CC Prop 4.5, (81)) |
| **S7** | Thm 4.7: SoninTr(f) = W∞(f) + E(f), ε as in (84), with convergence by B3 | new | 1000-1500 | yes: **CC Thm 4.7**, the "reason" for positivity |
| **S8** | Lemma 5.1/5.2 boundary terms, Prop 5.3 (99), Lemma 5.4 ε'(1⁺), Prop 5.5 N_I = −2ε'(1⁺)(Id − K_I) | new, calculus | 800-1200 | yes |
| **S9** | certified prolate engine: truncated tridiagonal W in even Legendre (rational entries in c² = 4π², so π-enclosures), Kato–Temple eigenpair bounds, Legendre-tail bounds, values/derivatives on [0, 2] (for x > 1 via the eigen-relation (68)) | new; certificate data via `decide +kernel` | 2000-3000 + data | yes: the first kernel-checked prolate eigen-data anywhere (CC map §4 found no formalisation) |
| **S10** | certified χ on [0, log 2] (piecewise-polynomial enclosure, the KWin_Minorant pattern) | new | 600-1000 + data | |
| **S11** | spectral certificate for K_I: Galerkin + Schur tail (the KWin_Tail pattern) giving λ_max(K_I) ≤ 0.96 at \|I\| = ½ (one condition); or λ_max ∈ [1.050, 1.053], λ₂ ≤ 0.78, ⟨ζ\|ξ₀⟩ ≥ 0.94 at \|I\| = log 2 | new + data | 1000-1500 + data | |
| **S12a** | (S-one): (Y) with the Sonin lower bound for L ≤ 1/4 | assembly | 200 | yes: one-condition, **conceptual + certified**, short of the full window |
| **S12b** | CC Thm 1 / 6.11 in our conventions (Lemma 6.9 assembly) | assembly | 300 | yes: **W∞ ≥ SoninTr ≥ 0** on the CC class at L₀, strictly stronger than KWin's "≥ 0" there |

**Totals.**
* S1-S4 (structural core without prolates): about 3.7-5.8k lines.
* Through S12b: **about 12-18k lines plus certificate data**.
* For comparison, KWin (full class) took about 3.3k lines of Lean plus data.

**Parallelism.**  S1, S2, S5 and S9 are independent.  S3 depends on S1.  S6 and S7 depend on S5.  S10 and S11 depend on S8 and S9.

### 4.3 Recommended staging

1. **S1 + S2 + S4** (about 1.5k lines).  These are cheap, independently useful (the exact Weil identity and the pole-free parametrisation), and needed by every route.
2. **S3**, the structural L ≥ 0.  This is the decisive test of whether the conceptual layer is formalisable at a sane cost.  If it overruns, take S3' and record that the "conceptual" layer is partial.
3. **S5 → S6 → S7**, the Sonin structure theorem.  It is mathematically the heart, and it is purely structural given B2.
4. **S8 → S9 → S10 → S11 → S12a**, then S12b.  These are the certified-numerics tail.  S12a needs the least precision (λ_max ≤ 0.96).

## 5. Feasibility verdict and what it buys

**Verdict: FEASIBLE ONLY WITH CERTIFIED NUMERICS**, as a staged programme of about 12-18k lines.

The certified numerics needed are:
1. prolate eigen-data for c = 2π, n ≤ 10: λ_n to about 1e-9, and ξ_n, ξ_n' on [0, 2] to about 1e-8;
2. the kernel χ = Qε/(2ε'(1⁺)) on [0, log 2] to about 1e-5 in L¹;
3. one spectral certificate for the HS operator K_I.  At L = 1/4 this is λ_max ≤ 0.96.  At L₀ on CC's class it is λ_max − 1 ≈ 0.0516, λ₂ ≤ 0.78 and ⟨ζ|ξ₀⟩ ≥ 0.94, with total slack ε₂ − ε₁ ≈ 0.003.

The CC §6 route as written (Toeplitz guesses, downloaded α_j/d(j), floating-point ε₁ = 0.00122) is NOT practical to formalise faithfully.  B4 replaces it.

**What it does NOT give.**
* It does not give the one-condition statement (Y) on the full window.  CC's argument provably cannot without a further idea (Rem 6.12).
* (Y) on the full window stays covered by KWin only.
* The conceptual route gives (Y) only for L ≤ 0.279 (S12a), and CC's two-condition class on the full window (S12b).
* It involves no prime, so it cannot separate ζ from Davenport–Heilbronn.

**What it would give beyond KWin.**
1. **A stronger inequality on CC's class:** W∞ ≥ Tr(ϑ(g)Sϑ(g)*), a positive operator-trace lower bound, not just ≥ 0.
2. **Kernel-checked structural theorems that exist nowhere else in formal form:**
   * the exact u-space Weil identity (S1);
   * CC Cor 2.3, W∞ + D ≥ 0 for all supports (S3);
   * the Sonin decomposition SoninTr = W∞ + E (S7);
   * certified prolate data (S9).
3. **A template for the semilocal case.**  CC's intro and the CCM paper (arXiv:2310.18423: semilocal Sonin spaces, Thm 2) frame this as a programme for places {∞, 2, …, p}.

**Does it plausibly extend past the first prime?**  Not with current tools; this is [C], judged from the literature and the gate-0 ladder:
* No paper proves semilocal positivity for any set S containing a prime (CC map §1, reading note §3).
* CC2 (2106.01715) reports only numerics past log 2, with margins that become exponentially small: 2.4e-48 at μ = 11.
* The gate-0 ladder measured λ_min ≈ exp(−(60–80)L²) and found that Davenport–Heilbronn passes every rung below L ≈ 1.86.
* A semilocal analogue of S11 would need certified spectra at precision e^{−(60–80)L²}.  S12b's slack is about 3e-3.
* The structural part (S3, S7) is the piece CC claim generalises.  Formalising it now would make a semilocal attempt a matter of new mathematics plus the same certificate pattern, not new infrastructure.

**Closest practical alternative,** if the user wants a "reason" rather than a certificate at lower cost: S1 + S2 + S3' + S4.
* This is about 3-4k lines.
* It gives a kernel-checked W∞ + D ≥ 0 (by certified ℓ(t) ≥ 0), the Q-trick, and the jump lemma.
* That is CC's §2-3 mechanism end to end, plus the δ-rung (L ≤ 0.093, below KWin) as an honest demonstration.
* The prolate/Sonin layer would be deferred.

`conjecture1_proved = False`.
