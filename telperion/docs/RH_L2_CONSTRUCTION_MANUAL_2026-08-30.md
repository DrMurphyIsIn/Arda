<!-- ultrathink 4-agent primary-source extraction of Connes 1999 L2 spectral realization, 2026-08-30. Build spec for H1(Pic~,eta~): objects 1-5 unconditional at finite Lambda; the 2 claims (clean limit + Weil positivity) are RH-equivalent. conjecture1_proved=False. -->

# The L² framework for H¹(P̃ic(Spec Z), η̃): exact ingredients to build on

**Status:** `conjecture1_proved=False`. This is a construction toolkit, not a proof. Every formula below is source-anchored to Connes math/9811068 (Selecta Math 5 (1999) 29–106), Connes–Consani 2006.13771 (archimedean Weil positivity), 2207.10419 (Hochschild/ζ-cycles), and 2602.15941 (Jacobian of Spec Z̄). Equation numbers are the authors' own. Items marked **[SYNTH]** or **[UNVERIFIED]** are not quotable single-line theorems — do not build a proof on them without independent confirmation.

---

## (1) THE SPACE

The construction lives on **two** Hilbert spaces linked by an isometry `E`; the target object is the **cokernel** of `E`. Do not conflate them.

**Base function space** (Connes III.6) — the codimension-2 Bruhat–Schwartz subspace:
```
S(A)₀ = { f ∈ S(A) ; f(0) = 0 , ∫ f dx = 0 }
```
Both conditions are load-bearing and are the origin of the two divergent boundary terms later. `f(0)=0`: because `0` is `k*`-fixed, so `Σ_{q∈k*} f(qx)` needs it. `∫f dx=0`: because as `|x|→0`, `Σ f(qx) ≈ |x|⁻¹∫f dx` (Riemann-sum divergence). The 2-dim supplement `S(A)/S(A)₀ = C ⊕ C(1)` carries the trivial module plus the Tate twist `C(1)` (III.10–11).

**Adele-class Hilbert space** `L²_δ(X)₀`, `X = A/k*` = completion of `S(A)₀` in (Connes III.7):
```
‖f‖²_δ = ∫_{A*/k*} |Σ_{q∈k*} f(qx)|² (1 + log²|x|)^{δ/2} |x| d*x
```
Key point (Connes' own): the measure is `|x| d*x`, NOT additive `dx`. The weight `(1+log²|x|)^{δ/2}` is the "unnatural" Sobolev parameter `δ`.

**Companion idele-class-group space** `L²_δ(C_k)`, `C_k = GL₁(A)/k*` (Connes III.12):
```
‖ξ‖²_δ = ∫_{C_k} |ξ(g)|² (1 + log²|g|)^{δ/2} d*g
```
with module normalization `∫_{|g|∈[1,Λ]} d*g ∼ log Λ` (III.14).

**The intertwining isometry E** (Connes III.18) — a scale-invariant Riemann sum with a half-density twist:
```
E(f)(g) = |g|^{1/2} Σ_{q∈k*} f(qg)   ∀g ∈ C_k
```
The `|g|^{1/2}` is forced by matching `|g|d*x` in (7) against `d*g` in (12).

**δ is scaffolding — eliminate it.** Section VIII sets `δ=0`: `L²(X) := L²_δ(X)|_{δ=0}`. The final construction must use the clean `δ=0` space; `δ>1` exists only to make the absorption spectrum a point spectrum in Theorem 1. Carrying `δ` into the final object is an error.

---

## (2) THE ACTION

**Scaling representation on the adele-class space** (Connes III.9):
```
(U(j) f)(x) = f(j⁻¹ x)   ∀x ∈ A, j ∈ C_k
```

**Left regular representation on `L²_δ(C_k)`** (Connes III.15):
```
(V(a) ξ)(g) = ξ(a⁻¹ g)   ∀g, a ∈ C_k
```

**Equivariance / half-density twist** (Connes III.19) — the reason the realization sits at `Re = ½`:
```
E U(a) = |a|^{1/2} V(a) E
```
`Im(E)` is a closed `V`-invariant subspace. `W` = the representation induced by `V` on the cokernel `H`. `V, W` are non-unitary from the Sobolev weight: `‖V(g)‖ = O(log|g|)^{δ/2}` (III.16); at `δ=0` the restriction to `K={|g|=1}` is unitary.

**Semilocal form** (2602.15941, eq. 19), `A_S = Π_{v∈S} Q_v`, `C_{Q,S} = Z_S^×\A_S^×`:
```
(θ(u) ξ)(a) = ξ(u⁻¹ a),   ξ ∈ L²(Z_S^×\A_S)
```

---

## (3) THE SPECTRUM — the crux

**The zeros appear as CO-INVARIANTS (a cokernel/quotient), realized spectrally as an ABSORPTION spectrum — not as eigenvalues of a positive Polya–Hilbert operator on a subspace.** This is unambiguous and stated in all four papers.

**The Polya–Hilbert space is the cokernel** (Connes III.33, verbatim after III.19):
```
0 → L²_δ(X)₀ → L²_δ(C_k) --E--> H → 0 ,    H = L²_δ(C_k) / Im(E)
```
> "the cokernel `H = L²_δ(C_k)/Im(E)` of the isometry E plays the role of the Polya-Hilbert space."

Confirmed independently in 2207.10419: **Prop 3.3** — the range of the trace map = **co-invariants** = quotient by the subspace of `f − f_γ`; **Thm 1.2** — the spectral realization of the critical zeros is `H⁰(S, L²/Σ Ē)`, the cohomology of the **quotient** by the closure of the range of `E`.

**The operator D** (Connes III.26). Decompose `C_k ≅ K × N`, `K={|g|=1}`, `N=|C_k|⊂R*₊`; `H = ⊕_{χ∈K̂} H_χ`. On each sector:
```
D_χ ξ = lim_{ε→0} (1/ε)(W_χ(e^ε) − 1) ξ
```
**Theorem 1** (Connes III, verbatim):
> "`D_χ` has discrete spectrum, `Sp D_χ ⊂ iR` is the set of imaginary parts of zeros of the L function with Grössencharakter χ̃ which have real part equal to ½; `ρ ∈ Sp D_χ ⇔ L(χ̃, ½+ρ)=0` and `ρ∈iR`" (multiplicity = largest integer `n<(1+δ)/2`, `n ≤` zero multiplicity).

Riemann ζ = trivial character, `k=Q`. **How each family of zeros appears:**
- **Critical zeros (Re=½):** genuine point spectrum of `D_χ` (after `δ` isolates them) = the missing lines of the absorption spectrum in the cokernel `H`.
- **Non-critical zeros:** appear as **resonances**, entering the trace formula "through their harmonic potential with respect to the critical line" (Connes §VIII, Lemma 3). The `δ`-space "artificially eliminates the non-critical zeros."
- The "appear from its negative ⊖H" / absorption framing (Connes intro, eq. C) is the cohomological SIGN — the `−Σ ĥ(χ,ρ)` in the trace formula.

**Corollary 2** (spectral trace, Connes III): for `h∈S(C_k)`, `W(h)=∫W(g)h(g)d*g` is trace-class,
```
Trace W(h) = Σ_{L(χ̃,½+ρ)=0, ρ∈iR/N⊥} ĥ(χ̃,ρ),   ĥ(χ̃,ρ) = ∫_{C_k} h(u) χ̃(u) |u|^ρ d*u
```

**This spectral side is entirely canonical and unconditional** — Theorem 1 constructs `Sp D_χ` with no RH assumption and without even defining the L-functions first.

---

## (4) THE TRACE FORMULA

**Cutoff** (Connes V.15–16). On `L²(K)`, `P_Λ` = multiplication by the indicator of `{|x|≤Λ}` (infrared); `P̂_Λ = F P_Λ F⁻¹` (ultraviolet, Fourier-conjugate); the phase-space cutoff:
```
P_Λ = { ξ ∈ L²(K) ; ξ(x)=0 ∀ |x|>Λ } ,    R_Λ = P̂_Λ P_Λ
```

**Local trace formula — Theorem 3** (Connes §V, verbatim), `h∈S(K*)` compact support:
```
Trace(R_Λ U(h)) = 2 h(1) log′Λ + ∫′ h(u⁻¹)/|1−u| d*u + o(1)
   2 log′Λ = ∫_{λ∈K*, |λ|∈[Λ⁻¹,Λ]} d*λ
```
`∫′` = the principal value fixed by "the unique distribution agreeing with `du/|1−u|` for `u≠1` whose Fourier transform vanishes at 1" = Weil's principal value.

**Global — Theorem 5** (Connes §VIII), `Q_Λ` = projection onto `f∈S(A)` with `f, f̂` vanishing for `|x|>Λ`:
```
Trace(Q_Λ U(h)) = 2 h(1) log′Λ + Σ_v ∫′_{k_v*} h(u⁻¹)/|1−u| d*u + o(1)   ⟺   RH for all Grössencharakter L
```

**Origin of the `2h(1)log′Λ` divergence** (Connes V.29–33). With `g(λ)=h((λ+1)⁻¹)|λ+1|⁻¹`, the annulus integral `∫dx/|x|` over `|Λ⁻¹u|≤|x|≤Λ` gives `2log′Λ − log|u|` (V.30), hence:
```
(V.31)  Trace(R_Λ T) = ∫_{|u|≤Λ²} ĝ(u)(2 log′Λ − log|u|) du
(V.33)  Trace(R_Λ T) = 2 ĝ(0) log′Λ − ∫ ĝ(u) log|u| du + o(1)
```
The divergence is `2ĝ(0)log′Λ` with `ĝ(0)=h(1)` — the value of the test function at the group identity `= the non-transversal / diagonal / regular-representation term`. `2log′Λ` is literally the `d*λ`-volume of the truncated scaling group. **`h(1)=0` kills the divergence**; the formula collapses to pure transversal fixed-point terms.

**Origin of the finite local terms** (Connes V.34–36). The self-dual Fourier transform of `−log|u|` equals `ρ⁻¹/|a|` off 0, so by Parseval:
```
−∫′ ĝ(u) log|u| du = (1/ρ) ∫′ ĝ(a)/|a| da = ∫′ h(u⁻¹)/|1−u| d*u
```
These are exactly the Weil explicit-formula local terms `Σ_v D_v` (App. II, eq. 8: `D_v(f)=Pf_w ∫ f(u)/(|1−u||u|^{1/2}) d*u`), minus the discriminant term `log|d⁻¹|`.

**The o(1):** rapid-decay Fourier tail beyond scale `Λ²`, `O(Λ⁻N) ∀N` (V.32), because `h` is smooth compactly supported. Nothing spectral is discarded.

---

## (5) THE RELATIVE/PAIR OBJECT — how to define H¹(P̃ic, η̃)

**Define it as a COKERNEL (co-invariants), NOT a relative subspace.** The `2h(1)log′Λ` divergence is homed on `η̃` by quotienting out the generic-point regular representation.

**The CC26 bridge** (2602.15941, verbatim):
- **Thm 7.9:** the fiber over the generic point is `F_η ≅ C_Q` (class number 1: every rank-1 subgroup of `Q` is `≅ Z`).
- **§9.2:** "We interpret the divergent term `2h(1)logλ` as the contribution of the image `Θ(η) = η̃` of the generic point... This suggests that the relevant cohomology is that of the pair `(P̃ic(Spec Z), η̃)`."
- **§9.3 eq. 20:** semilocal `Trace(θ(h) R_λ) = 2h(1)logλ + Σ_{v∈S} ∫′_{Q_v×} h(u⁻¹)/|1−u| d*u + o(1)`; the `2h(1)logλ` "signals the white light coming from the (trace of the) regular representation... the contribution of the image of the generic point."

**The correct L² construction of the pair** (Connes §VIII, the difference of two projections whose divergences cancel):
- `S_Λ` (VIII.21) = regular-representation cutoff `{ξ : ξ(g)=0 ∀|g|∉[Λ⁻¹,Λ]}` = the **white light / η̃ piece**, with `Trace(S_Λ V(f)) = 2f(1)log′Λ`.
- `Q'_{Λ,0} = E Q_{Λ,0} E⁻¹` = the image of the adele-class cutoff.
- **Reflection identity** (Connes App. I Lemma 2, eq. 38): `E(f)(x) = E(f̂)(1/x)` — this forces `E(B_{Λ,0}) ⊂ S_Λ`, giving the projection inequality `Q'_{Λ,0} ≤ S_Λ` (VIII.23).
- **The pair object** = the difference, `Δ_Λ(f) = Trace((S_Λ − Q'_{Λ,0}) V(f))` (VIII.24), whose `Λ→∞` limit is the Weil distribution `Δ = log|d⁻¹|δ₁ + D − Σ_v D_v` (VIII.17). The two divergent `2f(1)log′Λ` terms cancel, leaving the finite spectral side.

**Recipe for `H¹(P̃ic, η̃)`:** take `L²(C_Q)` with the scaling/regular representation; the generic point `η̃ = Θ(η)` supplies `Im(E)` (the white-light `2h(1)logλ`); **quotient it out** (equivalently, form `S_Λ − Q'_{Λ,0}`). The residual absorption spectrum on the cokernel is the critical zeros. The `2h(1)logλ` counterterm is precisely what the quotient removes. **[SYNTH/FLAG]** CC realize this pair as a degree-0 cokernel `H⁰(S, L²/Im E)`, not literally `H¹`; the `H¹`↔`H⁰` shift is the expected `H¹(curve) ↔ H⁰(coker trace)` dimension shift. Any literal `H¹` degree claim must be reconciled with the CC `H⁰`-realization before use.

---

## (6) THE (4d) OBSTRUCTION

State the required properties as: **S1** (trace-class / discrete spectrum after cutoff), **S3** (`C_Q`-equivariant), **S4** (self-dual under `s ↔ 1−s`, i.e. Fourier `F` / inversion symmetry, entering via `R_Λ = P̂_Λ P_Λ`).

**The structural obstruction — compact vs non-compact base** (Connes III, after eq. 21) **[SYNTH]**:
- Over `F_q`: `N = |C_k| ≅ q^Z ≅ Z` is **discrete**; the `N`-action on each `H_χ` is a single operator with unitary spectrum — compact/finite-dimensional per sector, `H¹` finite-dim, RH is Weil's theorem.
- Over `Q`: `N = R*₊` is **continuous non-compact**; `D_χ` has continuous "white-light" spectrum on `L²(C_Q)`. Discreteness must be *manufactured* by the cutoff, paying the `2h(1)logλ` divergence. This is the "(4d)"-type obstruction: there is no ambient compact geometry forcing S1.

**What is unconditional vs RH-equivalent** (the precise definitional status):
- **Unconditional:** the space `L²(X)₀` / cokernel `H`, the reps `U/V/W`, the operator `D_χ`, the cutoff `R_Λ`/`Q_Λ` (trace-class after cutoff), **S3** (equivariance is built in), and **S4** (Fourier/inversion is a definitional symmetry). Theorem 1 constructs the critical-zero spectrum with no RH input.
- **RH-EQUIVALENT:** the clean `Λ→∞` limit of the trace formula (Thm 5 a⇔b) — equivalently **positivity of the Weil distribution** `Δ` (VIII.17), `Δ_Λ(f*f*) ≥ 0`, equivalently the projection inequality `Q'_{Λ,0} ≤ S_Λ` surviving the limit. **S1 in the limit** (that the pair object is trace-class with the clean `2h(1)logλ + Σ_v` form and no extra positive defect) is exactly where RH enters.

**What a construction with S1∧S3∧S4 would have to prove** — two claims:
1. **(existence / limit trace-class)** The pair cokernel `H = L²(C_Q)/Im(E)` carries a trace-class realization of the scaling action in the `Λ→∞` limit whose trace is exactly `Σ_v ∫′ h(u⁻¹)/|1−u|` (no extra term) — equivalently `Δ_Λ(f) → Δ(f)` with the clean form.
2. **(positivity)** The Weil distribution is positive: `Δ(f * f*) ≥ 0` for all admissible `f`.

Either claim, established, yields RH (Thm 5, VIII.17). **[FLAG]** No source states "S1∧S3∧S4 ⇒ zeros on the line" as a single packaged theorem; that implication is interpretive. The honest status: S3, S4, and the *cutoff-level* S1 are free; the *limiting* S1 = positivity of `Δ` = RH. Positivity is a **separate inequality on the finite geometric term** (2006.13771 Thm 1: `W_∞(g*g*) ≥ Tr(ϑ(g) S ϑ(g)*)`, `S` = projection onto Sonin's space = complement of `Range(P̂₁P₁)`) — it does NOT enter the definition of the space, only the upgrade of the trace-formula equality to RH.

---

## BUILD SPEC

**Objects the construction must define (5):**
1. **The space:** `H = L²(C_Q) / Im(E)` (δ=0), cokernel of `E(f)(g) = |g|^{1/2} Σ_{q∈Q*} f(qg)` from `L²(A/Q*)₀` (codim-2: `f(0)=0, ∫f=0`), with measure `|x|d*x`.
2. **The action:** the induced scaling/regular representation `W` of `C_Q` on `H`, from `(V(a)ξ)(g)=ξ(a⁻¹g)`, intertwined by `E U(a) = |a|^{1/2} V(a) E`.
3. **The operator:** `D_χ = lim_{ε→0} ε⁻¹(W_χ(e^ε)−1)`, per character sector, `Sp D_χ ⊂ iR` = critical zeros (absorption spectrum on the cokernel).
4. **The cutoff pair:** `S_Λ` (regular-rep cutoff = white-light / `η̃` piece) and `Q'_{Λ,0} = E Q_{Λ,0} E⁻¹`, with the reflection identity `E(f)(x)=E(f̂)(1/x)` giving `Q'_{Λ,0} ≤ S_Λ`.
5. **The pair/relative object:** `Δ_Λ(f) = Trace((S_Λ − Q'_{Λ,0}) V(f))` — the L² incarnation of `H¹(P̃ic, η̃)`, homing the `2h(1)log′Λ` divergence on `η̃ = Θ(η)` by cancellation.

**Claims the construction must prove (2):**
1. **Limit trace formula:** `Δ_Λ(f) → Δ(f) = log|d⁻¹|δ₁ + D − Σ_v D_v` as `Λ→∞` with no residual divergence — i.e. `Trace(Q_Λ U(h)) = 2h(1)log′Λ + Σ_v ∫′_{Q_v*} h(u⁻¹)/|1−u| d*u + o(1)`.
2. **Weil positivity:** `Δ(f * f*) ≥ 0` for all admissible `f` (equivalently `Q'_{Λ,0} ≤ S_Λ` in the limit).

Either proven claim ⟹ RH (Connes Thm 5 / VIII.17). **`conjecture1_proved=False`** — both remain open; the definitions (Objects 1–4, and Object 5 at finite Λ) are unconditional, the two claims are RH-equivalent.