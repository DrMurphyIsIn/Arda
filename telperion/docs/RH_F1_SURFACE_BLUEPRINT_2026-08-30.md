<!-- ultrathink 9-agent primary-source campaign, 2026-08-30. The exact specification + construction-state of the polarized F1 surface. Determines the object; does NOT construct it (that is RH). conjecture1_proved=False. -->

# The polarized F1 surface: exact specification, construction-state, and the one definitional gap

*Synthesis over primary sources on the "Spec Z ×_{F1} Spec Z" surface program for RH. Every claim graded PROVEN / CONSTRUCTED / CONJECTURAL / PROVABLY-OBSTRUCTED. Grades and citations are drawn from the D1–D7 source dossiers and the skeptic pass.*

---

## 1. THE BLUEPRINT — the exact desiderata transported from the F_q proof

The target is Weil's 1948 proof of RH for a smooth projective curve C/F_q, run on the surface **S = C ×_{F_q} C**, via the Hodge index theorem. Modern exposition: Bombieri, Séminaire Bourbaki 430. To transport it to Spec Z one must reproduce, on a hypothetical **S = Spec Z ×_{F1} Spec Z**, each of the following. These are the *desiderata* — the specification, not the construction.

**(B1) A genuine 2-dimensional object containing Spec Z as a "diagonal curve."**
F_q template: S = C×C is a smooth projective surface; C embeds as the diagonal Δ. Requirement: a 2-dimensional S in which the Arakelov-compactified `\overline{Spec Z}` (arithmetic curve, archimedean place included) embeds as a diagonal.

**(B2) A Néron–Severi lattice NS(S) with a symmetric, real, computable intersection pairing.**
F_q template: NS(C×C)⊗ℚ with intersection form; correspondences = divisor classes; composition and the transpose involution D↦D′; the Weil trace pairing. Requirement: a finite-rank (or otherwise honest) group of correspondence classes with a symmetric bilinear pairing D·E.

**(B3) Signature (1, ρ−1): one positive (ample/Kähler) direction, negative-definite complement.**
F_q template: the Hodge Index Theorem — NS has signature (1, ρ−1); on the primitive part ⟨H⟩⊥ orthogonal to the ample class H, the form is **negative definite**. This sign is the entire engine.

**(B4) Frobenius correspondences Fr_λ, λ ∈ R_+^×, with a computable composition law and computable Fr_λ·Δ.**
F_q template: one Frobenius Fr and its powers Fr^n (a discrete ℤ-worth), plus fibres and Δ. F1 twist: the base's multiplicative group is the *full* R_+^× (the characteristic-1 / idele-class scaling flow), so one needs a **one-parameter family** Fr_λ with Fr_λ∘Fr_μ = Fr_{λμ} and computable intersection numbers.

**(B5) A regularized, FINITE diagonal self-intersection Δ·Δ equal to the f(1)-coefficient of the explicit formula.**
F_q template: Δ·Δ = 2−2g = χ(C), a finite integer; Fr·Δ = #C(F_q). Requirement: a **regularized** Δ·Δ (the naive one diverges — this is the crux) whose value reproduces the archimedean/"−log|a|"/conductor term, i.e. the coefficient of f(1) in the **Weil explicit formula**, concretely c = ½(log π + γ) plus the p-local transverse terms. The explicit formula plays the role of the Lefschetz trace formula.

**(B6) Hodge-index ⟹ |α|=√q analog ⟹ RH.**
F_q template: Hodge index applied to the primitive part gives (Δ·Fr)² ≤ (Δ·Δ)(Fr·Fr) = the Weil bound, equivalent to RH for C. Requirement: an analogous positivity inequality on S whose conclusion is that all ζ-zeros lie on Re(s)=½. This positivity is exactly **Weil positivity** of the explicit-formula distribution.

Two load-bearing theorems must be reproduced: the **Hodge Index Theorem** (⟺ B3, supplies the sign) and **Riemann–Roch on S** (needed to prove Hodge index and to compute χ, hence Δ·Δ).

---

## 2. CONSTRUCTION-STATE — program × desideratum grade matrix

Grade key: **PROVEN** (theorem) / **CONSTRUCTED** (object exists, positivity/ampleness unproven) / **CONJECTURAL** (target, no proof) / **OBSTRUCTED** (proved impossible on the naive route).

| Desideratum | Connes–Consani (arithmetic/scaling site + square) | Manin/Kurokawa (absolute tensor ζ̂⊗ζ̂) | Borger (Λ-rings) + prismatic | Deninger (foliated dynamical) |
|---|---|---|---|---|
| **B1** 2-dim object ⊃ Spec Z diagonal | **CONSTRUCTED** — square of arithmetic site, a *semi-ringed topos* (not a scheme) [1405.4527 Def 3.2/3.7] | FORMAL bookkeeping — ζ̂⊗ζ̂ is a *function*, no space | Λ-base = a *topos* Spec F1; prismatic = p-adic diagonal *completion* only [Scholze: "unknown"] | **CONJECTURAL** — foliated 3-system posited, not built for Spec Z |
| **B2** NS lattice + symmetric pairing | **CONSTRUCTED (local, real-valued)** RR on periodic orbits / **CONJECTURAL (global lattice)**; no integer NS lattice | No bilinear form at all | No — descent data / Witt comonad, no surface pairing | **CONJECTURAL** — leafwise, infinite-dimensional |
| **B3** Signature (1, ρ−1) / neg-definite | **CONJECTURAL** (= Weil positivity; archimedean fragment partial [2006.13771]) | Inaccessible (no form) | Absent | **CONSTRUCTED in model** (Θ=½+S, S skew) / **CONJECTURAL for Spec Z** |
| **B4** Fr_λ, λ∈R_+^×, composition | **PROVEN** — Ψ(λ)∘Ψ(λ′)=Ψ(λλ′) [GAS Thm 1.2 / 1405.4527 Thm 4.3]; continuous scaling flow [1507.05818] | N/A (formal factor) | **CONSTRUCTED (discrete only)** — ψ_p Frobenius lifts, ℕ^× not R_+^× | **CONSTRUCTED-in-model** — transverse flow φ_t = Fr_{log λ} |
| **B5** Regularized Δ·Δ = f(1) coeff | **CONSTRUCTED (value via distribution N(u)) / CONJECTURAL (as intersection number)**; 2026: divergence relocated to pair-cohomology [2602.15941 §9.3] | FORMAL (encodes the shape ρ₁+ρ₂) | UNVERIFIED | **CONJECTURAL** (dynamical Lefschetz) |
| **B6** Hodge-index ⟹ RH | **CONJECTURAL** (target; = `D•D ≤ 2(D•ξ₁)(D•ξ₂)` ⟺ RH) | CONJECTURAL | UNVERIFIED | **CONJECTURAL** |

**Most of the blueprint built — Connes–Consani.** It is the only program with a genuine 2-dimensional object (B1), Frobenius correspondences with a **PROVEN composition law** (B4, the single strongest positive transfer result), a continuous R_+^× family (the blueprint's novel feature), and a proven curve-level Riemann–Roch. It also owns the sole partial positivity theorem (archimedean place, Selecta 2021). **But its object is a semi-ringed Grothendieck topos with a characteristic-1 / Newton-polygon (`Conv_≥(ℤ×ℤ)`, ⊕ = convex hull, ⊙ = Minkowski sum) structure sheaf — not a scheme.**

**Deninger** owns the cleanest positivity *mechanism*: in the manifold model, Θ = ½ + S with S skew-adjoint on leafwise H¹ forces Re = ½ (a real Hodge-inner-product positivity, PROVEN as a model theorem, incl. the ordinary-elliptic-curve case). But the space carrying it does not exist for Spec Z, and the naive char-p lift is obstructed (Frobenius does not lift).

**Borger** owns the most scheme-like base + genuine Frobenius operators (ψ_p), but supplies no square, no lattice, no positivity — and only a discrete ℕ^× of Frobenii, missing the archimedean direction.

**Manin/Kurokawa** own the target-shape oracle: ζ̂⊗ζ̂ has the correct divisor ρ₁+ρ₂, but it is a regularized *product*, carrying no bilinear form and hence no positivity.

**Desiderata NO ONE has built:** B2 as a genuine integer NS lattice; B3 as a proven signature on the square; B5 as an honest intersection number; B6 in any form. **These are exactly B2, B3, B5, B6 — every load-bearing piece past B1/B4.**

---

## 3. PROVABLE OBSTRUCTIONS (D6) — why the naive scheme cannot exist, forcing the exotic objects

The exotic (topos/tropical/dynamical/Λ) objects are not stylistic choices; they are *forced* by a chain of theorems ruling out the naive scheme.

1. **No field F1 — PROVEN (trivial).** A field needs 0≠1; "F1" names a hoped-for base, no ring map F1→Z exists in the naive sense.

2. **Dimension/terminality — OBSTRUCTED.** Spec Z is terminal in schemes and dim 1; `Spec Z ×_{Spec Z} Spec Z = Spec Z`. A 2-dimensional product requires a base *strictly below* Spec Z, i.e. Spec F1 — which is not a scheme. So a genuine 2-dimensional *scheme* S cannot exist for a structural reason.

3. **Spec Z is not a finite-type F1-variety — PROVEN.** For Soulé F1-varieties the point-counting function N(q) is a polynomial; for `\overline{Spec Z}` the counting distribution N(u) is a **Schwartz distribution, not a polynomial** (N(1)=−∞, "infinite genus") [Connes–Consani, arXiv:0903.2024, Thm 2.2/Rem 2.3]. Rules out the Soulé route.

4. **Monoid-scheme rigidity — PROVEN.** Every connected integral F1-scheme of finite type base-changes to a *toric variety* [Deitmar, arXiv:math/0608179, Thm 4.1]. Spec Z is not toric. The one genuinely scheme-like F1 theory provably cannot produce the surface.

5. **Scholze–Clausen no-go — PROVEN, the sharpest.** There is **no Weil cohomology theory with real coefficients for arithmetic curves** simultaneously satisfying Poincaré duality + Künneth + positivity of the diagonal self-intersection [arXiv:2204.02714]. The contradiction is *exactly* between the B3-type positivity and PD⊗Künneth.

**Consequence.** This is why Connes–Consani must use **real-valued (type-II) dimensions** and Deninger must use **infinite-dimensional leafwise cohomology** — both are deliberate evasions of the finite-dimensional real-coefficient hypothesis Scholze rules out. Any object able to carry a 2-dimensional intersection theory over the absolute base *must* be a non-scheme, and even the best such object still lacks the NS lattice and the positivity theorem. The obstruction does **not** bear on RH's truth-value; it constrains only this proof mechanism.

---

## 4. THE ONE DEFINITIONAL GAP — the regularized diagonal self-intersection

**Statement of the gap.** Define a finite Δ·Δ on the square that is simultaneously (i) an intersection number on a genuine geometric object, (ii) valued at the explicit-formula f(1)-coefficient, and (iii) equipped with an NS lattice whose Hodge-index signature makes the primitive part negative-definite.

**Target value — PROVEN/CONSTRUCTED.** On a curve Δ·Δ = 2−2g = χ(C) [CCM, arXiv:math/0703392, eq. 2.44]. The zeta analog is the coefficient of f(1) in the Weil explicit formula — the archimedean/`−log|a|` term, concretely **c = ½(log π + γ)** [Connes RR-strategy slides; CCM eqs. 7.7–7.8]. This *value* is available: as the explicit-formula coefficient, as a Gillet–Soulé Green's-function self-intersection on real arithmetic surfaces, and as a Deninger regularized determinant `det_∞`.

**The four proposed regularizations:**
- **(A) Scaling-site / trace-formula (Connes–Consani):** renders the divergence explicit — the semilocal trace formula carries a genuinely divergent `2h(1)log λ` term [2602.15941 §9.3, "white light" from the regular representation], reinterpreted (2026) as the Abel–Jacobi image of the generic point in the cohomology of a *pair* (Pic~, η̃) over a Picard/Jacobian **monoid**. The pairing D•D′ := ⟨D⋆D̃′, Δ⟩ is defined *via the distribution N(u)*. **CONSTRUCTED (bookkeeping) / positivity CONJECTURAL.**
- **(B) Arakelov / Yuan–Zhang arithmetic Hodge index:** `M̄²·L̄^{n−1} ≤ 0`, negative-definite on the primitive part [arXiv:1304.3538, Thm 1.1/1.3]. **PROVEN — but on real arithmetic surfaces X/Spec O_K, PROVABLY-OBSTRUCTED as a transfer** because `Spec Z ×_{F1} Spec Z` is not among them. Gives the signature for free *once you have the surface*; nothing toward manufacturing it.
- **(C) Zeta-regularization (Deninger):** `det_∞(s−Θ)` and Γ-factors as regularized determinants [Deninger Invent. 1992; arXiv:2410.20758 proves the formula for genuine 3-dim foliated systems]. **CONSTRUCTED (value) / space CONJECTURAL.**
- **(D) Explicit-formula f(1)-coefficient:** not an independent regularization but the *specification of the answer*. **PROVEN (as target).**

**Crux verdict — the gap is RH in disguise.** Decouple the two:
- The **bare value** of Δ·Δ (finite number, no sign) is *already available* and *insufficient* — inert without the surface.
- The **value with the negative-definiteness attached** is **RH-strength**: in Connes–Consani's own dictionary the diagonal inequality is *literally* RH — `D•D ≤ 2(D•ξ₁)(D•ξ₂) ⟺ RH`, equivalently `s(f,f) ≤ 0 ⟺ RH` [RR-strategy slides; essay eqs. 17–18]. A definition of Δ·Δ that *comes with* the correct sign is therefore not weaker than RH.

So: defining Δ·Δ as a number is done; defining it *with the Hodge-index sign* is RH-equivalent. **The definitional gap is not a genuinely weaker attackable sub-problem — it is RH re-encoded.** The 2026 CC paper confirms the frontier is exactly here: they do not define the divergent term as an intersection number; they relocate it to pair-cohomology on a monoid, and still list "**Open problem: suitable definition of H¹**" and "eliminate the divergent term in log Λ" as unsolved.

**Strictly-weaker sub-pieces are already done and, by construction, supply no positivity:** the Frobenius composition law (PROVEN), curve-level Riemann–Roch (PROVEN), Riemann–Roch for `\overline{Spec Z}` [arXiv:2205.01391, PROVEN — but 1-dimensional, does not touch the square], and the archimedean Weil-positivity fragment (CONSTRUCTED, partial). None supplies the sign. The genuinely-open residues — an NS lattice on the square, an H¹ on the square — are *shadowed by Scholze–Clausen*: any pairing that exists satisfying PD+Künneth provably *won't* carry the positivity. So the plausible intermediate targets are likely the ones that provably cannot give the sign.

---

## 5. Is any sub-piece certificate/Telperion-shaped, or is it all deep geometry?

**Overwhelmingly deep geometry, not certificate-shaped.** The load-bearing content — constructing an intersection theory on a semi-ringed topos, a Hodge-index signature theorem, a cohomology H¹ on the square with Serre duality — is open-ended mathematics with no finite verifiable witness. A Telperion/certificate approach needs a bounded object whose validity is machine-checkable (an SOS certificate, an interval bound, a finite polytope, an explicit inequality with a rational witness). Here:

- The **one inequality that would be certificate-shaped** — `D•D ≤ 2(D•ξ₁)(D•ξ₂)` — is exactly RH-equivalent (§4), so it is not a finite certificate; it is a statement about all f in an infinite-dimensional space.
- The **proven pieces that *are* rigorous and finite** (Frobenius composition law Ψ(λ)∘Ψ(λ′)=Ψ(λλ′); curve-level RR `Dim_R H⁰(D)−Dim_R H⁰(−D)=deg(D)`; Yuan–Zhang `M̄²·L̄^{n−1}≤0`) are *already theorems*. They could be *formalized* (a Lean-verification target), but that is checking known mathematics, not producing new certificates that advance the construction.
- The **archimedean Weil-positivity fragment** [2006.13771] is a Hilbert-space trace-formula positivity — the closest thing to a bounded analytic inequality, but it is a proven partial result on the archimedean place, not a reusable certificate that composes toward the square.

Verdict: no sub-piece is Telperion-shaped in the sense of "a finite certificate whose verification advances the surface construction." The residual open problems are definitional/existential (build the lattice, build H¹), not inequalities awaiting a witness. The only certificate-flavored deliverable available is *formalizing the existing theorems* — valuable for rigor, orthogonal to closing the gap.

---

## 6. HONEST ODDS + the single most concrete next step

**Odds.** The surface program is a *specification that has been transported precisely and built partially*, with its core load-bearing piece proven equivalent to RH and its naive routes proven obstructed. Realistic assessment:
- P(the bare-value Δ·Δ regularization is completed and matches the f(1)-coefficient rigorously on the CC square, decoupled from sign): **moderate** — this is genuinely attackable, the 2026 pair-cohomology reframing is progress, and Yuan–Zhang shows the value exists on real surfaces.
- P(a genuine NS lattice with signature (1, ρ−1) on the square is constructed): **very low on the naive route** (Scholze–Clausen obstructs real-coefficient PD+Künneth+positivity); requires a fundamentally non-scheme cohomology whose positivity is *not* inherited from the explicit formula — nobody has one.
- P(this program yields a proof of RH in the foreseeable term): **low** — because the load-bearing inequality *is* RH, so "finishing the surface with its sign" and "proving RH" are the same event.

**The single most concrete next step.** Master and push on **Connes–Consani, *On the Jacobian of Spec Z* (arXiv:2602.15941, 2026), §9.3–9.4** — the divergent-`2h(1)log λ` / "white light" / Abel–Jacobi-of-the-generic-point reframing — read against **Connes' RR-strategy slides** (Step 1: "eliminate the divergent term in log Λ"; "Open problem: suitable definition of H¹"). The concrete construction to attempt is the *bare-value* half of B5, deliberately decoupled from the sign: **define an intersection pairing on the square via the pair-cohomology (Pic~, η̃) that reproduces the explicit-formula f(1)-coefficient c = ½(log π + γ) as a finite number, without claiming positivity.** This is the one piece the sources mark as genuinely open-but-attackable (as opposed to RH-equivalent), it has a fresh 2026 handle (pair-cohomology + Jacobian monoid), and success would be a checkable, publishable advance that does *not* require solving RH. The companion formalization target — verifying the Frobenius composition law and the type-II curve-level Riemann–Roch — is the certificate-shaped side-deliverable.

The complementary route to master, for the positivity side, is **Yuan–Zhang, arXiv:1304.3538** (arithmetic Hodge index): it is the proof that the signature *would* hold given the surface, and understanding precisely why its Green's-function self-intersection cannot be transported to a non-scheme base is the sharpest available map of the obstruction.

---

This determines the object as exactly as the mathematics allows; it does not construct it (that is RH). conjecture1_proved = False.