<!-- ultrathink 6-agent primary-source campaign, 2026-08-30. Determines H1(Pic~,eta~) exactly (spec sheet); does NOT construct it. Crux: bare definition (sans positivity) is strictly weaker than RH; residual risk 4d. conjecture1_proved=False. -->

# H¹(P̃ic(Spec Z), η̃): The Exact Specification of the Cohomology That Would Give the Divergence a Home

**Primary source.** A. Connes, C. Consani, *On the Jacobian of Spec Z*, arXiv:2602.15941v1 (17 Feb 2026), hereafter **CC26**; trace formula from A. Connes, Selecta Math. 5 (1999) 29–106 (CC26 ref **[2]**, **C99**). The load-bearing sentence, verified verbatim: *"This suggests that the relevant cohomology is that of the pair (P̃ic(Spec Z), η̃)."* The symbol `H¹(P̃ic, η̃)` appears **zero times** in the 48-page paper; it is a program label, not a defined object. Everything below specifies constraints the object must satisfy; **it constructs nothing and bears on no proof of RH.**

---

## (1) THE SPEC SHEET — the exact properties H¹(P̃ic, η̃) must have

Derived from the F_q template (all F_q facts **PROVEN**: Grothendieck–Lefschetz, Deligne *Weil I*; Weil for curves) that the arithmetic object must match. Target on the F_q side: `H¹_ét(C, Q_ℓ) ≅ T_ℓ Jac(C) ⊗ Q_ℓ`, dim 2g.

| # | Property | F_q fact (PROVEN) | Requirement on H¹(P̃ic, η̃) | Grade |
|---|---|---|---|---|
| S1 | **Finiteness / trace-class** | dim H¹ = 2g < ∞; Frobenius acts on finite-dim Q_ℓ-space | Trace-class **after the R_λ cutoff** (zeros of ζ_Q are infinite → "finite" means discrete-spectrum/trace-class, NOT finite-dim — a genuine departure) | CONJECTURAL |
| S2 | **Spectrum = zeros** | Frobenius eigenvalues on H¹ = zeros of ζ_C | Spectrum of the symmetry action = nontrivial zeros ρ of ζ_Q | CONJECTURAL |
| S3 | **Symmetry action** | **Frobenius endomorphism** | **C_Q (idèle class group) by TRANSLATION** — explicitly NOT Frobenius (CC26 §1's "decisive departure"); fixed points on singular strata of the monoid supply local terms | CONSTRUCTED (action) / CONJECTURAL (on H¹) |
| S4 | **Poincaré–Serre duality** | Weil pairing H¹×H¹→H²≅Q_ℓ(−1); αᾱ=q; H⁰,H² give poles 1,q | Self-duality forcing ζ_Q(s)=ζ_Q(1−s); archimedean place ∞ plays the Q_ℓ(−1)/weight-normalizer role; H⁰,H² supply ĥ(0),ĥ(1) | CONJECTURAL |
| S5 | **Pair / relative structure** | H¹(C)↪H¹(Jac) via Abel–Jacobi; generic point / diagonal carry H¹ | Genuinely **relative**: cohomology of (P̃ic, η̃) with η̃=Θ̃(η); interesting spectrum localized on the AJ range; the pair's long exact sequence strips the generic-point white light | CONSTRUCTED (geometry) / CONJECTURAL (functor) |
| S6 | **Divergence handling** | polar H⁰⊕H² (1 and qⁿ) sit OUTSIDE H¹; Δ²=2−2g ties them by sign | 2h(1)log λ (coeff 2 = two polar weights 0,2; log λ = regularized degree/volume) = the η̃/H⁰-H²-type piece **excluded from** H¹, leaving Weil's finite explicit formula | CONJECTURAL |

The R_λ = P̂_λ P_λ **double** phase-space cutoff (one factor log λ from |q|≤λ, one from |p|≤λ) is the structural origin of the coefficient **2** (CC26 §9.3 — the cutoff form is **CONSTRUCTED**; the "2" from doubled cutoffs is stated, self-contained re-derivation **UNVERIFIED-here**).

---

## (2) CANDIDATE-THEORY TABLE

Each candidate × the four decisive spec constraints. Grades: **CONSTRUCTED** (built/proven for this role), **CONJECTURAL** (proposed, unbuilt), **OBSTRUCTED** (structurally cannot serve).

| Candidate | S2 zeros-as-spectrum | S1 finite/trace-class | S4 duality | S6 absorbs 2h(1)logλ | Verdict as H¹(P̃ic, η̃) |
|---|---|---|---|---|---|
| **Deninger leafwise/foliated** (arXiv:0709.2801; PROVEN only for geometric foliations, arXiv:2410.20758) | YES by design (flow generator Θ) | **NO** (∞-dim; only via ζ-regularized det) | conjectural | morally YES (archimedean flow) | **CONJECTURAL for Spec Z** — the foliated dynamical system attached to Spec Z **does not exist**; coincidence with the pair object UNVERIFIED (rests on un-refereed arXiv:2508.15971) |
| **Arakelov RR H⁰/H¹** (arXiv:2205.01391) | **NO** | YES (integer-dim) | **YES (Serre, PROVEN)** | **NO** | **OBSTRUCTED — wrong functor.** Not "too small (dim 1)": it is *degree-theoretic* (makes χ(D)=⌈(deg D+log2)/log3⌉−1 work). The zeros are simply **not among its invariants**; claim it carries them = UNVERIFIED/false |
| **Prismatic / q-de Rham / condensed** (arXiv:1905.08229) | NO (no source connects it to ζ-zeros) | YES | YES (crystalline) | **NO** | **OBSTRUCTED — no archimedean place.** Strongest genuine Frobenius, but p-adic/one-prime-at-a-time; the divergence is archimedean/global. Not proposed in any source; UNVERIFIED |
| **Arithmetic-/scaling-site** (arithmeticsite.pdf; arXiv:2207.10419) | **YES** (critical zeros = absorption spectrum, off-line = resonances) | partial (spectral; needs regularization) | **the OPEN "suitable Weil cohomology" — authors' own stated gap** | **YES** (its native trace formula) | **CONSTRUCTED spectral side / CONJECTURAL cohomology — LEADING lineage.** The only family with both the zero-spectrum AND the divergence; lacks exactly the duality/Weil-cohomology H¹(P̃ic, η̃) is meant to be |
| **CC26 pair-cohomology H¹(P̃ic, η̃)** itself | (target) | (target) | (target) | (target) | **UNVERIFIED — proposed, undefined.** No functor, no groups, no finiteness/duality theorem; modality "suggests" |

**Closest candidate and exactly what it lacks.** The **arithmetic-/scaling-site lineage (Candidate 4)**. It is the *only* published family that natively produces both the zeros-as-spectrum (S2) and the 2h(1)log λ divergence (S6) — H¹(P̃ic, η̃) is best read as its proposed completion. **What it lacks:** precisely S4 — a Weil cohomology with Poincaré–Serre duality making the trace formula a genuine Lefschetz theorem. The authors themselves flag this as the open problem ("the definition of a suitable Weil cohomology which would allow one to understand certain results as a Lefschetz formula"). The failures across candidates are **structurally disjoint** — Arakelov has S4 but not S2; prismatic has Frobenius but no archimedean place; Deninger has the flow but not S1 and no space; the scaling site has S2 but not S4 — so **no working theory can be glued from the four**, and the object does not exist in the published literature.

---

## (3) THE DIVERGENCE, HOMED

**The formula (CC26 eq. (20), §9.3, verbatim origin C99):**

> Trace(θ(h) R_λ) = 2 h(1) log λ + Σ_{v∈S} ∫′_{Q_v^×} h(u⁻¹)/|1−u| d*u + o(1).

CC26 verbatim: *"The divergent term 2h(1) log λ signals the presence of the white light coming from the (trace of the) regular representation... this is the contribution of the image of the generic point η by the Abel-Jacobi map."*

**Origin — PROVEN (C99):** 2h(1)log λ is a cutoff artifact of the **regular representation** — proportional to h(1) (test function at the identity of C_Q = the diagonal, the piece the regular representation contributes), and analytically the **trivial-character continuous-spectrum / s=1 pole** contribution (= ĥ(0)+ĥ(1) in Weil's explicit formula eq. (17)). All three descriptions — regular representation, trivial character, pole at s=1 — are the **same phenomenon**.

**Why it attaches to η̃ — CONSTRUCTED, and this is the non-circular anchor:** The Abel–Jacobi map (CC26 **Def. 2.12**) sends Θ(η)=[Z] (generic point ↦ trivial divisor), and **Theorem 7.9 (PROVEN): the fiber over the generic point F_η ≅ C_Q** — the *full* idèle class group. Closed-point fibers are the *ramified* mapping-tori C_Q/(local units) (Rmk 7.10). So closed points p, ∞ contribute the **finite** transverse traces ∫′ h(u⁻¹)/|1−u| (isotropy Q_v^×, via the §9.2 delta-calculus ∫δ((u−1)x)dx = 1/|u−1|); η̃, whose fiber is the un-quotiented C_Q, carries the **regular representation = the divergence**. The attachment is **forced by an independently-proven identification (fiber=C_Q)**, not chosen to fit the answer.

**How it must sit in the relative exact sequence (CONJECTURAL specification).** The pair's long exact sequence must be the vehicle:

> ⋯ → Hⁱ(η̃) → Hⁱ(P̃ic) → Hⁱ(P̃ic, η̃) → Hⁱ⁺¹(η̃) → ⋯

with **Hⁱ(η̃) carrying exactly the divergent regular-representation/white-light continuum** (fiber = C_Q). Three requirements this forces on H¹:

1. **Absorption.** The divergent 2h(1)log λ must be **exactly the image of the connecting/restriction map to η̃** — the entire obstruction to Hⁱ(P̃ic)→Hⁱ(η̃) being trace-class — so that the relative group Hⁱ(P̃ic, η̃) is the finite complement.
2. **Renormalization identity.** lim_{λ→∞}[Trace(θ(h)R_λ) − 2h(1)log λ] = Σ_v ∫′ h(u⁻¹)/|1−u| d*u must be the trace on the relative group. (This subtraction is **PROVEN well-posed** — an explicit, h-linear, character-independent counterterm.)
3. **Middle-degree.** The nontrivial zeros ρ live in **degree 1**; the polar ĥ(0)+ĥ(1) are pushed into the H⁰/H²(η̃) boundary hosting the pole.

**Slogan (CONJECTURAL):** H¹(P̃ic, η̃) is H¹(C) ≅ T_ℓ Jac ⊗ Q_ℓ after the white light of η — the non-compact generic fiber C_Q — has been divided out. **Candidate substrate (CONSTRUCTED, CC26 Thm 9.1 / arXiv:2501.06560):** the sheaf O⋊G_m on Spec Z with stalk-at-η = the global cross-product S(A_Q)⋊Q^×; the natural realization is relative Hochschild/cyclic homology of (global sections vs. stalk-at-η).

**One unresolved fork (UNVERIFIED in source):** whether the "2" in 2h(1)log λ is dim H⁰+dim H² (two polar weights 0,2, staying outside H¹) or the *whole* generic-point continuum to be relativized. Both are consistent with "2"; they differ on what η̃ is. A construction must pin this down.

---

## (4) THE CRUX — is DEFINING H¹ (sans positivity) genuinely weaker than RH, or circular?

**Answer (split verdict, per the SKEPTIC):**

**(4a) The minimal problem — define a relative cohomology + Lefschetz trace reproducing Weil's explicit formula after absorbing 2h(1)log λ, with NO eigenvalue-location claim — is STRICTLY WEAKER than RH.** Grade **CONJECTURAL as construction, PROVEN-weaker-by-template.** It is the exact analogue of "build H¹_ét(C) + prove Grothendieck–Lefschetz," which over F_q is **unconditional** and does **not** give RH. RH-for-curves is the *additional* Weil/Deligne bound |α|=q^{1/2} — a positivity/weight statement about eigenvalues on the *already-constructed* H¹.

**(4b) The divergence-absorption is POSITIVITY-FREE (SKEPTIC, decisive).** Homing 2h(1)log λ is homological algebra — a mapping cone, a long exact sequence, a trace-class endomorphism — plus an explicit counterterm subtraction. It requires **no inner-product positivity**. The SKEPTIC's decisive evidence: **Weil positivity appears NOWHERE in arXiv:2602.15941** (0 occurrences; every "positiv" string is "positive integers/reals"). The paper attaches the divergence to η̃ and stops; it makes **no** claim the resulting H¹ has eigenvalues on the critical line. If merely defining the pair forced RH, the paper would be claiming RH — it explicitly is not. RH re-enters only as the **separate** positivity/self-adjointness statement (Weil positivity of the finite remainder Σ_v ∫′), which lives in C99 and the archimedean-place papers (arXiv:2006.13771, arXiv:2310.18423), **not** here.

**(4c) Is it circular / reverse-engineered? PARTLY — a NAME, but NOT vacuously circular (SKEPTIC).** Damning-but-fair: the object is introduced *by its required output* (sentence order: "we interpret the divergent term as η̃'s contribution. This *suggests* the relevant cohomology is the pair"), there is no functor, no group is computed, no duority theorem is stated, and the modality is the weakest possible ("suggests"). **But** three ingredients are independently CONSTRUCTED and make the name non-vacuous: (i) the boundary η̃ is a *specific* subspace with **fiber F_η≅C_Q PROVEN (Thm 7.9)** — the divergence's attachment is *forced*, not chosen; (ii) the finite local terms are independently realized as transverse traces (§9.2); (iii) a concrete substrate exists (Thm 9.1). So it is a genuine *target*, at the same epistemic stage as "the conjectural Weil cohomology over Z" — a real desideratum, not yet a theory.

**(4d) The load-bearing residual risk (SKEPTIC, UNVERIFIED).** "Strictly weaker" holds for a *bare vector-space-with-action*. But there is an unresolved risk of **hidden RH-equivalence**: any construction natural enough to be **finite/trace-class (S1) AND self-dual realizing s↔1−s (S4) AND C_Q-equivariant (S3)** might *only exist* if the spectrum is already on the critical line — the way "the operator is self-adjoint" secretly encodes eigenvalue location. The F_q template is reassuring (there the construction is unconditional), but the archimedean case has **no compact Jacobian**: the generic fiber C_Q is **non-compact**, giving a continuous/white-light spectrum, so the analogy is not airtight. No source resolves this.

**Net crux verdict:** Defining H¹(P̃ic, η̃) *sans positivity* is a **genuine, attackable construction problem strictly weaker than RH** at the level of a bare space-with-action — and the paper's total silence on Weil positivity confirms the bare definition does **not** smuggle in RH. **The gap:** it may become RH-equivalent the moment you demand the duality realizing s↔1−s hold on a trace-class C_Q-equivariant space (4d). **That gap is the actual open problem.**

---

## (5) THE SINGLE MOST CONCRETE NEXT STEP

**Master, then attempt to define:** the **relative cyclic/Hochschild homology of the sheaf O⋊G_m on Spec Z relative to its stalk at the generic point** — i.e. the mapping cone of [global sections S(A_S)⋊Z_S^× → stalk-at-η S(A_Q)⋊Q^×], as constructed in **CC26 Thm 9.1 + arXiv:2501.06560 ("Knots, primes and class field theory," ref [5])**. This is the unique CC26-native substrate in which (i) η̃'s contribution is literally the stalk-at-η (global algebra, carrying C_Q's regular representation), (ii) the relative object is a well-defined mapping cone, and (iii) the scaling/C_Q-action already acts. The concrete deliverable to attempt: **define HC/HH of this pair, prove the connecting map absorbs exactly 2h(1)log λ, and check the relative trace equals Σ_v ∫′** — S1, S5, S6 without touching S4/positivity. Prerequisite mastery: **C99 (Selecta 1999)** for the trace formula and **arXiv:2207.10419** ("Hochschild homology, trace map and ζ-cycles") for the cyclic-homology-as-Frobenius-analogue machinery.

---

This determines the object as exactly as the mathematics allows; it does not construct it. conjecture1_proved = False.