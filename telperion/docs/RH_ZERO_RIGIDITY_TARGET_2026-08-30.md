<!-- ultrathink multi-agent campaign (7 agents, adversarially verified), 2026-08-30. Builds on RH_BARRIER_CRACK. conjecture1_proved=False. -->

# RH's real target: is there an unconditional zero-rigidity that is NOT a rename of RH?

*A terrain map of the gap between "unconditional rigidity of the zeta zeros" and "sign-definiteness of the Weil prime block." Grades: PROVEN / PARTIAL / CONDITIONAL(RH) / CONJECTURAL / OPEN. Lead-liveness: ALIVE / SEMI-ALIVE / MIRAGE.*

---

## 1. The precise target restated

RH is equivalent to **Weil positivity** of the explicit-formula quadratic form (Weil 1952; Bombieri, *Remarks on Weil's quadratic functional*, Rend. Lincei 2000):

$$W(g,g) \ge 0 \quad \forall\, g \;\Longleftrightarrow\; \text{RH}.$$

For an even test function $g$ with transform $h$, the explicit formula reads
$$\sum_\rho h(\gamma_\rho) = \underbrace{\hat g(0)+\hat g(1)}_{\text{polar}} + \underbrace{\frac{1}{2\pi}\!\int h(t)\tfrac{\Gamma'}{\Gamma}(\tfrac14+\tfrac{it}{2})\,dt}_{W_\infty}\; -\; \underbrace{2\sum_{n\ge2}\tfrac{\Lambda(n)}{\sqrt n}g(\log n)}_{W_{\text{prime}}}.$$

On a finite basis this is a Gram matrix $M = M_{\text{arch}} + M_{\text{prime}}$. **Connes–Consani (arXiv:2006.13771, Selecta Math. 27 (2021)) proved $M_{\text{arch}} \succeq 0$ unconditionally** via prolate-spheroidal / Toeplitz compression. The prime block
$$(M_{\text{prime}})_{ij} \sim \sum_{n,m\ge2}\tfrac{\Lambda(n)\Lambda(m)}{\sqrt{nm}}\,g_i(\log n)\,g_j(\log m)$$
is the **sign-indefinite core**, and its positivity **is** RH.

**The Brualdi–Goldwasser template we are testing against.** BG closed because Heilmann–Lieb (*Theory of monomer-dimer systems*, Comm. Math. Phys. 25 (1972)) supplies an **unconditional** Lee–Yang / no-phase-transition theorem → strong spatial mixing → **diagonal dominance** $2\sum|\text{off-diag}| < |\text{diagonal}|$ uniformly in system size. The load-bearing property: an unconditional decay-of-correlations that is **strictly weaker than "BG holds" yet sufficient for it**. The question of this map: **does any unconditional zero-rigidity for $\zeta$ sit in that same box — weaker than RH, yet sufficient — or does every sufficient rigidity collapse into RH itself?**

---

## 2. The unconditional-rigidity landscape, graded

| Lead | Statement grade | Unconditional? | A mixing/decay statement? | Reaches $M_{\text{prime}}$ sign-definite? | Liveness |
|---|---|---|---|---|---|
| **Zero-density (Ingham; Guth–Maynard 2024)** | PROVEN | Yes | No — population *count* bound | No — self-capped at density hyp. | MIRAGE for core / ALIVE in-domain |
| **Pair correlation $F(\alpha)$** (Montgomery 1973) | full asymp. CONDITIONAL(RH); $F(\alpha)\ge0$ PROVEN | only the nonneg. part | **Yes — the right object** | No — useful $(1{-}\alpha)$ half is RH-conditional (circular) | SEMI-ALIVE |
| **Unconditional Montgomery** (Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, arXiv:2306.04799, 2023) | PROVEN under weaker-than-RH hyp. | Yes | Yes, but **$\beta$-agnostic by design** | No — carries no Re$(\rho){=}\tfrac12$ content | SEMI-ALIVE |
| **Proportion on line $\kappa\ge5/12$** (Levinson 1974; Conrey 1989; Pratt–Robles–Zeindler–Zaharescu, *Res. Math. Sci.* 2020) | PROVEN | Yes | No — subset *location* | No — $\kappa<\tfrac12$, mollifier ceiling | ALIVE-as-rigidity / MIRAGE-as-route |
| **Selberg $S(T)$ CLT** (Selberg 1946) | PROVEN | Yes | **Yes — Gaussian, unconditional** | No — blind to Re$(\rho)$ | SEMI-ALIVE |
| **Moments $I_k(T)$** (Harper, Forum Math. Pi 8 (2020); RSound) | PROVEN $k\le2$; sharp $k>2$ CONDITIONAL(RH) | in-range only | No — magnitude only | No — location-agnostic; strong range is circular | MIRAGE for core |
| **RMT/log-gas rigidity** (Erdős–Yau–Yin 2012; Bourgade–Erdős–Yau 2014) | PROVEN | Yes — **for matrices, not $\zeta$** | Yes | No — zeta log-gas is CONJECTURAL (Montgomery–Odlyzko) | SEMI-ALIVE → MIRAGE |
| **Ford–Zaharescu repulsion** (arXiv:1305.2520, 2015) | PROVEN | Yes | Yes — but one-sided, level-1 | No — too thin, two-point only | ALIVE-foothold |
| **Vinogradov–Korobov ZFR** (1958) | PROVEN | Yes | No | No — log-thin, far from $\tfrac12$ | SEMI-ALIVE |
| **Matomäki–Radziwiłł + Tao** (Ann. Math. 183 (2016); Forum Math. Pi 4 (2016)) | PROVEN | Yes — **strongest uncond. cancellation** | Yes | No — $\mu/\lambda$, log-averaged, wrong metric | **ALIVE (wrong metric)** |

**Three structural failure-modes** organize the whole table. Every unconditional rigidity is one of: **(a) a one-sided population/count bound** (zero-density, $\kappa\ge5/12$) that controls *how many* zeros misbehave but never certifies *cancellation*; **(b) a fluctuation/CLT blind to the real part** (Selberg $S(T)$) — controls vertical distribution of $N(T)$, invisible to the horizontal $\beta$ that makes $M_{\text{prime}}$ indefinite; or **(c) the genuinely-right mixing object proven only conditionally on RH** (Montgomery pair correlation), i.e. circular. Nothing bounds the off-diagonal prime-correlation *in absolute value below the diagonal*.

---

## 3. THE CRUX: sufficient-but-not-RH, or does everything collapse?

The load-bearing distinction. Test each candidate: is it provably **weaker** than RH (∃ model with ¬RH ∧ C) **yet** provably ⟹ RH? That is the SSM box.

| Candidate | Sufficient for RH? | Weaker than RH? | Classification |
|---|---|---|---|
| Weil positivity $W(g,g)\ge0$ | YES (equivalence) | **NO — proven EQUIVALENT** | **RENAME** |
| Li positivity $\lambda_n\ge0$ (Li 1997; Bombieri–Lagarias, JNT 77 (1999)) | YES | **NO — EQUIVALENT** | **RENAME** (BL identity is an algebraic tautology over any multiset symmetric about Re$=\tfrac12$; feeding "rigid zeros" in *assumes* the symmetry) |
| de Branges positivity | YES | **NO — EQUIVALENT** | **RENAME** |
| **$M_{\text{prime}}$ sign-definiteness** (the target) | YES | **NO — it IS $W\ge0$ restricted** | **RENAME** — the object the program wants to make positive is *definitionally* the RH-equivalent block |
| Unconditional Montgomery (2306.04799) | NO (⅔-simple-zeros only) | **YES, genuinely** | WEAKER but **INSUFFICIENT** |
| $\kappa\ge5/12$ | NO ($\kappa<1$) | YES | WEAKER, INSUFFICIENT (mollifier ceiling, Conrey–Ghosh/Farmer) |
| Guth–Maynard density | NO | YES | WEAKER, INSUFFICIENT (self-caps at density hyp.) |
| Selberg $S(T)$ CLT | NO (blind to Re) | YES | WEAKER, INSUFFICIENT (wrong axis) |

**Finding (skeptic-endorsed): the SSM-shaped middle box — weaker ∧ sufficient — is EMPTY in the vetted literature.** Every candidate that is *sufficient* is a **proven rename** of RH; every candidate that is *genuinely weaker* is **proven or evidently insufficient**. This clean dichotomy is precisely where the BG analogy breaks: SSM landed in the middle box; nothing for RH does.

**Why the off-diagonal necessarily re-encodes RH.** The prime block on a Fourier window is
$$\Big|\textstyle\sum_n \Lambda(n)\,n^{-1/2-it}g(\log n)\Big|^2,$$
the modulus-squared of a Dirichlet-polynomial approximation to $-\zeta'/\zeta(\tfrac12+it)$. Its size is **not an independent input** — it is governed by the zeros. Montgomery's own evaluation ($F(\alpha)\sim(1-\alpha)$) requires collapsing $\sum_\rho$ **using $\beta=\tfrac12$** — the collapse *is* the use of RH. Hence:
- **Fixed bounded cone:** finite explicit matrix, positivity is a checkable SDP, and it **holds** (Bombieri–Lagarias truncations, verified low-dimensionally). Grade **PARTIAL / SEMI-ALIVE** — the analog of BG's *local* sub-inequalities.
- **Unbounded support (what RH needs):** dominating the off-diagonal ⟺ bounding $\zeta'/\zeta$ off the zeros at critical-line strength ⟺ forcing zeros onto the line. **Diagonal dominance ⟺ RH.** The only unconditional bound available is Vinogradov–Korobov — orders of magnitude too weak.

**The deepest disanalogy (the reason the box is empty).** BG's SSM is a proven property of a **real Gibbs system**: Heilmann–Lieb's Lee–Yang theorem (no complex zeros off the axis, no phase transition at any density) is an unconditional *gift*. Over ℚ the "log-gas of zeros" is a **heuristic**: no proven Gibbs measure (Montgomery–Odlyzko sine-process is CONJECTURAL — Lewin, J. Math. Phys. 63 (2022)), no confining potential, no self-adjoint operator (Hilbert–Pólya OPEN), and the zeta analog of "no phase transition" (all zeros on a line) **is RH itself**. You cannot import decay-of-correlations from a Gibbs measure you have not proven exists. SSM inherited its unconditionality from Heilmann–Lieb Lee–Yang; **there is no unconditional Lee–Yang to inherit from over ℚ.**

**Verdict: effectively a NO-TRANSFER theorem.** Every rigidity proven sufficient is proven equivalent to RH; every genuinely weaker rigidity is insufficient. This is a valuable finding, not a failure — it says the BG closure route, *as a general mechanism*, does not exist over ℚ, and it explains structurally why. Two caveats keep it from being a *proven* no-transfer: (i) the identical program **succeeds over $F_q$** (§4), so a sufficient-but-non-circular rigidity provably exists in the parallel universe — the obstruction is the *absence of a base object*, not a logical impossibility; (ii) one narrow escape hatch is not known-RH-equivalent *and* not known-insufficient (§6).

---

## 4. The missing $F_q$-Frobenius ingredient, and the most-alive program to manufacture it

Over $F_q$, RH is a **theorem** (Weil 1948 curves; Deligne, *Weil II*, Publ. IHÉS 52, 1980). Four load-bearing facts, each with **no unconditional ℚ-analog**:

| $F_q$ ingredient (all PROVEN) | ℚ-side status |
|---|---|
| **(I) Frobenius on finite-dim étale cohomology** — zeros ARE eigenvalues (Grothendieck, SGA 4/5) | **No unconditional analog.** No cohomology whose finite-dim automorphism has the zeta zeros as eigenvalues. This is the true missing Frobenius. |
| **(II) Poincaré/Weil self-duality** = functional equation | **PROVEN** (Riemann 1859; now also as Serre duality on $\overline{\mathrm{Spec}\,\mathbb Z}$, Connes–Consani R-R, arXiv:2205.01391). The one block ℚ owns. |
| **(III) Hodge index / Castelnuovo–Severi on $X\times X$** — the actual bound | **The gap.** $M_{\text{arch}}\succeq0$ PROVEN (2006.13771); $M_{\text{prime}}$ = a signature/index positivity on $\mathrm{Spec}\,\mathbb Z\times_{\mathbb F_1}\mathrm{Spec}\,\mathbb Z$ is **OPEN**. |
| **(IV) Weil II + big monodromy** — equidistribution/rigidity (Katz–Sarnak 1999) | ℚ GUE-statistics (Montgomery–Odlyzko–Rudnick–Sarnak) are **CONDITIONAL(RH)** and give statistics, not the line. |

The obstruction is not one lemma: it is the **absent base $\mathbb F_1$** that would make $\mathrm{Spec}\,\mathbb Z$ a curve and $\mathrm{Spec}\,\mathbb Z\times_{\mathbb F_1}\mathrm{Spec}\,\mathbb Z$ the surface carrying the indefinite-but-signature-controlled intersection form.

**Most-alive program: Connes–Consani $\mathbb F_1$ / absolute geometry.** Graded trajectory:
- $M_{\text{arch}}$ positivity — **PROVEN** unconditional (2006.13771, 2021).
- Riemann–Roch + Serre duality on $\overline{\mathrm{Spec}\,\mathbb Z}$ — **PROVEN** (arXiv:2205.01391, 2023) — but on a *curve-like 1-dim object* (gives II, not III).
- The surface $\mathrm{Spec}\,\mathbb Z\times_{\mathbb F_1}\mathrm{Spec}\,\mathbb Z$ + Fargues–Fontaine bridge — **PARTIAL** (arXiv:2606.06604, 2026): constructs the surface, computes the diagonal self-intersection ($=\log 2\pi$), but does **not** prove the Hodge-index *signature inequality* that would drive RH. *(Caution: an automated read claimed "Theorem 3.1 proves Hodge-index unconditionally"; I could not verify a signature inequality as opposed to a positive self-intersection number — grade it OPEN.)*
- The decisive lemma (Hodge-index signature on the surface / Connes–Consani–Moscovici convergence rate) — **OPEN**.

Runner-up: **Deninger** foliated Lefschetz trace formula — the geometric trace machinery is now **PARTIAL/PROVEN** in special cases (regularized-determinant formula, arXiv:2410.20758, 2024), but the *arithmetic* dynamical system whose spectrum is the zeros is **CONJECTURAL**. **SEMI-ALIVE.**

---

## 5. Telperion applicability: is any piece cert-shaped?

**Honest split.**

- **Cert-shaped (genuine PSD / finite diagonal-dominance witnesses):** the **explicit-formula SDP / Fourier-optimization framework** (Chirre–Gonçalves–de Laat, Adv. Math. 361 (2020); Carneiro–Chandee–Chirre–Milinovich, Crelle 786 (2022); Carneiro–Milinovich–Ramos, Math. Comp. 2024) reduces Guinand–Weil extremal problems to **convex/SDP feasibility with checkable dual positivity certificates**. The **truncated Weil/Li blocks** (Bombieri–Lagarias) are finite explicit Hermitian matrices whose PSD-ness is machine-checkable, and low-dimensional blocks *are* PSD. **This is the one place Telperion could actually certify something** — a finite $M_{\text{arch}}+M_{\text{prime}}$ block on a fixed bounded cone, as a PSD / diagonal-dominance witness, exactly BG-shaped.

- **The load-bearing catch:** every such certificate is **bounded-support / one-sided** (upper bounds on off-line counts, lower bounds on line-proportion). RH needs **unbounded-support global sign-definiteness**, where the prime sum becomes indefinite and **no finite certificate is known to close** — the direct analog of BG *before* the mixing lemma: you can certify bounded-degree envelopes, but the boundary (there $\rho(A)\to1$; here unbounded-support prime oscillation = $\zeta'/\zeta$) escapes every finite certificate. The **chaining uniform-in-support** is the missing "Frobenius," and it is **pure analysis / arithmetic**, not certificate-shaped.

**Verdict:** Telperion can host the *finite local* diagonal-dominance certificates (real, non-circular, already known PSD) and could mechanize the SDP-dual search — but it **cannot** supply the uniform-in-support lever, because that lever does not exist as a certificate; it would have to be *proven* (a new unconditional arithmetic mixing input), and any certificate reaching the needed strength would itself become RH-equivalent.

---

## 6. The single most promising bold direction, with honest odds

**Direction:** upgrade **Matomäki–Radziwiłł / Tao** short-interval multiplicative cancellation from **log-density-averaged $\mu/\lambda$ correlations** to a **pointwise $\Lambda\Lambda$ off-diagonal bound, weighted by $(nm)^{-1/2}$, on a growing cone**, strong enough to be dominated by the Connes–Consani archimedean diagonal.

**Why it is the one live hatch:** it is the *only* candidate that is **not known-RH-equivalent** (MR is a genuine unconditional theorem that assumes no RH and carries real cancellation) **and not known-insufficient** (if it reached critical-line pointwise strength it would dominate $M_{\text{arch}}$). Every other lead is proven-rename or proven-insufficient.

**Honest odds: low.** Three reasons. (i) MR gives $x^{o(1)}$ savings in the **wrong metric** — multiplicative $\mu/\lambda$, log-averaged, not pointwise $\Lambda\Lambda$; no known transfer exists. (ii) The **circularity trap of §3**: if the upgrade *did* reach the needed pointwise $(nm)^{-1/2}$ strength, it would bound $\zeta'/\zeta$ off the zeros and thereby likely *become* RH-equivalent — the hatch may close back into a rename the moment it is forced open. (iii) It requires new analytic technology that does not currently exist. Call it a **lead worth one probe, not a route** — SEMI-ALIVE, ~single-digit-percent plausibility of even a partial non-circular transfer.

**The one concrete next lever, if one is pursued:** formalize the finite bounded-cone $M_{\text{arch}}+M_{\text{prime}}$ block as an explicit PSD/diagonal-dominance certificate (Telperion-hostable, §5), then attempt to **prove a uniform-in-cone growth bound on the $\Lambda\Lambda$ off-diagonal from MR-type input alone** — i.e., test whether *any* unconditional cancellation survives the $(nm)^{-1/2}$ weighting as the cone grows. If it plateaus (expected), that is itself a clean, publishable **no-transfer measurement** pinning exactly where the archimedean diagonal loses to the prime off-diagonal — the RH analog of measuring the BG tie at $\rho(A)\to1$.

---

*This maps the target; it does not prove RH.* **conjecture1_proved = False.**