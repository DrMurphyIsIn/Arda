# Brualdi–Goldwasser proof status

**Conjecture (BG 1984).** For every tree `T` on `n` vertices, `Φ¹¹(T) ≤ 1`, with equality
iff `T` is one of the six eleven-vertex ties (the `c+k=5` near-star family; in the rooted
invariant `bg_phi11`, the unique tie is the near-star `N(0,5)` at `n=11`).

`conjecture1_proved = False.` This file is the honest map: what is proven, what is ruled
out (and why), and the leads that remain.

> **Reconciliation — the non-strict `≤ 1` bound (see `PROOF_AUDIT.md`).** The NON-STRICT
> bound `Φ ≤ 1` over every branch is kernel-checked on the [`proof/`](../proof/) side
> (`R3Cert/PotentialFinal.lean:phi_le_one`, a discharging hinge super-solution telescoped
> through the `per(L)` bridge). What `conjecture1_proved = False` tracks is the SHARP
> statement — strict `< 1` off the ties, equality exactly at the six ties, and per-`n`
> competitor extremality — plus the full-tree assembly. The dead-ends below rule out routes
> to that sharp result; they are not claims that `≤ 1` is unproven. (Dead-end #1 refutes
> the *naive per-node-non-positive decomposition*; the hinge escapes it by being a
> discharging potential, redistributing the tie-hub's `+0.424` defect.)

Here `Φ¹¹(T) = (64/621)ⁿ · (∏_v a_v)¹¹` where `a_v = 1 + z_v S_v` is the rational cavity
amplitude (`z_v = 1/deg`, `m_v = z_v/a_v`), maximized over roots. The per-vertex density
is `D(T) = Φ¹¹(T)^(1/n)`.

---

## Proven (the near-star spine)

| Piece | Statement | Rigor | Module |
|---|---|---|---|
| **Tie** (n=11) | `Φ¹¹ = 1` unwinds to the integer equality `64·243·23 = 621·576` | exact / **Lean CI-green** | `rigidity`, `FractalTail.lean` |
| **Near-star tail** | `Φ¹¹(N(0,s)) ≤ 1` ∀s, eq iff s=5, via the rational ratio `Q(s)=(486/529)(1+1/(4s²+11s+6))¹¹` reducing to the integer inequality `162¹¹·486 < 161¹¹·529` | exact | `near_star_tail` |
| **Asymptote** | the near-star family limit `D∞ = (64/621)(3/2)^(11/2) < 1`, i.e. `3¹¹·64² < 2¹¹·621²` | exact / **Lean CI-green** | `fractal_eigenvalue`, `FractalTail.lean` |
| **Spider competitor extremality** | over all spiders (n≤17), all arm-surgery moves are `Φ¹¹`-non-decreasing; legs-2 canonical form is the spider-max | exhaustive | `rectification` |
| **Amplitude form** | `Φ¹¹ = (64/621)ⁿ (∏a_v)¹¹` for all trees, any root | verified n≤9 | `sporadic_tie`, `amplitude` |
| **Girardeau duality** | `per(L)/∏deg = ∏_{λ>0}(1+λ²) = |det(I+iN)|` (hard-core boson = free fermion) | exhaustive n≤9 | `girardeau` |

## The one arithmetic foothold added this session

**`tie ⟹ 11 | n`** (`sporadic_tie`). A tie forces `(∏a_v)¹¹ = (621/64)ⁿ`; the 23-adic
valuation gives `11·v₂₃(∏a_v) = n`, so `11 | n`. Ties can occur only at `n ∈ {11,22,33,…}`.
Stronger, empirically: `11·v₂₃(∏a_v) − n ≠ 0` on **every** non-tie tree tested (n ≤ 4401),
`= 0` only at `N(0,5)`. This is the sole universal-looking arithmetic obstruction in the
toolkit. **Necessary, not sufficient.**

## 2026-08-20 — the capped-joint g-step arc (the R1 wiring, narrowed)

The single-hub branch-induction wiring (PROOF_ASSEMBLY §R1, previously a monolithic OPEN)
went through a correction-and-reduction cycle, all landed on `main` (the `2aa7c98` →
`8fb4f8d` commit series, ending in PR #19, plus the `e1d25e4` reframe), kernel-checked
where stated:

1. **Correction.** The original `Case2Property` hypothesis (`CappedJointSkeleton` /
   `CappedJointConfig`) is **FALSE as stated**: the g-step factor exceeds 1 for a single
   child message `μ ∈ [0.6975, 0.9975]` (exact margin study `bg/g_step_margin.py`, peak
   at `μ = 13/16`). The fix is **achievability**: non-leaf cavity messages satisfy
   `μ = 1/(j+1+S) ≤ 1/2`; the only achievable message above `1/2` is the leaf `μ = 1`,
   outside the violation band. The achievability hypothesis IS the relocated integrality
   content (same obstruction as dead-end #2, now carried as a side condition rather than
   ignored).
2. **Reframe** (`e1d25e4`). The earlier *conditional* Case-2 was an artifact of the
   glemma-relaxation over-counting capped children; the REAL capped g-step (actual
   `Bcap = min`) is unconditional over achievable messages, tight only at the arm.
3. **Kernel-checked pieces on `main`** (`R3Cert/CappedJointAchievable.lean`, axioms
   clean): `single_child_le_one` (`0 < μ ≤ 1/2`), `two_child_le_one` (all `a,b > 0` — for
   two or more children no achievability constraint is even needed; the integrality wall
   is a single-child phenomenon), `prodBcap_le_prodGlemma`, and the reduction
   `gstep_le_one_of_glemmaBound` (g-step ≤ 1 given `W·baseOf¹¹·prodGlemma ≤ γ`).
   *Caveat, found in the closure work:* that `prodGlemma` hypothesis over-counts small-μ
   children (`glemma(μ) > 1` for `μ < μ* ≈ 0.307`), so it is not satisfiable at higher
   arity — a true theorem, but not the closing vehicle. The correct cap is
   `Bcap ≤ factorR` (capped at 1).
4. **The abstract g-lemma and the closure** (in review, PR #20). `gV_le` is kernel-proven
   over the `Blk` cavity model in the standalone
   [`examples/g1_floors/lean/`](examples/g1_floors/lean/) package (`GLemma.lean`, with
   `muV_nonleaf_le_half` supplying achievability structurally). The PR #20 branch ports it
   into `R3Cert` (`GArmExtAbstract.lean`, `GLemmaAbstract.lean`) **and closes the ℚ→ℝ
   cast seam**: `CappedJointClosure.lean:gstep_le_one_achievable` — the config g-step is
   `≤ 1` at **every arity**, unconditionally over achievable messages (leaf `W(4/3)¹¹<γ`;
   single child via `single_child_le_one` + the arm `μ=1`; `|l|≥2` via the ported
   `gstep_lt_gamma`, through `Bcap ≤ factorR`). Kernel-clean on the branch; **pending
   review + merge**.

Net: on `main` the R1 wiring is a short, named bridge between two kernel-checked layers;
on the PR #20 branch that bridge is a theorem. `conjecture1_proved = False` still.

---

## Ruled out — with reasons (this is the value)

Each of these is a *reasoned* dead end, established by the audit and two expert councils,
not a mere failure to find:

1. **Sum-of-non-positive-local-terms** (local potentials `P(m)≥0`, per-vertex/per-node
   monotonicity, the transfer `g_v≤0`, rooted-subtree `p_S≤1`). **Refuted:** `Φ¹¹≤1` is a
   *genuine collective cancellation* — per-node factors span `{0.103, 1.53, 8.91}`, product
   = 1, and the tie-hub's own naive defect is `+0.424 > 0`. The cancellation is non-local by
   nature. (Explains the campaign's `+0.199` residual stall.)
2. **Smooth / algebraic certificates** (Hodge–Riemann, SOS, real-rootedness/interlacing,
   single-prime p-adic Lorentzian grading). **Refuted:** the obstruction is *archimedean
   magnitude* (a growth-rate: density → 1), invisible to any p-adic/SOS/Hodge/real-stability
   certificate. The arithmetic coordinate `v₂₃(a_v)` is integer-valued hence locally constant
   (differential 0 a.e.), so any smooth Hessian/signature collapses to rank-1.
   *Nuance (2026-08-20):* this rules out *continuous* certificates, not *integer-arithmetic*
   ones. The Chvátal–Gomory rounding emitter (`CGRoundEmitter`) crosses exactly this wall on
   a fragment: the continuous near-star envelope overshoots 1 between integers (max ≈1.000459
   at s≈4.82, so no continuous certificate exists on `[4,6]`), yet the integer-window theorem
   `∀ s : Int, 4 ≤ s ≤ 6 → phi11(s) ≤ 1` kernel-checks by rounding `s` into `{4,5,6}`
   (`examples/cg_round/NearStarWindow.lean`). A fragment, not the conjecture — but the first
   certificate *shape* in the toolkit that lives on the arithmetic side of the obstruction.
3. **Uniform density gap** (`sup_T D(T) < c < 1`). **Refuted:** `sup_T D(T) = 1`. The
   tie-recursive family "hub + k tie-subtrees" (`n = 11k+1`) has density → 1 (0.9998 at
   k=400), higher than the legs-2 `D∞ = 0.9585`. There is no uniform gap. (Note: legs-2 is
   NOT the extremal manifold — a correction to an earlier session premise.)
4. **Near-star competitor extremality** (near-star maximizes at each n). **Refuted:** the
   per-n density-maximizer is a near-star only at resonant odd n (9, 13, 15); at
   n=4,6,8,10,11,12,14,16 a two-hub structure wins. There is no single extremal family.
5. **Single-prime unit finiteness** (finitely many `{2,3,23}`-unit amplitude products).
   **Refuted:** the unit population is unbounded in n. The 23-gate sparsifies (~11× / ~500×
   with the full unit filter) and pins the tie uniquely at n=11, but supplies no finiteness.

---

## The corrected tail picture

BG is **not** "sup density < 1." It is:

> `D(T) < 1` **strictly** for every non-tie tree, while `sup_T D(T) = 1` is **approached**
> (by tie-recursive structures) and **reached** only at integer resonances (`11 | n` plus
> the specific tie structure).

**Archimedean approach + arithmetic reaching.** No uniform gap to lean on. On `Φ¹¹` itself
(equivalently `h_inf = −log Φ¹¹`), the sup is `1`, reached only at the resonances, and
`Φ¹¹ → ~0.4` (not 0, not 1) on the tie-recursive family.

---

## Open — the crux, and the one live lead

**General competitor extremality** remains open, and the map above shows it needs an
argument that is simultaneously **collective** (not a sum of local terms), **archimedean-
aware** (it is a growth-rate, not an algebraic certificate), and **integrality-based** (the
23-gate carves the exact-1 locus). No framework yet supplies all three.

**Live leads:**

1. **The sharp side — 23-gate-strictness lemma:** prove the deficit is `> 0` *strictly* for
   the tie-recursive family — that the amplitude product of any non-tie tree misses
   `(621/64)^(n/11)` by an amount bounded below by an arithmetic (not smooth, not local)
   quantity. The `sporadic_tie` gate is the anchor; the sufficiency is the research frontier.
2. **The ≤-half assembly — land the g-step closure** (see the 2026-08-20 section above):
   `gstep_le_one_achievable` is proven on the PR #20 branch; what remains is review +
   merge, then composing with the leaf-child all-n case and the multi-hub side (R2) —
   mechanical/structural work, not open mathematics, unlike lead 1.

---

*Session-honest note: the near-star spine is proven with Lean CI green on the arithmetic
cores; the conjecture is not. Every "ruled out" above carries its reason. The toolkit's
`conjecture1_proved` flag is `False` throughout, by design.*
