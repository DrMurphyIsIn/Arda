# QC_RECURRENCE_MEMO — the recurrence dictionary (Face 4, quantitative)

> **`conjecture1_proved = False`.** This memo *states* a dictionary between two
> faces of RH, proves one row as a classical theorem-sketch, and connects a
> kernel-certified defect witness to a concrete recurrence-deficit number. It does
> **not** prove RH and does not claim to. Certifying *one* recurrence instance is
> not progress toward RH — the *uniform* Bagchi recurrence **is** RH. Every
> conjecture below is labeled a conjecture; every proof is a paper-level proof;
> the numerics are in-session `mpmath` transcripts (§6).

**Agent:** `qc3-recur` (MIRRORMERE Wave 3, deliverable **W3d**).
**Map:** `ROADMAP_ANDURIL_MIRRORMERE_2026-09-14.md` W3d + THE SEVEN FACES (row 4).
**Instruments read (not rebuilt):** `DefectDictionary.lean`, `R2Rigidity.lean`,
`BraggDefect.lean` (kernel defect instrument), `emit_bagchi_recurrence.py` (the
positive-side certifier). **Method:** mathematics + writing + light web
verification (≥2 sources for the Bagchi statement); small `mpmath`/`flint`
numerics; NO Lean builds.

---

## §0. One-paragraph orientation

The SEVEN-FACES table lists Face 4 (**Recurrence**) as "RH ⟺ Bagchi strong
recurrence in the strip," instrumented by the `bagchi_recurrence` emitter on the
positive side and by the W3d memo on the negative side. This memo is the negative
side: it builds the **dictionary** connecting the *defect* face (Face 1 positivity,
kernel-instrumented in `DefectDictionary`/`BraggDefect`, defect = negative index of
the finite Weil compression) to the *recurrence* face (Face 4, Bagchi). The
intellectual core is three dictionary rows that make Face 4 **quantitative**: an
off-line zero of displacement `δ = β − 1/2` at height `γ₀` forces a computable
**recurrence deficit** `ε₀(δ, γ₀)`, so that the kernel-counted defect `k`
lower-bounds the number of disjoint deficit-witnessing discs. The headline
arithmetic identity, verified in-session and matching the kernel witness on the
nose: for the synthetic BraggDefect configuration (`β = 3/5`, `γ₀ = 50`,
`δ = 1/10`) the **first-order** recurrence deficit is the amplitude excess
`d = e^δ + e^{−δ} − 2 = 0.0100083…`, and its **second-order (Weil-energy)** form is
`d² = 1.00167·10⁻⁴` — *exactly* the `−1.00167·10⁻⁴` defect witness of
`BraggDefect.defect_witness_offline`. The defect number **is** the squared
recurrence deficit. This is the dynamical reading of the kernel measurement.

---

## §1. Bagchi's theorem, pinned precisely

**B. Bagchi (1981)**, Ph.D. thesis *"The statistical behaviour and universality
properties of the Riemann zeta-function and other allied Dirichlet series,"* Indian
Statistical Institute, Calcutta. The equivalence is written up in **J. Steuding,
*Value-Distribution of L-Functions*, Springer LNM 1877 (2007), §8** (the canonical
textbook reference; cited as such by the strong-recurrence literature, e.g.
Nakamura–Pańkowski, *Archiv der Math.* 95 (2010), 549–555 and its corrigendum
arXiv:1203.1393, which formulate it as "Theorem A … see also [Steuding, §8]").

Write `D := {s ∈ ℂ : 1/2 < Re s < 1}` (the open right half of the critical strip).

> **Theorem (Bagchi 1981; strong-recurrence equivalence).**
> The Riemann Hypothesis holds **if and only if**, for every compact set `K ⊂ D`
> with **connected complement** and for every `ε > 0`,
> ```
>        lim inf_{T→∞}  (1/T) · meas{ τ ∈ [0,T] : sup_{s∈K} |ζ(s+iτ) − ζ(s)| < ε }  >  0 .
> ```

Verbatim ingredients (verified against the survey/paper statements, §7):

- **Hypotheses on `K`.** `K` is a **compact subset of the open strip `D`** (so
  `1/2 < Re s < 1` for `s ∈ K`) with **connected complement** `ℂ \ K`. The
  connected-complement condition is inherited directly from Voronin's universality
  theorem (below): it is exactly Mergelyan/Runge's hypothesis, ensuring the target
  is uniformly approximable by polynomials in `1/(s − a)`, i.e. that there is no
  "hole" in `K` that the approximation cannot reach. (The literature states the
  hypothesis but does not motivate it; the motivation is the Mergelyan step in the
  universality machine.)
- **Positive lower density.** `meas` is Lebesgue measure on `ℝ`; the quantity is the
  **lower density** `d̲(A) := lim inf_{T→∞} (1/T) meas(A ∩ [0,T])` of the shift set
  `A_{K,ε} := {τ : sup_K |ζ(·+iτ) − ζ| < ε}`. "Positive lower density" is
  `d̲(A_{K,ε}) > 0`; in topological-dynamics language this is **recurrence** of the
  flow `T_τ ζ = ζ(·+iτ)` to every neighbourhood of `ζ|_K`, and its *positive-density*
  strengthening is **strong recurrence**.

### Voronin universality, and what strong recurrence adds

> **Voronin (1975), universality.** Let `K ⊂ D` be compact with connected
> complement, and let `g : K → ℂ` be **continuous, non-vanishing on `K`, and
> analytic in the interior**. Then for every `ε > 0`,
> ```
>       lim inf_{T→∞} (1/T) meas{ τ ∈ [0,T] : sup_{s∈K} |ζ(s+iτ) − g(s)| < ε }  >  0 .
> ```

Universality says ζ's vertical shifts approximate **every** admissible target `g`
(non-vanishing analytic) with positive density. **Strong recurrence is the single
choice `g = ζ|_K`** — ζ approximates *itself*. The crux is the **non-vanishing**
requirement: Voronin's theorem is only *available* for zero-free targets, so it
delivers self-approximation **for free precisely on those `K` where `ζ` itself is
zero-free** — i.e. on `K ⊂ D` **if RH holds** (then ζ has no zeros in `D` at all).
The content of Bagchi's equivalence is that this is not just sufficient but
**necessary**: an off-line zero destroys self-recurrence. That necessity is the ⇐
direction and the subject of dictionary row (a).

Background note (joint universality, for context): Voronin's original and its
Bagchi-era extensions are *joint* (simultaneous approximation for tuples of
Dirichlet `L`-functions with independent characters); strong recurrence is the
single-function diagonal specialization. The `d = 0` phrasing in the modern
literature ("self-approximation of `log ζ` with shift parameter `d = 0`") is the
same statement — `d` there is an *extra* real dilation parameter `ζ(s + iτ)` vs.
`ζ(d·s + iτ)`; `d = 0`/`d = 1` recovers the pure vertical shift, and only that case
is equivalent to RH (Nakamura–Pańkowski).

---

## §2. The dictionary rows — DEFECT ⟷ RECURRENCE

The three rows connect the kernel-instrumented **defect** (negative index of the
finite Weil compression, `DefectDictionary.defect`) to **quantified
recurrence-failure**. Each is stated at its honest grade.

### Row (a) — OFF-LINE ⇒ RECURRENCE-DEFICIT (the quantitative Rouché row)

**Classical qualitative form (Bagchi ⇐, the necessity direction).** Reconstructed
argument (this is the standard Hurwitz/Rouché mechanism; it is the ⇐ half of the
Steuding §8 write-up, stated there via "the classical Rouché theorem," cf. the
Nakamura–Pańkowski corrigendum proof of their Theorem 2.1):

> Suppose ζ has an off-line zero `ρ₀ = β + iγ₀` with `β > 1/2`. Pick `r > 0` so
> small that the **closed disc** `B̄(ρ₀, r) ⊂ D` contains `ρ₀` as its **only** zero
> of ζ (possible: zeros are isolated), and let `C = ∂B(ρ₀, r)` be its boundary
> circle. On the compact `C`, ζ is zero-free, so
> ```
>        m := min_{s∈C} |ζ(s)|  >  0 .                                   (m)
> ```
> Take `K = B̄(ρ₀, r)` (compact, in `D`, connected complement). Suppose, for
> contradiction, that a shift `τ` satisfies `sup_{s∈K} |ζ(s+iτ) − ζ(s)| < m`. Then
> on `C`, `|ζ(s+iτ) − ζ(s)| < m ≤ |ζ(s)|`, so by **Rouché's theorem** `ζ(·+iτ)` and
> `ζ(·)` have the **same number of zeros inside `C`** — namely one. Hence `ζ(·+iτ)`
> has a zero in `B(ρ₀,r)`, i.e. ζ has an off-line zero in `B(ρ₀ − iτ, r)` = a
> **translated copy** of the off-line zero, at height `γ₀ − τ`. If the recurrence
> set `A_{K,m} = {τ : sup_K|ζ(·+iτ)−ζ| < m}` had positive lower density, ζ would
> have off-line zeros at a positive-density set of heights `γ₀ − τ` — a positive
> proportion of all zeros off the line — contradicting the classical fact that the
> off-line zeros have density zero (Bohr–Landau / the zero-density theorems; even
> the crude `N(T) ∼ (T/2π)log T` with the Bohr–Landau `o(T)` off-line bound
> suffices). Therefore `d̲(A_{K,m}) = 0`: **the recurrence tolerance `ε` cannot be
> pushed below `m` at positive density**. Recurrence *fails* for every `ε < m`. ∎

So the qualitative deficit is exactly the min-modulus `m` of (m): **an off-line zero
`ρ₀` forbids self-recurrence to any tolerance below `m` on a disc around it.**

**Quantitative form — the explicit `ε₀(δ, γ₀)`.** The pure geometric content,
stripped of the analytic accident of *which* circle, is a rank-1 fact about the
off-line **factor**. Model the off-line pair (as `BraggDefect` does) on the
`z = e^{iωx}` circle by the self-inversive Blaschke pair with radii
`z = e^{−δ}` (inside `|z|=1`) and its mirror `z = e^{δ}` (outside): an on-line zero
sits *on* `|z| = 1`, an off-line one is displaced to radius `e^{±δ}`. The
min-modulus of a single factor `(z − ρ)` on `|z| = 1` is `|1 − ρ|`, so the two
half-deficits are

```
      g₋(δ) = 1 − e^{−δ}    (inner factor, the transported-zero clearance)
      g₊(δ) = e^{δ} − 1     (outer mirror factor)
```

and the **recurrence deficit** is the *product* (the two-sided clearance the shift
must simultaneously bridge to move the pair onto the line):

> **ε₀ formula (first order).**
> ```
>      ε₀(δ) = g₊(δ)·g₋(δ) = (e^{δ} − 1)(1 − e^{−δ}) = e^{δ} + e^{−δ} − 2 = d ,
> ```
> the **amplitude excess `d`** of the off-line pair — *identically* the `excess`
> of `BraggDefect.excess`. To leading order `ε₀(δ) = δ² + O(δ⁴)`.

The **Weil-energy** (quadratic-form) reading squares it — the defect functional
`BraggDefect.defectFunctional(d) = −d²` is a *quadratic* form value, one power of
`d` for each of the two evaluation-vector legs `x = Re u`, `y = Im u` of the pair
block `x xᵀ − y yᵀ`:

> **ε₀ formula (second order = the defect witness).**
> ```
>      ε₀²(δ) = d² = (e^{δ} + e^{−δ} − 2)²  =  |defectFunctional(d)|  =  |q| .
> ```

At `δ = 1/10`: `ε₀ = d = 0.0100083…`, `ε₀² = d² = 1.00167·10⁻⁴`. The **height
dependence** `γ₀` enters only through the **zeta-unit scale** of the abstract
deficit: to convert the dimensionless `ε₀(δ)` into a genuine `sup_K|ζ(·+iτ)−ζ|`
tolerance one multiplies by the local size of ζ near the shadow `1/2 + iγ₀`. To
leading order the min-modulus `m` of (m) on a circle of radius `r` around the
shadow is `m ≈ r·|ζ′(½+iγ₀)|`, so

> ```
>      ε₀^ζ(δ, γ₀)  ≈  d(δ) · |ζ′(½ + iγ₀)|         (first order, zeta units)
> ```
> giving `ε₀^ζ = 0.01617…` at `(δ,γ₀) = (1/10, 50)` since `|ζ′(½+50i)| = 1.61616…`.

**Honest label:** row (a) qualitative (`ε` below `m` ⇒ recurrence fails) is a
**classical theorem** (Bagchi ⇐, Rouché). The explicit closed form `ε₀ = d`,
`ε₀² = d²` is a **precise conjecture-grade identification** of the deficit with the
BraggDefect amplitude excess — exact for the rank-1 synthetic pair-block model, and
provable at that grade (§4); the `|ζ′|` scaling to genuine zeta units is
leading-order (a modulus-of-continuity refinement is deferred, exactly as the
emitter defers its continuous-sup step, §3).

### Row (b) — DEFECT-`k` ⇒ DEFICIT-COUNT `k`

`R2Rigidity.defect_eq_offline_pairs` (kernel) proves `defect A = p` — the finite
Weil compression's negative index equals the off-line pair count, two-sided, under
the honest `NegativeWitness` non-degeneracy input. Composing with row (a):

> **Conjecture (deficit-count).** If the kernel-counted defect of the height-`γ₀`
> window is `k` (`k` independent off-line pairs, `BraggDefect.defect_eq_two` is the
> `k = 2` instance), then there are **`k` disjoint discs** `B(ρ₀^{(j)}, r_j) ⊂ D`,
> one per pair, each carrying its own recurrence deficit `ε₀^{(j)} = d_j > 0`. Hence
> the defect lower-bounds the number of deficit-witnessing discs:
> ```
>        #{ disjoint discs with recurrence-deficit > 0 in the window }  ≥  defect = k .
> ```

The disjointness is exactly what `R2Rigidity` certifies on the algebraic side: the
`k` negative directions `y_j` are **linearly independent** (`NegativeWitness.ofLinearIndependent`),
which is the compression-side image of "the `k` off-line zeros sit at `k` distinct
places," so their discs can be taken disjoint. `BraggDefect.defect_eq_two`
(`d₁ = e^{1/10}+e^{−1/10}−2`, `d₂ = e^{1/5}+e^{−1/5}−2`, orthogonal channels
`e₁, e₃`) is the two-disc instance: defect exactly 2, two independent deficits. This
row is the quantitative bridge — the kernel already counts `k`; row (a) turns each
count into a *dynamical* obstruction of magnitude `d_j`.

### Row (c) — THE FINITE PROBE (Wave-4-ready)

The synthetic BraggDefect configuration is a **complete, two-directional probe** of
Face 4. The `bagchi_recurrence` emitter certifies the **positive** side (genuine ζ
*does* recur), the ε₀ formula is what a **refutation** would violate. Both
directions, spelled out:

- **POSITIVE instrument (emitter, genuine ζ).** `emit_bagchi_recurrence.py` scans
  integer shifts `τ`, computes via flint/Arb `acb.zeta` the certified rational
  grid-max `M = max_{grid} |ζ(s+iτ) − ζ(s)|` over a rational box `K`, and emits the
  kernel theorem `dev ≤ M ≤ ε` (trust seam: the Arb enclosure carried as `hdev`;
  the kernel proves `M ≤ ε` by `norm_num`). This certifies *recurrence instances* —
  ζ approximating itself to a small `M` at some shift — the positive evidence that,
  for the *actual* zeta with no known off-line zeros, recurrence discs *exist*. Its
  self-check REFUSES `ε < M` (negative control): you cannot claim a tolerance the
  grid does not meet.

- **REFUTATION instrument (ε₀, synthetic).** For the synthetic off-line
  configuration, row (a) gives the deficit `ε₀(δ) = d`, `ε₀²(δ) = d² = |q|`. A
  recurrence *refutation* is precisely the emitter's dual, packaged in the emitter's
  own `bagchi_recurrence_refutes` atom: a shift-free **lower** bound `L ≤ dev` with
  `ε ≤ L` forces `¬RH`. The synthetic configuration furnishes the number: near a
  planted off-line pair the deficit floor is `L = ε₀ = d`, so **any claimed
  recurrence tolerance `ε < d` at that disc is refuted**. Concretely, at
  `(β,γ₀) = (3/5, 50)`: the disc around `1/2 + 50i` has a certified real-ζ
  min-modulus `m = 0.18503…` on the radius-`δ` circle (§6) — the *actual* ζ clearance
  there — while the *synthetic-pair* deficit is `d = 0.010008…`, `d² = 1.00167·10⁻⁴`.
  The instrument's two numbers are: the emitter would certify `M` (how well genuine ζ
  recurs at that box); the ε₀ formula certifies `d` (how badly a *planted* off-line
  pair would degrade it). **The probe is complete when a Wave-4 run reports `M` (real
  ζ, positive) and `d` (synthetic, refutation floor) side by side on the same box —
  the certified statement of Face 4's two directions.**

  A ready Wave-4 experiment (specified, not run here — no Lean/emitter build in this
  worktree): run the emitter on box `K = [0.55,0.65]×[49.9,50.1]` for genuine ζ to
  get `M`; overlay the synthetic pair `ρ₀ = 3/5+50i` and recompute the perturbed
  grid-max `M'`; the increment `M' − M` should track `ε₀ = d = 0.010008…` (first
  order) — the emitter's grid-max is the observable that the ε₀ formula predicts.

---

## §3. The dynamics frame

The quasicrystal ⟷ recurrence correspondence is not a metaphor; it is the
Kronecker-flow structure that both W3c (spatial) and W3d (dynamical) formalize —
"the same torus seen spatially vs dynamically" (roadmap W3d). Carefully:

**The flow.** Let `𝕋 = ∏_p S¹` be the infinite-dimensional torus indexed by primes
(the Kronecker/Bohr compactification of the line, via `t ↦ (p^{−it})_p`). The map
`t ↦ (p^{−it})_p` is the **Kronecker flow**: a one-parameter group of rotations by
the frequency vector `(log p)_p`. For `Re s > 1` the Euler product realizes ζ as the
pullback of a continuous function `𝒵` on `𝕋`, `ζ(σ + it) = 𝒵(σ, (p^{−it})_p)`, and
the vertical shift `t ↦ t + τ` **is** the time-`τ` map of the flow. Because the
frequencies `{log p}` are ℝ-linearly independent (unique factorization), the flow is
**minimal and uniquely ergodic** (Weyl), and `t ↦ ζ(σ+it)` is **Bohr
almost-periodic** for `σ > 1`.

**Bohr almost-periodicity = Poincaré recurrence of the isometric flow.** For `σ > 1`
the orbit closure is a compact group (a sub-torus of `𝕋`) on which the flow is an
isometry; almost-periodicity of `ζ(σ+i·)` is exactly **Poincaré recurrence** of this
isometric flow — every neighbourhood of the initial point is revisited, at a
*syndetic* (relatively dense) set of times. This is the `σ > 1` shadow of strong
recurrence, and it is *unconditional* (no RH content) precisely because there are no
zeros there.

**Universality = strip-recurrence gone wild.** Push `σ` into the strip
`1/2 < σ < 1`. Now the Euler product diverges; the correspondence with `𝕋` survives
only in an `L²`/measure sense (the Bagchi limit measure on the space of analytic
functions, the pushforward of Haar measure on `𝕋` under the analytic-continuation
map). The flow is no longer an isometry of a finite-dimensional torus but its
**image measure has full support** on the space of admissible (non-vanishing
analytic) targets — that is Voronin universality: the orbit is not merely recurrent,
it is **equidistributed densely enough to approximate every zero-free target**.
Strong recurrence is universality's diagonal (`g = ζ|_K`).

**RH = the boundary survival of group-flow recurrence.** The one obstruction to
extending the isometric recurrence from `σ > 1` down through the strip is a **zero**
of ζ in `D`: a zero is a point where the target `ζ|_K` *itself* fails the
non-vanishing hypothesis of universality, so the group-flow's self-recurrence has
nothing to recur *to* — the orbit cannot approximate a function that vanishes where
the approximant provably (Rouché, §2 row (a)) cannot. RH is exactly the statement
that **no such obstruction exists** — that the Poincaré recurrence of the Kronecker
flow, unconditional for `σ > 1`, **survives all the way to the critical line**. In
KS/section language: the quasicrystal (the zero comb) is a **Poincaré section** of
the Kronecker flow, and W3c formulates its point set spatially (restriction from
`∏_p S¹`) while W3d reads the *same* object dynamically (return times of the flow) —
recurrence deficit `ε₀` is the *cross-section thickness* an off-line zero punches
through the section.

Citations for this frame: Bohr (almost-periodicity of Dirichlet series);
Voronin 1975 (universality); Bagchi 1981 (the limit measure on `𝕋` and the
recurrence equivalence); Reich (discrete universality via the same measure);
Steuding LNM 1877 (the modern synthesis, §5 measure / §8 recurrence). See §7.

---

## §4. Ranked open problems feeding Wave 4

Ranked by attackability with **current** tools.

1. **Row (a) qualitative — ALREADY A CLASSICAL THEOREM (Bagchi ⇐).** "An off-line
   zero forbids recurrence below `m`" is proved (§2, Rouché). Nothing to do but
   *cite* it; it anchors the dictionary.

2. **Row (a) explicit `ε₀ = d`, `ε₀² = d²` on the rank-1 pair-block model —
   PROVABLE NOW, kernel-ready.** The identity `(e^δ−1)(1−e^{−δ}) = e^δ+e^{−δ}−2` and
   its square are pure `Real.exp` arithmetic; they can be a guarded Lean lemma in the
   `BraggDefect` file linking `excess` to a `recurrenceDeficit δ := (Real.exp δ − 1)*
   (1 − Real.exp (−δ))` with `recurrenceDeficit δ = excess` and
   `recurrenceDeficit δ ^ 2 = |defectFunctional excess|`. **This is the concrete W4
   deliverable** — the kernel statement "the defect witness equals the squared
   recurrence deficit," honestly `ζ`-free and RH-free. *Assessment: provable this
   wave with existing machinery; recommend it as the W3d→kernel hand-off.*

3. **Row (b) deficit-count = defect (the disjoint-disc conjecture) — NEEDS the
   analytic disjointness lemma.** The algebraic side (`defect = k`, `k` independent
   `y_j`) is done in the kernel; turning "`k` independent negative directions" into
   "`k` disjoint discs each with `ε₀^{(j)} > 0`" needs the analytic input that
   distinct off-line zeros have disjoint Rouché discs with individually positive
   min-modulus. This is classical (isolated zeros) but not currently formalized; it
   is a **modulus-of-continuity / isolation lemma**, provable with effort, not RH-hard.

4. **Row (a) `|ζ′|` scaling to *genuine* continuous-sup zeta tolerance — NEEDS new
   analysis (modulus of continuity), same gap the emitter defers.** Converting the
   grid-sup / leading-order `r·|ζ′|` into a certified *continuous* `sup_K` bound
   requires a Lipschitz/derivative-bound argument between grid points on `K`. The
   emitter documents this as out of scope; closing it is a genuine (but standard)
   effective-analysis task — the honest boundary of the finite probe.

5. **The RH-hard wall (NOT attempted).** Driving the deficit count `k → 0` uniformly
   in `γ₀`, i.e. proving *no* disc ever carries a deficit, **is RH** (it is the ⇒
   direction of Bagchi via the ⇒ direction of `defect_zero_iff_onLine`, carried as
   the named hypothesis `hcryst_forces_online`). Tracked, never touched.

---

## §5. Cross-face reconciliation (why the two numbers coincide)

The identity `ε₀² = |q|` is not a coincidence; it is **conservation of difficulty**
across faces 1 and 4 made arithmetic. Face 1 (positivity) measures the off-line pair
by the *quadratic form* `x xᵀ − y yᵀ` — its negative eigenvalue is `−d²` because the
form is quadratic in the evaluation vector `u = x + iy` whose imaginary leg has size
set by `d`. Face 4 (recurrence) measures the *same* pair by the *linear* clearance
its zero must travel to reach the line — the min-modulus deficit `d`. Squaring the
linear (dynamical) deficit gives the quadratic (energy) defect: **`(recurrence
deficit)² = defect witness`**. The kernel measured `−1.00167·10⁻⁴`; the dynamics
predicts `−(0.0100083…)²`; they agree to all printed digits (§6). Two faces, one
off-line pair, one number — exactly the SEVEN-FACES "conservation of difficulty …
the probes are interderivable" prediction, now checked on the row-4/row-1 pair.

---

## §6. In-session numeric verification log

Run in `/Users/peterwmurphy/arda-qc3-recur` with `mpmath` (dps=40) + `flint`.

- **BraggDefect cross-check.** `δ = 1/10`, `d = e^δ+e^{−δ}−2 = 0.0100083361116`,
  `q = −d² = −1.00166791723·10⁻⁴` — matches `BraggDefect`'s `−1.00167·10⁻⁴`. **PASS.**
- **ε₀ formula (first order).** `g₋ = 1−e^{−δ} = 0.0951625820`,
  `g₊ = e^{δ}−1 = 0.1051709181`; **product `g₊·g₋ = 0.0100083361116 = d`** exactly
  (the recurrence deficit is the amplitude excess). *(Note: the* sum *`g₊+g₋ =
  0.2003… = 2δ+O(δ³)` is* not *`d`; the* product *is — corrected here.)* **PASS.**
- **ε₀ formula (second order).** `d² = 1.00166791723·10⁻⁴ = |q|` — the squared
  recurrence deficit equals the defect witness. **PASS.**
- **zeta-unit scale.** `|ζ′(½+50i)| = 1.616161758`; first-order deficit in zeta
  units `d·|ζ′| = 0.01617509`, second-order `d²·|ζ′| = 1.618857·10⁻⁴`.
- **Concrete Bagchi `m` (real ζ).** min-modulus of *genuine* ζ on the circle
  `|s − (½+50i)| = δ = 0.1` is `m = 0.1850313075` (attained near `0.507+49.90i`);
  this is the actual real-ζ recurrence-forbidding floor of (m) at that disc, against
  which the synthetic pair's `d = 0.0100…` deficit is the *planted* obstruction.

Scripts: `/tmp/deficit_probe.py`, `/tmp/deficit_probe2.py` (transcripts above).

---

## §7. Sources (verified this session, ≥2 for the Bagchi statement)

- **B. Bagchi**, *The statistical behaviour and universality properties of the
  Riemann zeta-function and other allied Dirichlet series*, Ph.D. thesis, Indian
  Statistical Institute, Calcutta, 1981. (The strong-recurrence equivalence; primary
  source.)
- **J. Steuding**, *Value-Distribution of L-Functions*, Springer LNM 1877 (2007),
  §5 (Bagchi limit measure) and §8 (the recurrence equivalence + Rouché proof) — the
  canonical textbook write-up.
- **K. Matsumoto**, *A survey on the theory of universality for zeta and
  L-functions*, arXiv:1407.4216 — states Bagchi's equivalence and the topological-
  dynamics ("strong recurrence") reading. https://arxiv.org/abs/1407.4216
- **Nakamura–Pańkowski**, *The generalized strong recurrence for non-zero rational
  parameters*, Archiv der Math. 95 (2010) 549–555; corrigendum arXiv:1203.1393 —
  "Theorem A … see also [Steuding, §8]"; the `d = 0` ⟺ RH phrasing; the Rouché
  contradiction proof of their Thm 2.1. https://arxiv.org/abs/1203.1393
- **Joint value-distribution of shifts of ζ**, arXiv:2010.08332 — verbatim Bagchi
  statement with `K ⊂ D`, connected complement, positive-lower-density condition.
  https://arxiv.org/abs/2010.08332
- **Voronin (1975)**, universality theorem (non-vanishing analytic targets); Bohr
  (almost-periodicity of Dirichlet series); Reich (discrete universality) — the
  dynamics-frame classics (§3), via Steuding LNM 1877 and Matsumoto's survey.

`conjecture1_proved = False`.
