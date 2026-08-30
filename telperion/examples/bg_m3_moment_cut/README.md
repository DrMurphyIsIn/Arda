# bg_m3_moment_cut — the degree-3 no-distant-competitor step (route-b, kernel-gated)

Emitter-generated, Mathlib-only frozen Lean (`lean/BGM3MomentCut.lean`, kernel-checked by
`telperion-lean-e2e` via `lake build`; regenerated stdlib-only by `generate.py`).
`conjecture1_proved = False` — **not** a proof of Brualdi–Goldwasser.

## What it certifies

`F(T) = ½ ∫ log(1+u) dμ_N(u)` (the matching free-energy density; `u = λ²`, `N = D^{-1/2} A D^{-1/2}`) is
bounded, for any degree-3 **upper envelope** `P_3(u) = c₀ + c₁u + c₂u² + c₃u³ ≥ ½log(1+u)` on `[0,1]`, by the
weighted walk moments `m_k = (1/n)Tr N^{2k} = ∫ u^k dμ_N`:

```
F(T) ≤ c₁ m₁(T) + c₂ m₂(T) + c₃ m₃(T)  (+ c₀).
```

So if the caterpillar **maximizes** that linear moment functional over a competitor set, no competitor's `F`
exceeds `F(cat) + [Σcₖmₖ(cat) − F(cat)]`. This example kernel-gates the **argmax** (by `norm_num`): the
length-2-arm ~7-arm caterpillar strictly beats a set of **structurally distinct** competitors under
`c₁m₁ + c₂m₂ + c₃m₃` —

- the **2-regular path**, the **3-regular** and **4-regular** trees,
- **L=3-arm** caterpillars (`a=5, 7`), and far-off arm counts **`a=3`, `a=10`**.

Margins run from `+1.8e-4` (`a=10`, same family, near the frontier) to `+0.10` (4-regular). The knife-edge
nearest neighbours `a=6, a=8` are deliberately left to `bg_caterpillar_concavity` (piece 2); this certificate
covers the **distant / structurally-different** directions.

## Exact inputs

Moments are exact rationals computed (stdlib `fractions`) from the periodic bulk types via the **verified
radius-2 `m₃` integrand**

```
lhs₃(v) = C1r + T₃/d + 2·S·T₂/d² + S³/d³,   S = Σ_{a~v} 1/d_a,  S_a = Σ_{c~a} 1/d_c,
  T₂ = Σ_a (S_a−1/d)/d_a²,  T₃ = Σ_a (S_a−1/d)²/d_a³,  C1r = (1/d²)Σ_a (1/d_a²)(S_a−1/d)(S−1/d_a),
```

derived by closed-6-walk / **Dyck-path** enumeration + middle-vertex reassignment (the one radius-3 shape
`v→a→b→c→b→a→v` is reassigned to its middle vertex, collapsing to radius-2). `Σ_v lhsₖ(v) = Tr N^{2k}` is
**verified to ~1e-16** against the eigenvalue ground truth on structured + 30 random trees, and re-checked
exactly (stdlib rational matrix power) in `tests/test_bg_m3_moment_cut.py`.

The envelope coefficients `(c₁,c₂,c₃) = (1219/2520, −947/5040, 1/20)` are **frozen** exact rationals — the
tightest degree-3 upper envelope for the caterpillar (derived offline by LP; `P_3 ≥ ½log(1+u)` on `[0,1]`
with min margin ~`3.6e-4`, interval-verified offline — the `turan`/`jensen` enclosure trust model).

## Where it sits (piece 3, first certified rung)

The BG-classical crux (global concavity of the Bethe density over all trees) reduces to **[SSM, a known
theorem]** + **[`F''(a)<0`, piece 2, kernel-verified]** + **[the global no-distant-competitor step, piece 3]**.
Empirically, adding `m₃` collapses the caterpillar's moment-bound gap (`8.4e-4 → 1.8e-4`) and makes it the
unique argmax. This example is the **first kernel-gated rung** of that piece-3 hierarchy over an explicit
competitor set.

**Honest ceiling.** This is a **finite** competitor set. The *universal* degree-3 cut (over all trees) needs
**radius-2 mass-transport** — the worst-case over neighbour-of-neighbour sums `S_a` is far from the
caterpillar's, so a radius-1-mass-transport cut is loose; tightening requires a radius-2 telescoping
potential (the remaining research). So this is a proven finite rung, not a proof of BG.
`conjecture1_proved = False`.
