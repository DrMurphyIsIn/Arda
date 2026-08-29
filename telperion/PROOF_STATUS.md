# Brualdi–Goldwasser proof status

**Conjecture (BG 1984).** For every tree `T` on `n` vertices, `Φ¹¹(T) ≤ 1`, with equality
iff `T` is one of the six eleven-vertex ties (the `c+k=5` near-star family; in the rooted
invariant `bg_phi11`, the unique tie is the near-star `N(0,5)` at `n=11`).

`conjecture1_proved = False.` This file is the honest map: what is proven, what is ruled
out (and why), and the one lead that remains.

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

---

## Ruled out — with reasons (this is the value)

Each of these is a *reasoned* dead end, established by the audit and two expert councils,
not a mere failure to find. **Re-audited 2026-08-29** (exact-arithmetic reproductions):
#1, #3, #5 confirmed rigorous; #4 confirmed in conclusion but its evidence corrected (see
below); #2 is the only one *asserted* rather than *proven* — a reasoned no-go, not a theorem.

1. **Sum-of-non-positive-local-terms** (local potentials `P(m)≥0`, per-vertex/per-node
   monotonicity, the transfer `g_v≤0`, rooted-subtree `p_S≤1`). **Refuted:** `Φ¹¹≤1` is a
   *genuine collective cancellation* — per-node factors span `{0.103, 1.53, 8.91}`, product
   = 1, and the tie-hub's own naive defect is `+0.424 > 0`. The cancellation is non-local by
   nature. (Explains the campaign's `+0.199` residual stall.)
2. **Smooth / algebraic certificates** (Hodge–Riemann, SOS, real-rootedness/interlacing,
   single-prime p-adic Lorentzian grading). **No known certificate works — strong reasons,
   not a proven no-go.** The obstruction is *archimedean magnitude* (a growth-rate: density
   → 1; a corollary of #1 and #3), which no algebraic identity sees; and the arithmetic
   coordinate `v₂₃(a_v)` is integer-valued hence locally constant (differential 0 a.e.), so
   smooth Hessians/signatures collapse to rank-1 (observed: the campaign's rank-1 collapse
   and `+0.199` stall). This is the one dead end *asserted* rather than *proven* — a genuinely
   novel certificate is not rigorously forbidden, but must be simultaneously collective +
   archimedean-aware + integrality-based (the crux bar). (Re-audit 2026-08-29: prong (a) is
   a corollary of the reproduced #1/#3; prong (b) is a well-evidenced heuristic, not a theorem.)
3. **Uniform density gap** (`sup_T D(T) < c < 1`). **Refuted:** `sup_T D(T) = 1`. The
   tie-recursive family "hub + k tie-subtrees" (`n = 11k+1`) has density → 1 (0.9998 at
   k=400), higher than the legs-2 `D∞ = 0.9585`. There is no uniform gap. (Note: legs-2 is
   NOT the extremal manifold — a correction to an earlier session premise.)
4. **Near-star competitor extremality** (near-star maximizes at each n). **Refuted:** the
   per-n density-maximizer follows a *parity law* — near-star at **every odd n**
   (5, 7, 9, 11, 13, 15, …), a non-near-star (multi-hub) at **every even n**
   (4, 6, 8, 10, 12, 14, 16, …). So near-star is not universally extremal (it loses at all
   even n), yet it *does* win at n=11, where the maximizer is the tie N(0,5) with Φ¹¹=1
   (**not** a two-hub). There is no single extremal family. (Re-audit 2026-08-29: exact per-n
   maximizer sweep n≤16 — no max exceeds 1; this corrects an earlier n-list that listed n=11
   as two-hub, which read literally would be a BG counterexample, and understated near-star's
   odd-n reach to {9,13,15}.)
5. **Single-prime unit finiteness** (finitely many `{2,3,23}`-unit amplitude products).
   **Refuted:** the unit population is unbounded in n. The 23-gate sparsifies (~11× / ~500×
   with the full unit filter) and pins the tie uniquely at n=11, but supplies no finiteness.
   (Re-audit 2026-08-29: the `{2,3,23}`-unit count is **root-sensitive** — over all roots it
   grows 2, 3, 4, 6, 5, 14, 25, 32, 37 across n=7…15; a single-root count looks deceptively
   bounded (≤5 to n=13), so count over all roots to avoid a false "re-refutation.")

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

**Live lead (the single rope left hanging):** prove the deficit is `> 0` *strictly* for the
tie-recursive family via a **23-gate-strictness lemma** — that the amplitude product of any
non-tie tree misses `(621/64)^(n/11)` by an amount bounded below by an arithmetic (not
smooth, not local) quantity. The `sporadic_tie` gate is the anchor; the sufficiency is the
research frontier.

---

*Session-honest note: the near-star spine is proven with Lean CI green on the arithmetic
cores; the conjecture is not. Every "ruled out" above carries its reason. The toolkit's
`conjecture1_proved` flag is `False` throughout, by design.*
