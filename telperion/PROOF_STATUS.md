# Brualdi–Goldwasser proof status

**Conjecture (BG 1984).** For every tree `T` on `n` vertices, `Φ¹¹(T) ≤ 1`, with equality
iff `T` is one of the six eleven-vertex ties (the `c+k=5` near-star family; in the rooted
invariant `bg_phi11`, the unique tie is the near-star `N(0,5)` at `n=11`).

`conjecture1_proved = False.` This file is the honest map: what is proven, what is ruled
out (and why), and the one lead that remains.

Here `Φ¹¹(T) = (64/621)ⁿ · (∏_v a_v)¹¹` where `a_v = 1 + z_v S_v` is the rational cavity
amplitude (`z_v = 1/deg`, `m_v = z_v/a_v`), maximized over roots. The per-vertex density
is `D(T) = Φ¹¹(T)^(1/n)`.

> **⚠️ SCOPE CORRECTION (2026-08-29).** `Φ¹¹` (the rooted-branch cavity invariant above) is
> **NOT** the classical Brualdi–Goldwasser quantity. BG (1984) asked for `max per(L)/∏deg`
> over `n`-vertex trees — the "raw ρ" this repo's own `rooted_phi.py` docstring set aside.
> The two are provably distinct (verified with the repo's own `girardeau` module vs
> `bg_phi11`): at the tie `N(0,5)`, `per(L)/∏deg = 81/8 = 10.125` but the `Φ¹¹` amplitude is
> `621/64 = 9.703`; at Pant's `T(3,4,3)` (n=23), `per(L)/∏deg = 116.131` (matching the
> literature) but the `Φ¹¹` amplitude is `112.41`. In fact `per(L)/∏deg > ρ_B^n` at the
> maximizer for **every** `n ≥ 4`, so "`per(L)/∏deg ≤ ρ_B^n`" (what `Φ¹¹ ≤ 1` would be in the
> classical normalization) is **false for every n ≥ 4** — `Φ¹¹ ≤ 1` holds only because `Φ¹¹`
> is the different, smaller rooted-branch invariant. Classical BG is a **separate open
> problem**: Wu–Dong–Lai (2025) conjectured the max; **Pant (2026, arXiv:2605.14176) refuted
> WDL** with caterpillar families `T(3,t,3)`, `T(t,t,t,t)`, `T(t,t,t+1,t)`; the true max is
> unknown and parity-structured. **Everything below is a genuine, kernel-verified study of the
> `Φ¹¹` invariant — a legitimate object inspired by BG, but not the BG conjecture itself.** The
> `BG*`-named Lean gate modules certify facts about `Φ¹¹`; their results stand under this
> corrected name.

---

## Proven (the near-star spine)

| Piece | Statement | Rigor | Module |
|---|---|---|---|
| **Tie** (n=11) | `Φ¹¹ = 1` unwinds to the integer equality `64·243·23 = 621·576` | exact / **Lean CI-green** | `rigidity`, `FractalTail.lean` |
| **Near-star tail** | `Φ¹¹(N(0,s)) ≤ 1` ∀s, eq iff s=5, via the rational ratio `Q(s)=(486/529)(1+1/(4s²+11s+6))¹¹` reducing to the integer inequality `162¹¹·486 < 161¹¹·529` | exact | `near_star_tail` |
| **Asymptote** | the near-star family limit `D∞ = (64/621)(3/2)^(11/2) < 1`, i.e. `3¹¹·64² < 2¹¹·621²` | exact / **Lean CI-green** | `fractal_eigenvalue`, `FractalTail.lean` |
| **Spider competitor extremality** | over all spiders (n≤17), all arm-surgery moves are `Φ¹¹`-non-decreasing; legs-2 canonical form is the spider-max | exhaustive | `rectification` |
| **Amplitude form** | `Φ¹¹ = (64/621)ⁿ (∏a_v)¹¹` for all trees, any root | verified n≤9 | `sporadic_tie`, `amplitude` |
| **Girardeau duality** | `per(L)/∏deg = ∏_{λ>0}(1+λ²) = |det(I+iN)|` (hard-core boson = free fermion). **NB:** this is the classical BG `per(L)/∏deg`, which is **≠ the `Φ¹¹` amplitude** (`81/8 ≠ 621/64` at the tie) — see the SCOPE CORRECTION above. `girardeau` correctly computes classical BG; `Φ¹¹` is the separate rooted-branch invariant. | exhaustive n≤9 | `girardeau` |

## The one arithmetic foothold added this session

**`tie ⟹ 11 | n`** (`sporadic_tie`). A tie forces `(∏a_v)¹¹ = (621/64)ⁿ`; the 23-adic
valuation gives `11·v₂₃(∏a_v) = n`, so `11 | n`. Ties can occur only at `n ∈ {11,22,33,…}`.
Stronger, empirically: `11·v₂₃(∏a_v) − n ≠ 0` on **every** non-tie tree tested (n ≤ 4401),
`= 0` only at `N(0,5)`. This is the sole universal-looking arithmetic obstruction in the
toolkit. **Necessary, not sufficient.**

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

**Live lead (the single rope left hanging):** prove the deficit is `> 0` *strictly* for the
tie-recursive family via a **23-gate-strictness lemma** — that the amplitude product of any
non-tie tree misses `(621/64)^(n/11)` by an amount bounded below by an arithmetic (not
smooth, not local) quantity. The `sporadic_tie` gate is the anchor; the sufficiency is the
research frontier.

---

*Session-honest note: the near-star spine is proven with Lean CI green on the arithmetic
cores; the conjecture is not. Every "ruled out" above carries its reason. The toolkit's
`conjecture1_proved` flag is `False` throughout, by design.*
