# RH critical path -- registry nodes (2026-09-17)

*`conjecture1_proved = False`. This registers STATEMENTS on the routes roadmap's
critical path (`RH_ROUTES_ROADMAP_2026-09-16.md` section 6); nothing here is proved.*

The roadmap's critical path is route-independent:

    RvM unconditional (E6 probe, else native A4)  ->  corridor bound (E7)  ->  limit explicit formula (E8)

Until today none of it had a registry node in the `rh` campaign (the MIRRORMERE
residual `MM_rvm_unbounded_mean_density` is the only registered RvM-shaped statement,
and it is the weaker superlinear-count form). This PR registers the first two as
draft nodes; the third is deliberately NOT registered (below).

## Registered (draft, blind read-back pending)

| slug | roadmap | statement (O-form) | vocabulary |
|---|---|---|---|
| `RH_rvm_unconditional` | A4 / D5, the E6 target | `∃ C > 0, ∀ T ≥ 2, |N(T) − (T/2π·log(T/2π) − T/2π + 7/8)| ≤ C·log T` | `RvMCount.zetaZeroCount` (new in RHDefs): a finsum over the strip zeros with `0 < Im ≤ T` of the order given by `MeromorphicOn.divisor riemannZeta` on the open strip -- a RECTANGLE count with multiplicity |
| `RH_corridor_bound` | E7 = A3 = B5 = D6 | `∃ C > 0, ∀ T ≥ 2, ∃ T' ∈ [T, T+1], (segment −1 ≤ σ ≤ 2 at height T' is zero-free) ∧ ∀ σ, ‖logDeriv ζ(σ + iT')‖ ≤ C·log² T` | Mathlib only (`logDeriv`, `riemannZeta`) |

Design decisions:
- **Rectangle count, not ball count.** The island's `RHInBoxAnalytic.zeroFinset c R`
  is ball-based; a ball enclosing `[−1,2]×[0,T]` reaches below the real axis and
  miscounts conjugates (roadmap section 9 refused `RH_rvm_explicit_remainder` for
  exactly this reason). `zetaZeroCount` avoids it. `finsum` is 0 on infinite
  support, so the definition is total; finiteness of the support is a theorem.
- **Multiplicity, not distinct zeros.** A distinct-zero count would NOT be a
  classical statement (that `N_distinct(T) ~ N(T)` is not known unconditionally);
  the divisor order gives the classical N(T).
- **Explicit zero-free conjunct in the corridor bound.** Under Lean's `x / 0 = 0`
  convention `logDeriv` is 0 at a zero, so the bare norm bound would be vacuous on
  ordinates. The classical proof chooses `T'` avoiding ordinates by `≫ 1/log T`;
  the statement says so.
- **No segment / edge / winding hypotheses.** Contrast `Backlund.nt_count_effective_bound`
  (RvMNTCount.lean), which carries `hnzBot/hnzTop/hnzL/hnzR/hbox_ball/hζne/hwind`.
  Discharging them for every `T` (ordinates included: the jump at an ordinate is
  `O(log T)` and is absorbed into `C`) is the content of `RH_rvm_unconditional`.
- **O-form constants.** The effective-constant forms stay on the standing queue;
  the O-forms are what E8 and Routes A/B/D consume.

Dependencies wired: `RH_corridor_bound -> RH_rvm_unconditional -> RH_backlund_s_log`;
both added to the goal node `RH_conjecture`.

## Deliberately NOT registered: E8, the limit explicit formula

E8 = "the unconditional Guinand-Weil identity at all heights in diffraction form".
Its statement is determined by a test-function class that the roadmap explicitly
leaves open (B6: "test-class choice determines the statement; queued until B5"),
and the finite in-tree form (`rect_explicit_formula_bragg`, weight `g ≡ 1`) has no
`T → ∞` limit at all -- the zero side diverges like N(T). Authoring E8 now would be
the "statement is the work" trap the roadmap's section 9 discipline forbids.
Proposed shape for when B5/B6 fix the class: for `g` smooth, even, compactly
supported on ℝ with Fourier transform `h`,
`∑_ρ h(γ_ρ) = h(i/2) + h(−i/2) − g(0)·log π + (1/2π)∫ h(r)·Re ψ(1/4 + ir/2) dr − ∑_n Λ(n)/√n·(g(log n) + g(−log n))`
(Weil 1952 / Guinand 1948 normalisation), with the zero sum over the multiplicity
count above. This goes on the standing queue as `RH_limit_explicit_formula`.

## Relation to E6

If the E6 probe finds a portable external Riemann-von Mangoldt formalization, the
port target is `RH_rvm_unconditional` (statement-match under the comparator
harness, then dependency-closure audit). If not, it is native A4: hard-known-shape,
~2 quarters, with `nt_count_effective_bound` + the Backlund chain as the in-tree
starting point.
