# Support-side search — ONE survivor, explicitly orthogonal to the wall

*Adversarial multi-agent search `wryhnwohw` (13 agents; literature web-verified, corpus
read against disk). Outcome: **one genuine partial foothold survived** — and, crucially,
it discloses its own limitation: it is orthogonal to the off-line wall. The other five
threads collapse (all into RH). `conjecture1_proved = False`.*

## The survivor: partial-temperedness (Selberg's second moment)
Strictly PARTIAL + UNCONDITIONAL + NON-TRIVIAL, and it survives both degenerate collapses:
- **Not free.** Selberg's second moment `∫₀ᵀ |S(t)|² dt = (T/2π²) log log T + O(...)`
  (Selberg 1946; Fujii) is *unconditional* and strictly stronger than the free polynomial
  `N(T)` count — it pins the fluctuation `S(t) = N(t) − ⟨N⟩(t)` mean-square to `log log T`.
  Trudgian (arXiv:1208.5846): `|S(T)| ≤ 0.111 log T + 0.275 log log T + 2.450` unconditionally.
- **Not RH.** The bounds are unconditional (RH only sharpens the error term).

## Why it is a foothold, NOT a bridge (the honest heart)
`S(t)` counts zeros **by ordinate**. By the functional equation, an off-line symmetric
zero pair `(ρ, 1−ρ, ρ̄, 1−ρ̄)` contributes to `N(t)` at its ordinate *identically* to an
on-line pair at the same ordinate — so the second moment is **insensitive to the real
part** (the *OrdinateInsensitivity* witness). Hence the survivor **forces no zero onto
`Re = ½`.** All extant partial-temperedness lives on the **vertical / ordinate axis**,
orthogonal to the **horizontal / off-line axis** where the wall is. It is a foothold that
*cannot, by construction, migrate to off-line location.*

**Its value is diagnostic:** it pins, kernel-checkably, the exact boundary between what all
current temperedness delivers (ordinate) and what RH demands (off-line) — certifying
*where* the missing support-side idea must act. It is **not** progress toward closing RH.

## The five collapses (all → RH)
- `weakest-support` → the only relaxation that does work on zeta (Favorov 2411.07190)
  hypothesises "only real zeros" = RH.
- `crystalline-frontier` → Favorov 2504.03365 linear-growth condition `Σ_{|γ|<r}|h_γ|=O(r)`
  is *unconditionally FALSE* for the zeta comb (`ψ(eʳ)~eʳ` super-linear); the bounded-strip
  lever silently re-requires bounded spectral density, which the dense arithmetic spectrum denies.
- `beurling-malliavin` → completeness is location-blind (free); any reality-forcing lands on
  Hermite–Biehler positivity = Suzuki Hamiltonian positivity = RH; Conrey–Li refutes naive positivity.
- `dbn-support` → the support-side dynamical content lives inside the counterfactual `Λ<0`
  (stronger than RH); Tao states the `Λ≥0` methods "don't seem to say anything new about zeta."
- `support-bifurcation` (kill test) → both horns confirmed; decisive independent fact: the
  Riemann–Weil explicit-formula object is a *distribution*, not a measure (archimedean continuous
  term + δ′ at 0), so it is not even a crystalline measure **even assuming RH**.

## Highest-value next action (diagnostic guardrail, NOT an RH route)
Formalize the survivor as a kernel certificate `FREE < SURVIVOR < RH` with an explicit
**OrdinateInsensitivity** witness: an off-line symmetric zero-pair at a fixed ordinate leaving
the Selberg `S(t)` second-moment leading term `(T/2π²) log log T` invariant relative to the
on-line pair. Finite/decidable over classical (Selberg 1946, Trudgian 2012) inputs. Label it
explicitly: it pins WHERE the missing idea must act (off-line / horizontal); it is not a step
toward acting there. Plus five collapse-certificate guardrails.

## Verdict
The support side is, like the weight side, essentially the wall — with **one honest partial
foothold that proves itself orthogonal to the wall.** Combined map after two sweeps: the
missing idea is neither weight-side (free) nor extant-temperedness (ordinate-orthogonal); it
must act on the **off-line / horizontal** direction, which no current tool reaches.
`conjecture1_proved = False.`
