# The Master Inequality — the open arithmetic core of the BG closure

**Status: OPEN.** `conjecture1_proved = False`. This document states the single
remaining inequality precisely, records the layers proven *around* it (with their
kernel-checked Lean names), and pins the exact obstructions that make it hard. It
is a target, not a result. Every numeric claim below is exact-rational and was
checked with `fractions.Fraction` (no floats at any decision point).

## 1. Where it sits

The Brualdi–Goldwasser closure reduces, on real rooted trees, to a per-hub step
inequality split into two halves by the tie boundary `23·S = 3j`:

- **Tie-dominant half** (`23·S ≤ 3j`): the hub factor is bounded by its tie value.
  **PROVEN, kernel-checked** — `TieClosure.tie_dominant_half` and the strict
  `tie_dominant_half_lt_one` (`formalization/R3Cert/TieClosure.lean`). Env-free
  pure algebra; survives the `∏env ≤ 1` retraction (see §4).
- **Near-star half** (`23·S > 3j`): the hub factor exceeds its tie value, and the
  deficit must be paid by *slack in the children* — `∏ F_child < 1`. Closing this
  half is exactly the **master inequality** below.

## 2. Statement

For a child block `C` with cavity message `μ_C ∈ (0, 1/2]`, let `F(C)` be its
F-factor and let `env★(μ)` be the **integer-achievable** F-extremal envelope at
message `μ` — the maximum of `F` over blocks whose message is `μ`, realized by the
near-star / tie / arm families at their integer-admissible points.

> **Master inequality.** For every real child block `C`,
> `F(C) ≤ env★(μ_C)`,
> with equality iff `C` is the exact tie (`μ_C = 3/23`, `F = 1`).

The near-star half follows: away from the tie every child has `env★(μ_C) < 1`, so
`∏ F_child < 1` supplies the deficit against `W·a_hub^11 > F_tie`.

### Endpoints of `env★` (all exact, all `≤ 1`, `=1` only at the tie)
| family | message μ | `env★(μ)` | value |
|---|---|---|---|
| tie | `3/23` | `1` | `1` (only equality point) |
| tie bound | `→ 26/23`* | `W·(26/23)^11` | `0.396998…` |
| arm | `1/3` | `486/529` | `0.918714…` |
| near-star `N(0,k)`, integer k | `3/(4k+3)` | `W·a_k^11·(W²·(3/2)^11)^k` | `≤ 1`, `=1` at **k=5** |

`W = 64/621`, `a_k = (4k+3)/(3(k+1))`. *the `a_hub` supremum, not a message.

## 3. Why the *weak* form is not enough

`F(C) ≤ 1` is already **unconditionally proven** — `phi_le_one`
(`PotentialFinal.lean`, Branch model, 0 sorry). The closure needs the **tight** form `F(C) ≤ env★(μ_C)`,
i.e. the *quantified slack* `1 − env★(μ_C)`, not merely non-positivity. The gap
between "proven" and "open" here is precisely this slack.

## 4. The two obstructions (why no easy proof exists)

1. **No continuous certificate.** The continuous near-star envelope exceeds 1:
   `F_ns(k)` at real `k ≈ 4.82` equals `1.000459… > 1`. Any smooth/SOS/potential
   bound valid on the real relaxation therefore *cannot* give `≤ 1` — it must be
   an **integrality (lattice) fact**. This is the retraction that killed the
   earlier `∏env ≤ 1` route; the tie-dominant half survived only because it never
   used the continuous env (pure algebra on the exact tie value).
2. **Non-monotone optimal child.** The F-maximizing child index is non-monotone in
   the hub context (`k★: 4 → 3`), so there is **no clean rearrangement / monotone
   balancing** argument reducing an arbitrary child to a near-star. The extremal
   structure is genuinely combinatorial, not order-theoretic.

The arithmetic signature of the tightness is `529/486 = 23²/(2·3⁵)`
(`near_star_ratio`, `ExactCruxes.lean`) — a 23-adic coincidence, consistent with
obstruction (1) being a p-adic/integrality phenomenon.

## 5. Provable bricks already kernel-checked (the ring around the core)

| brick | Lean name | file |
|---|---|---|
| weak form `F(C) ≤ 1` | `phi_le_one` | `PotentialFinal.lean` |
| tie-dominant half | `tie_dominant_half`, `tie_dominant_half_lt_one` | `TieClosure.lean` |
| near-star family `Φ(N(c,k)) ≤ 1`, `=1 ⇔ c+k=5` | `nearStar_family_le_zero` | `NearStar.lean` |
| arms+ties tie-monotonicity | `aHubAT_add_tie_le` | `R47LegsAT.lean` |
| ℓ≥3 legs gadget rate | `legs_rate_ge3` | `R47LegsRate.lean` |
| single-child rate `π ≤ (4/3)ρ_B^n` | `pi_le_rate` | `R47RateZBound.lean` |

Everything provable is proven. What remains is one inequality whose proof must be
arithmetic (integrality), not analytic.

## 6. Staged tools (correct-by-construction, not yet wielded)

- **Ratio-unimodality (#3, `telperion/unimodal.py`)** — for the `23²/(2·3⁵)`
  step-ratio crossing that pins the `k=5` equality.
- **p-adic valuation emitter (`telperion/emit_padic.py`)** — for the 23-adic
  content of obstruction (1).
- **Witnessed-bound guard (`telperion/witnessed_bound.py`)** — mandatory before
  any optimizer is gated by `env★`: it refuses the flat-arm phantom (`0.919` at
  `μ=0.797` where the real F-max is `0.17`) that sprang three times. Any
  near-star-half search MUST run behind this guard.

## 6b. Finite-domain validation (VALIDATED, not a proof)

The statement's *form* was stress-tested by exact enumeration (`fractions.Fraction`,
no floats at any decision) of **all 11,006 rooted blocks with n ≤ 12**:

- **`F(C) ≤ 1` for every block** (worst `F>1` = exactly 0) — consistent with `phi_le_one`.
- **The near-star family realizes the envelope**: at every near-star message
  `μ_k = 3/(4k+3)`, no block exceeds `NS(k) = W·a_k^11·(486/529)^k`. The top-F
  ladder is exactly `NS(5)=1`, `NS(4)=0.98877`, `NS(3)=0.93034`, arm `=486/529`.
- **`F = 1` is attained only at the k=5 near-star** (n=11, μ=3/23-equivalent).

This confirms the target is not mis-stated — there is no ordinary block that slips
above the near-star envelope while staying under 1. It is **finite-domain evidence
only**: the master inequality's hard cases are the large-n near-tie configurations
(n ≥ 4k+3 grows without bound), which no finite enumeration reaches. VALIDATED on
n ≤ 12; OPEN in general.

## 7. Honest boundary

This document does not advance the proof of the master inequality. It states it
precisely so the target is unambiguous and any future proof plugs into the named
bricks of §5 by unification. Until the arithmetic closes, `conjecture1_proved`
stays `False` — and no test, envelope, or continuous certificate may flip it.
