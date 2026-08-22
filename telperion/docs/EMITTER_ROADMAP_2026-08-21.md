# Telperion emitter roadmap — necessities from the BG and P=NP campaigns (2026-08-21)

A prioritized plan for expanding Telperion's certificate-skill set, derived from a
gap analysis of the two active research proof campaigns in this repo: the
**Brualdi–Goldwasser (BG)** Laplacian-ratio proof (`proof/`, `telperion.bg`) and
the **P vs NP / knapsack-SoS / 3-XOR** ladder (`proof/verification/knapsack_sos`,
the `rational_identity` / `finite_decide` / `fwd_telescope` emitters). Each item is
a recurring certificate shape that is currently **hand-rolled, named-open, or a
Lean stub** — a reusable emitter would crystallize it into kernel-checked Lean.

Selection principle: prefer emitters whose emitted Lean uses the **deterministic,
search-free tactics that reliably compile** (`ring` / `positivity` / `linarith` /
`norm_num` / `omega` / `decide` / `linear_combination`) over ones needing tactic
search or an SDP solver. Exact-arithmetic (sympy-only) beats cvxpy-gated.

## Shipped from this analysis
- **`PSDFormEmitter`** (2026-08-21, this doc's first installment) — `0 ≤ xᵀMx` for
  an explicit rational **positive-definite** `M` via exact LDLᵀ congruence
  (`ring`+`positivity`, cvxpy-free). The deterministic PSD primitive both
  campaigns recur on (moment matrices, Gram bridges). Extensions below (B1).

## Cross-cutting theme
The single most-recurring shape across **both** campaigns is **"this explicit
rational symmetric matrix is positive (semi)definite"** — moment matrices (SoS
pseudo-expectation), block-rank-one PSD (3-XOR closure), and BG Gram bridges. The
LDLᵀ primitive (shipped) is the base; the symbolic-in-parameter and singular-PSD
generalizations are the highest-leverage follow-ups.

## Prioritized backlog

### P=NP / SoS ladder
| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| P1 | **SymmetricQuadForm** (symbolic-n moment PSD) | degree-d moment matrix PSD, *symbolic in n*, as a `Finset` congruence (harmonic block + rank-one collapse + CS remainder) | `examples/knapsack_sos/D2_CERTIFICATE.md`, `Hsq.lean` (d=1 template); d≥2 mechanical | `Finset` induction + `positivity`; mirror `Hsq.lean` | M–L | sympy |
| P2 | **XorClosureStructure** | per-instance 3-XOR width-2d GF(2) closure → block-rank-one PSD; converts `gen_xor3_duality.py` (one-off template) to a reusable emitter | `xor3_pseudoexpectation.py`, `Xor3Structure.lean` | `decide` over enumerated closure data (like `finite_decide`) | M | ℤ/exact |
| P3 | **PolytopeMaxMonotone** (Handelman Route B) | `∀x∈P, p(x) ≤ B` via corner dispatch + per-edge monotone slice — closes g-step Case-2 `q≥4` without the Handelman variable-explosion | `proof/docs/GSTEP_HANDELMAN_RECIPE.md` (Route B) | `interval_cases` corners + `MonotoneRatioTail` edges + `cone`/`linarith` | L | sympy |
| P4 | **SecondOrderRecurrence** (Hahn 3-term) | `A(q)f(q+1)+B(q)f(q)+C(q)f(q-1)=0` closed forms (Krawtchouk/Jacobi) — generalizes `fwd_telescope` to 2nd order; Laurent max-cut W2 moments | `examples/knapsack_sos/FULLRANK_W2_SCOPING.md` | `Nat.le_induction` (two-step) + `ring` | M | sympy |

### BG Laplacian-ratio proof
| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| B1 | **SingularPSD / rank-revealing LDLᵀ** | extend `PSDFormEmitter` to positive-*semi*definite (zero pivots → rank reduction) — needed wherever a moment/Gram matrix is singular at a tie | BG Gram bridges; moment ties | LDLᵀ-with-pivoting congruence + `positivity` (drop zero-weight squares) | M | sympy |
| B2 | **SeparableConvexExtremum** (vertex / homogeneous) | max of a separable convex `Σφ(xᵢ)` over a fixed-sum box is at a **vertex**; min is at the **homogeneous** point (kink-pinned) — the CRITICAL heterogeneous→homogeneous reduction | `proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md` (vertex lemma, kink); unifies R3/capped-joint/g-step | `ConvexOn.map_sum` + spreading-exchange induction + `norm_num` (kink value) | L | sympy+`norm_num` |
| B3 | **IntegralityGate** (p-adic obstruction family) | a finite exceptional table + a **uniform p-adic valuation certificate** forcing an equality/tie only when `p ∣ n` (the 23-gate strictness) | `telperion.bg.sporadic_tie`; PROOF_STATUS.md lead #1 | `PadicValuationEmitter` (`norm_num` divisibility) + finite dispatch | M | sympy |
| B4 | **RecursiveDominationRatio** | `Φ(T) ≤ Φ(T_tmpl)` via a rational domination ratio `r(params)=P/Q > 1` (all-nonneg-coeff) over a multivariate parameter family — R7 competitor-extremality | `Depth3Single.lean` (1-param done); R7 multivariate numerical-only | clear denominators → `nlinarith`/`cone`; envelope → subdivide+glue | M–L | sympy |
| B5 | **AchievabilityClosure** | replace a relaxed inequality (false on the full domain) with its restriction to **achievable** values (e.g. cavity messages `μ=1/(j+1+S) ≤ 1/2`) | `CappedJointAchievable.lean` (PR #20 pattern) | achievability characterization + `le_iff_lt_or_eq` domain filter | S | sympy |

## Suggested build order
1. **`PSDFormEmitter`** — shipped (base primitive). 
2. **B1 SingularPSD** — small extension of the shipped emitter; unlocks the singular moment/Gram cases both campaigns hit.
3. **P2 XorClosureStructure** — `decide`-based (robust), converts a one-off generator to a reusable emitter; mechanical, no new math.
4. **B3 IntegralityGate** — robust `norm_num` divisibility; closes BG live-lead #1's arithmetic.
5. **P1 SymmetricQuadForm** — the marquee P=NP unblocker (mirror `Hsq.lean`); higher Lean risk, do once B1 is in.
6. **B2 / P3 / B4 / P4 / B5** — research-heavier; schedule against the campaigns' open fronts.

Every item above discharges a named-open in the respective proof state; none
duplicates an existing emitter (checked against the README shape table). The
kernel (via cloud CI `lake build`) remains the sole gate — a wrong certificate is
a compile error, never a false theorem.
