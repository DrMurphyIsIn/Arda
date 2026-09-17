# RH campaign consolidation — the wall map + kernel ledger (2026-09-16)

*Consolidation of the recent RH work across two tracks: the Turing-ladder climb
(`rh/million-turing`) and the arithmetic-FQ / reverse-Dyson wall-map
(`research/arithmetic-fq-membership-spec`). Standing invariant throughout:
`conjecture1_proved = False` — none of this proves RH.*

## 1. The four-sweep wall map (ANALYZE-GRADE — a diagnostic, not a kernel theorem)

Four adversarial axis-sweeps mapped *why* partial footholds cannot reach RH from any
coordinate direction. Each axis's verdict, and how it fails to reach the temperedness/
growth wall:

| Axis | Verdict | Mechanism |
|---|---|---|
| Weight (multiplicativity) | **FREE** | does no work — conservation of difficulty |
| Ordinate (S(t) statistics) | **ORTHOGONAL** | Selberg 2nd moment is real but reflection-blind |
| Horizontal (real-part single-coord) | **FREE-OR-RH** | blocked structurally by reflection invariance |
| Joint (real-part × ordinate) | **RH-IRREDUCIBLE** | breaks reflection only via the prime side → Weil positivity = RH |

**Completeness:** all four reduce to the SAME single clause — temperedness/growth of the
prime-side object (= Weil positivity = the corridor-bound wall). The reflection
(β,γ)→(1−β,γ) is a symmetry of the zero SET ITSELF (Λ(s)=Λ(1−s)+conjugation), so any
zeros-only functional is reflection-blind; only the Euler-product/prime side breaks it,
and controlling it to infinite height for all test functions IS RH. The missing idea must
be an unconditional, infinite-height, ASYMMETRIC joint coupling.

**Cross-connection:** the certified million-zero Turing ladder (argument-principle winding
box-localization) is the FINITE pointwise instance of exactly that joint coupling —
a landmark, not a lever; PRZZ (>5/12 on-line) is the uniform-proportion landmark.

**HONESTY:** sweeps 1–3 completed; sweep 4's Refute phase rate-limited across three attempts
(server throttling, not usage) → the joint-axis "RH-irreducible" verdict rests on the
analyze agents' self-disclosed limitations + synthesis + 2 verified citations (BGSTB
arXiv:2306.04799, Groskin arXiv:2607.02828), NOT on completed adversarial refutation.
Analyze-grade. A throttled verifier is not a refutation.

## 2. Kernel-verified ledger (the part that COUNTS)

- **RvMUnboundedMeanDensity DISCHARGED** — unconditional, 3-axiom, double-confirmed by two
  sessions' own `#print axioms` (`rh/rvm-port`, `a2a0462a7`; ported from
  cc-chen-tech/riemann-pnt-lean4). The roadmap's five-consumer critical-path blocker.
- **Reflection trilogy complete** — `OrdinateInsensitivity.lean` 7/7 theorems 3-axiom
  (`research/arithmetic-fq-membership-spec`, `ed7c94a72`): `Gammaℝ_conj`,
  `completedRiemannZeta_conj_ne`, `same_ordinate_partner` (nontrivial zero ρ → partner
  1−conj ρ at the SAME ordinate, mirrored real part) — the precise kernel reason the
  ordinate foothold is reflection-blind.
- **Turing ladder: 1,000,000+ certified** — T=640,000, N=1,072,715 kernel-clean on Re=½,
  tiling contiguous 0-gaps, N-exact vs `zeta_nzeros` (leg 26, `6b36d7909`). Leg 27 (→680,000)
  rebuilding at consolidation time (a full rebuild triggered by a disk-crisis ir-prune;
  sound, verified by guard on completion).
- Count-drift audit flag reconciled (sum-of-band-n over-counts by design; N(T) authoritative).

## 3. New Telperion capabilities captured (this consolidation)

- **skill `adversarial-axis-sweep`** — the wall-mapping methodology (analyze → refute →
  synthesize; throttle≠refutation; kernel-probe-shapes-only).
- **skill `external-lean-port`** — probe → bridge → size → drift-bellwether → port → verify
  (the RvM discharge pipeline), with disk discipline.
- **emitter `emit_reflection_halving`** (on the arithmetic-FQ branch) — the reflection-
  invariance no-go-certificate shape.

## 4. Branch ledger (all pushed to origin)

`rh/million-turing` (ladder + B2 tooling), `rh/rvm-port` (RvM discharge), `rh/b1-li-prefix`,
`rh/c-dbn-scaffold`, `rh/e7-corridor-scope`, `rh/routes-node-proofs`, `b2/shard-migration`,
`research/arithmetic-fq-membership-spec`. Main-ward integration = statement packages +
these skills/docs (steward owns main; raw corpus stays on the branches). `conjecture1_proved
= False`.
