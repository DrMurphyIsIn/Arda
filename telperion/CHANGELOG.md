# Changelog

## 0.1.0 (2026-08-15/16) — extraction + hardening

Born from the Brualdi–Goldwasser campaign (`../proof/`), where the pattern
produced 200+ CI-green Mathlib theorems.

**Core**: `InequalityFamily` (direct + bilinear-box), `certify()` with
structural refusals, three emitter kinds (Polya batches, ℕ-reparam adapters,
`interval_cases` assemblies), enforced certify→validate→emit→freeze workflow,
input-hash provenance, byte-stable rendering across sympy versions.

**Hardening round 1**: `diagnose` refusal triage (FALSE with exact witness /
NOT_POLYA with remedy hints / CERTIFIABLE); structural lint gate inside
`emit()`; `ShardSpec` file sharding with cross-shard imports; `telperion.toml`
manifest + `verify` drift net (fails on unlisted generate scripts);
fuzz/property tests.

**Hardening round 2**: `safe_parse_expr` token whitelist on every
string-taking surface (CLI probe/diagnose, MCP tools) — sympy's parser is
never fed raw input; `telperion init` project scaffolding (family template
with the validation discipline built in, pinned Lean shell, drift manifest,
lean-verify workflow); `certify(progress=)` + `certify -v` for long runs;
path-hashed module loading (family.py can't shadow installed modules);
`CustomAssemblyEmitter` escape hatch for hand-designed assemblies.

**The Pólya engine**: `polya_lift` (multiply through by `(1+Σxᵢ)^N` — Pólya's
theorem as an algorithm; certifies strict positivity, provably cannot converge
at equality cases) integrated as `family.auto_lift` / `polya_certify(lift_max)`;
recursive box subdivision (`auto_subdivide` on corner refusals,
`force_subdivide` to isolate tie regions) producing leaf cells plus
`SubdivisionGlueEmitter`'s `le_total` case-split glue reconstructing the
original cell theorem; diagnose now reports the exact lift exponent when one
exists, and names the tie obstruction when none does.  Toy example gains
ToyLift and ToySplit — both new shapes compile against pinned Mathlib in CI.

**Tie-variety extraction + margins** (`margins.py`, CLI `margins`/`ties`, MCP
tools): the exact equality cases of every certificate — combinatorial tie
faces via minimal hitting sets for certified (nonneg-coefficient) numerators
(with the structural corollary: certified instances have no interior ties,
which is exactly why interior-tie claims need the arithmetic treatment),
exact real roots for refused univariate claims; per-certificate margin reports
(constant-term floor + exact-rational sample minimum with argmin), tight
instances first.  diagnose now names the tie points when lifting fails.

**Wishlist 3–7**: `telperion latex` — paper appendix / leanblueprint nodes
stamped with the SAME input hash as the Lean (sync checkable by comparing two
hex strings); symbolic-tail families (`TailFrom` axis: finite table + one
``K = K₀ + t`` certificate, `TailNatEmitter` emitting the ℕ-quantified
``∀ K ≥ K₀`` theorem; the certifier's integrality check even catches int/int
float contamination in user targets); exact SOS certificates for the
rationalizable subset (even powers + iterated quadratic completion — reaches
interior-tie shapes lifting cannot; surfaced via diagnose); CAS-neutral
certificate interchange (JSON with expression ASTs + a PURE-stdlib
`recheck.py` — coefficient signs, factor positivity, Schwartz–Zippel identity
spot-checks in `fractions` — a third independent verifier beside sympy and the
Lean kernel); `certify(workers=N)` fork-parallel certification;
`telperion package` reviewer bundles (family + frozen + certificates.json +
standalone rechecker + generated REVIEWING.md).

**The honesty engine** (from a review of what made the origin proof
possible): (1) tie pinning — `family.ties`/`family.anchors` declarations; the
certifier asserts the target AND the certificate vanish exactly at declared
ties (the campaign's overclaim trap, which killed three false proofs, as a
standing invariant) and that anchors evaluate exactly (the pi(T(3,3,3)) =
19683/256 pattern); (2) the relaxation probe (`telperion relax`) — the
campaign's decisive maneuver as a tool: interpolate an integer grid axis
continuously and hunt for exact violations; ARITHMETIC verdict with witness
means no smooth certificate can close the family; (3) the adversarial hunt
(`telperion hunt`) — exact-rational minimization in three modes: coordinate
descent, GA with memetic descent refinement (the Arda evolution engine's
transferable core), and a MAP-Elites quality-diversity archive returning
DIVERSE near-tight points (tie varieties have many points; a pure minimizer
finds one — demonstrated: both basins of a bimodal tie landscape recovered
exactly). diagnose escalates from sampling to hunting before concluding
NOT_POLYA. Deliberately not ported from Arda: Rust kernels (audit surface),
island/climate machinery (overkill). Named future step: pluggable hunt
domains (the origin hunted over TREES via Prufer sequences).

**Route ledger + executable status** (the collaboration layer from the
history review): `--ledger` on diagnose/relax/hunt appends refused routes and
exact disproofs to a deduplicated, fingerprint-keyed JSON ledger
(`telperion ledger` renders ROUTES.md) — the origin's `*_nogo*` convention as
infrastructure, so nobody re-attempts a dead route blind.  `telperion status`
generates STATUS.md by EXECUTING every manifest check (theorem counts and
input hashes read from frozen manifests; verdicts never asserted), with the
origin's reminder that green certificates do not by themselves prove a
surrounding conjecture.  `telperion review-brief` fills the adversarial
review checklist with the family's actual facts — and nags when ties or
anchors are undeclared.

**Identity families + kernel facts** (second history-review run, items B+C):
`equation=(lhs, rhs)` claims — certified by exact symbolic zero-check, emitted
by `IdentityEmitter` in the proven field_simp shape with a RAW tree renderer
that preserves the author's spelling (a together-based render had produced a
vacuous `1 = 1`; construction-time evaluation caveat documented — use
UnevaluatedExpr/evaluate=False when spelling matters); identities flow through
interchange/recheck (stdlib identity spot-checks) and latex.
`ExactFactEmitter` + `fact_pow`/`int_expr_lean`: kernel integer/rational facts
in unevaluated-power spelling closed by decide/norm_num — regenerates the
origin's `s_tail_crux : (3:ℤ)^317 * 2^81 ≤ 23^129 := by decide` verbatim, and
makes VerifiedConstant brackets emittable. Closes two named-opens.

**The second-brainstorm batch (A, D–H)**: witness-search claims
(`family.witnesses` — the per-residue comparator pattern as API: existential
claims, first certifiable candidate wins, label recorded and exported: the
winner-table pattern); the sharpness probe (`telperion sharpen` — bisect a cap
between the CERTIFICATE boundary and the TRUTH boundary; the gap is the room a
better method could win — the G3/G4 cap-widening question as a tool);
`emit --pilot N` (validate the template on N instances in CI before a
972-theorem batch — the campaign's first-try-green ritual as a flag);
`telperion cilog` (the Lean-failure knowledge base: seven hard-won gotcha
classes as executable diagnostics, error COUNT always reported first);
`per_node_family` + `fixed_points` (the telescoping-potential shape's
achievable half: per-node inequality families with the step map's fixed point
as the pinned tie — full induction emission stays the v2 headline); exact cone
membership (`cone_combination` — target = Σ λᵢ·basisᵢ with λ ≥ 0 decided in
exact rational arithmetic; the LP cutting-plane maneuver's solvable core,
float-guided LP for the underdetermined case named-open).

**Third-brainstorm batch (L, M, K)**: dual-engine validation as API
(`family.independent_target` — a pure-Fraction second implementation
cross-checked exactly at certification; the pi(T(3,3,3)) pattern, which had
already caught the nsimplify bug when hand-rolled); the persistent
certification cache (`certify(cache_dir=)` + `DiskCache`/`memoize` — content-
hash-keyed Polya results incl. cached refusals; performance layer only, the
drift net and kernel stay the arbiters; justified by the 972-cell run's
redundant-search profile); interval symbols (`interval_family` — bracket-
quantified claims `∀ ρ ∈ [lo,hi]`, multilinear per bracket, LOWERED onto the
bilinear-box machinery with floors: zero new emitters, the emitted _cell
theorem IS the quantified statement; composes with ExactFact bracket lemmas —
demonstrated on a miniature G1 floor claim over the campaign's real
log-bracket constants).  The G1 floor stratum is now expressible end to end.

**J + I (completing the three brainstorms)**: unimodality certificates
(`unimodal_certificate` — the near-star integrality proof's shape composed
from existing primitives: ratio log-concavity as a symbolic-tail Polya claim,
exact crossing localization, and EXACT TIE detection when r(s*) = 1 — the
R(5) = 1 double-maximum pattern reported rather than glossed; closes the loop
the ARITHMETIC relax verdict opens); Farkas dual witnesses (`cone_decide` —
cone refusals upgraded to verified impossibility proofs: an exact functional
with y·basisᵢ ≤ 0 and y·target > 0, for both inconsistent systems and
forced-negative weights; 'change the basis, not the search'); declared-
complete witness spaces (`witnesses_complete=True` — exhaustion becomes
PROVEN IMPOSSIBLE, ledger-ready).

## 0.1.1 (2026-08-16) — the review cycle, absorbed

**The G1 review response** (REVIEW_20260816_TELPERION_G1: PASS math/honesty,
FAIL shipped Lean): the empty-symbol emission bug (`def c1 ( : ℝ)` — the
"empty-syms guard" had fixed a crash, not the emission) repaired; a lint rule
for the class; `telperion-production.yml` — the COMPILE GATE over frozen
production artifacts (regen-diffs check bytes, tests check mathematics, only
`lake build` checks that shipped Lean is Lean); version discipline learned
(emission changes must bump — the input hash covers inputs, not the emitter's
code; every family refrozen under 0.1.1).

**Fourth-brainstorm batch (N, O, P, Q, R, S)**: typed hole contracts in
`render()` (empty binders now UNCONSTRUCTIBLE — caught at fill time, before
lint, before freeze); the cost ledger (`certify(profile=, budget_seconds=)` +
`profile_report` — the R7 45-minute blind grind, never again); variable-map
adapters (`MapSpec`/`VarMapAdapterEmitter` — the campaign's most-used
maneuver generalized: substitution glue in original variables, subsuming the
reparam shape); dichotomy glue (`DichotomyGlueEmitter` — le_total case
splits over declared thresholds, the classification-not-surgery pattern);
gate negative-controls (every known-bad artifact class PROVEN red in its
gate — silence from a gate is indistinguishable from safety); bracket
adequacy (`margins --adequacy` — the MR69 ΔCHARGE fragility class as a
report; FIRST RUN on G1 found exactly one FRAGILE cell in 514: a (2,0,1)
tax-window leaf at 0.59 of its bracket width).

**Named open items** (deliberately not shipped as stubs): `python-flint` fast
path (sympy expand/together dominates the profile, so a flint coefficient pass
would be decorative until the conversion layer is done properly);
bilinear-family built-in assembly (use `CustomAssemblyEmitter`); Kind-3
multi-axis grids; the SOS Lean-emitter path (certificates found by sos.py are
surfaced in diagnose but not yet emitted — needs a squares-aware skeleton);
incremental per-instance certification caching; bilinear tails; retrofitting
the R7 star-of-hubs family onto the witness API (it hand-rolls the search);
float-guided LP for underdetermined cone membership; the generic Lean lemma for
unimodal integer maxima (the emitted pieces close its hypotheses; the
induction skeleton is documented); generic induction
emission for telescoping potentials (the v2 headline); hunt over pluggable
combinatorial domains.

## 0.1.3 (2026-08-28) — first application beyond Brualdi–Goldwasser

**Turán / Laguerre inequalities for the Riemann ξ** (`turan.py`,
`examples/turan_xi/`): the exact-rational→kernel-Lean pipeline pointed at an
RH-*adjacent* family. RH ⟹ ξ ∈ Laguerre–Pólya ⟹ its even Taylor coefficients
`a_k = [z^{2k}] ξ(1/2+z)` satisfy `a_k² ≥ a_{k-1}a_{k+1}` (Csordas–Norfolk–Varga
1986; *necessary*, never sufficient). `TuranEnclosureCertificate` certifies the
finite algebraic step — given imported rational enclosures `lo_k < a_k < hi_k`,
the strict Turán inequality follows from the worst-corner margin
`hi_{k-1} hi_{k+1} < lo_k²` (`norm_num`), bridged by the once-proved
`turan_from_enclosure` monotonicity lemma (`nlinarith`). Indices k=1,2,3 emitted
(margins +7.06e-5, +5.68e-9, +2.00e-13). The transcendental import
(`compute_enclosures.py`, mpmath Cauchy-contour Taylor extraction, two-radius
cross-check to >40 digits) is kept OUT of the sympy-only core; the enclosures
enter Lean as hypotheses.

**Honest scope, stated in the module, the README, and here**: this is NOT
progress toward RH. Turán is necessary-only; k=1,2,3 is finite (the all-k result
is CNV 1986, an analytic theorem this tool does not reproduce); the enclosures
are numerics-as-hypotheses, not interval-proven in-kernel. The genuine
obstruction — a transcendental, zeta-zero-dependent quantity with no uniform-in-k
rational certificate — is exactly the class of wall the Brualdi–Goldwasser crux
also hit (no finite smooth certificate; content is arithmetic/analytic). The
tool holds the scaffolding at each fixed k; it does not manufacture the analytic
bound. Real next step (not shipped): *formalizing* the CNV all-k proof or the
Griffin–Ono–Rolen–Zagier (2019) hyperbolicity theorem, with Telperion emitting
the polynomial-inequality lemmas.

**`ExpBracketCertificate`** (`exp_bracket.py`): the bespoke
`examples/exp_bracket/` far-constant generalized into a reusable certificate —
the rigorous rational bracket `1−θ ≤ exp(−θ) ≤ hi` for any (θ, N), emitted as the
two Mathlib-backed theorems (`Real.sum_le_exp_of_nonneg` upper, `Real.add_one_le_exp`
lower), with `.check()` verifying `tfloor ≤ Taylor_N(θ)` and `1/tfloor ≤ hi` in
exact rationals and `suggest`/`build` auto-filling the numerals. Reproduces the
committed `exp_bracket` artifact **byte-for-byte** (subsumption test). Motivation:
the honest correction to the Turán↔BG assessment — the H2-Bridge exp sites
(`BridgeStep4*`, `LemmaA`, `R47RateZBound`) needed a *derive-side* generalization
of `exp_bracket`, **not** the consume-side `TuranEnclosureCertificate` (which does
not generalize it — opposite pipeline stages; see `turan_xi/BG_APPLICABILITY.md`).
Added additively; migrating the existing example onto the class is left to the
Bridge/H2 owner, with the byte-subsumption test as the safety net.

**Degree-3 Jensen–Pólya hyperbolicity for ξ** (`jensen.py`,
`examples/jensen_xi/`): the cubic rung above `turan_xi` (= degree 2).
`CubicJensenCertificate` certifies the cubic Jensen polynomial `J^{3,n}` of ξ is
hyperbolic (discriminant `Δ = 162g0g1g2g3 + 81g1²g2² − 108g0g2³ − 108g1³g3 −
27g0²g3² > 0`, ⟺ three real roots) for shifts n=0,1,2, via an exact worst-corner
bound (positive monomials at `lo`, negative at `hi`) and a once-proved monotone
bridge `cubic_jensen_pos_of_enclosure` (five `mul_le_mul` monomial chains +
`nlinarith`). Normalization fixed empirically and stated: `γ_k = k!·a_k` (EGF of
`G(u)=Σa_k u^k`, whose Laguerre–Pólya membership ⟺ RH) gives hyperbolic Jensen
polys; `(2k)!·a_k` does not. Tests include a numpy confirmation the certified
cubics are genuinely real-rooted and a 16-corner check that `Δ_lo` is a true
lower bound. Honest scope identical to `turan_xi` (RH-necessary, finite,
enclosure-conditional) plus: not yet `lake`-built (bridge hand-verified, not
machine-checked locally per the SoC hazard). Degree 4+ is the next rung.

**Two more RH-necessary lenses** (`newton_xi`, `toeplitz_xi`): breadth beyond the
Jensen-hyperbolicity ladder.
- **Newton inequalities** (`newton_xi`): the correctly-normalized log-concavity
  `γ_k² ≥ γ_{k-1}γ_{k+1}` on the Jensen sequence `γ_k = k!·a_k` — sharper than the
  raw-`a_k` Turán (`a_k² ≥ ((k+1)/k)a_{k-1}a_{k+1}`) and the pairwise necessary
  condition for hyperbolicity. Product-vs-square, so it *reuses*
  `TuranEnclosureCertificate` (no new Lean). k=1…6.
- **Total positivity** (`toeplitz_xi`, `toeplitz.py`): a different framework —
  RH ⟹ `G(u)=Σa_k u^k` is a Pólya-frequency function ⟹ its Toeplitz matrix is
  totally positive (Edrei–Thoma). New module `ToeplitzMinorCertificate` certifies
  the 3×3 minors (`a_m³ − 2a_{m-1}a_m a_{m+1} + a_{m-1}²a_{m+2} + a_{m-2}a_{m+1}²
  − a_{m-2}a_m a_{m+2} > 0`) for m=2…5 via a worst-corner `toeplitz3_pos_of_enclosure`
  bridge (five `mul_le_mul` chains + `nlinarith`); tests include a 32-corner
  lower-bound check. Same honest scope (RH-necessary, finite, enclosure-conditional,
  not lake-built).

Quartic (degree-4) Jensen hyperbolicity was validated numerically (`Δ₄>0 ∧ P<0 ∧
D<0` for n=0…5, matching root-checks) but NOT shipped: the discriminant bridge is
~16 monomials of degree 6, too large to hand-verify safely without a local Lean
build. It is the first thing to build once the RH examples get a CI `lake` gate.

**CI `lake` gate — the RH line is now KERNEL-PROVEN** (`examples/rh_lean/`,
`telperion-rh-lean.yml`): a lake library aggregates the frozen emitted Lean
(turan/jensen/toeplitz/newton hyperbolicity + exp/log/pi brackets) and CI
`lake build`s it against pinned Mathlib v4.32.0. First run: **green in 3 min** —
every hand-verified `mul_le_mul`/`nlinarith` bridge compiles, so the whole
RH-necessary + transcendental line is now kernel-checked, not just hand-verified.
`build.py` assembles/drift-checks the library from frozen (source of truth).

**Fourth transcendental skill + deep-transcendental roadmap** (`sqrt_bracket.py`,
`examples/rh_lean/DEEP_TRANSCENDENTALS.md`): `SqrtBracketCertificate` — the √
primitive the roadmap identifies as the next rung (needed for tight-`log` range
reduction *and* the Cohen–Villegas–Zagier path to `ζ(1/2)`). `lo ≤ √(n/d) ≤ hi`
over exact rationals (`lo² ≤ q ≤ hi²`), proved robustly by `Real.sqrt_sq` +
`Real.sqrt_le_sqrt` (no fragile iff-direction), cross-checked vs `iv.sqrt`. The
roadmap grounds the honest ceiling: `iv.zeta` is broken and the η-series is too
slow (`1/√N`), so even Python rigorous `ζ(1/2)` needs CVZ acceleration; in-kernel
`ζ(1/2)` is a focused formalization (one new analytic tail lemma) and `a_k` is
research-scale (needs `ζ`/`Γ` derivative brackets). Ships **zero** proofs for the
deep gap — the doc is a plan, kept out of the kernel-proven `RH` library.

**Third transcendental skill** (`pi_bracket.py`): `PiBracketCertificate` emits
`3.141592 < Real.pi < 3.141593` proved verbatim by Mathlib's
`Real.pi_gt_3141592`/`Real.pi_lt_3141593` (decimal literals matching Mathlib, no
defeq bridging); `check()` cross-verifies against mpmath's rigorous interval
`iv.pi`. π is load-bearing in ξ's `π^{-s/2}` factor.

**Second transcendental skill** (`log_bound.py`): after `exp_bracket`, a
`LogBoundCertificate` — the *transcendental* half of the toolchain, where the
theorem's Lean statement contains `Real.log` and the bound is DERIVED in-kernel
(`Real.log_le_sub_one_of_pos` + `Real.log_inv`), not imported. Emits the coarse
rigorous bracket `1 − d/n ≤ log(n/d) ≤ n/d − 1`. Honest limits: coarse (tight only
near 1; range-reduction via Mathlib's `Real.log_two_*` + a near-1 series is the
noted-not-shipped tight version); applies to the *archimedean* RH pieces (Li-trend
`(n/2)(log n − …)`, zero-free constants) but NOT the deep transcendentals
(`ζ(1/2)`, Stieltjes constants, the `a_k` themselves) — those need in-kernel
`ζ`/`Γ`-derivative bounds Mathlib does not have. That gap is the honest ceiling on
making the `turan_xi`/`jensen_xi`/… certificates unconditional.
