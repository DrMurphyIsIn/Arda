# Status — one-glance index

A navigable summary of where the Brualdi–Goldwasser proof campaign and the
Telperion engine stand. This page is deliberately **thin**: each row points to
the canonical document that owns the detail, so nothing here can silently drift
out of sync with the proof. `conjecture1_proved = False`.

Source-of-truth documents:
- [`telperion/PROOF_STATUS.md`](telperion/PROOF_STATUS.md) — the honest map: proven, ruled-out (with reasons), and the live leads.
- [`telperion/PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md) — the full ≤-half logical structure, every piece tagged PROVEN / VERIFIED-in-range / OPEN.
- [`PUBLICATION_LEDGER.md`](PUBLICATION_LEDGER.md) — conservative, provisional novelty tally.
- [`proof/`](proof/) — the Lean 4 formalization snapshot (R3Cert / R47 / Φ≤1) and exact-arithmetic verification harnesses.

---

## Brualdi–Goldwasser (1984): `Φ¹¹(T) ≤ 1` for all trees, equality only at the six 11-vertex ties

**The conjecture is NOT claimed proved.** What follows is the enumerated state
of a campaign in progress. Rigor tags: **PROVEN** (all *n*, machine-checked
where noted) · **VERIFIED** (exhaustive in a finite range only) · **OPEN**.

| Stratum | Statement | Status | Canonical detail |
|---|---|---|---|
| **Near-star spine** | tie `Φ¹¹(N(0,5))=1` (`64·243·23=621·576`); near-star tail `Φ¹¹(N(0,s))≤1` ∀s, eq iff s=5; asymptote `D∞<1` | **PROVEN** — arithmetic cores **Lean CI-green** | PROOF_STATUS §Proven |
| **Amplitude form** | `Φ¹¹ = (64/621)ⁿ (∏a_v)¹¹` for all trees, any root | VERIFIED n≤9 | PROOF_STATUS |
| **Integrality gate** | `tie ⟹ 11 \| n` via 23-adic valuation; `11·v₂₃(∏a_v)−n = 0` only at `N(0,5)` (tested n≤4401) | **PROVEN** (necessary, not sufficient) | PROOF_STATUS §foothold |
| **R1 single-hub** | master inequality `arm_maximal`: base (leaf) + chains + branching *analytic* steps (g-lemma unimodality over ℝ; two rational leaves) | analytic steps **PROVEN**; inductive wiring **NARROWED** (see next row) | PROOF_ASSEMBLY §R1 |
| **R1 g-step reduction** (2026-08-20) | achievability-corrected capped g-step: single-child (`0<μ≤1/2`) + two-child (unconditional) kernel-checked on `main`; abstract g-lemma `gV_le` kernel-proven over the cavity model (`g1_floors` pkg) | per-arity pieces **Lean kernel-checked** on `main`; the **full closure** `gstep_le_one_achievable` (every arity, unconditional over achievable messages) is on the PR #20 branch — **in review, pending merge** | PROOF_ASSEMBLY §R1 |
| **R2 multi-hub** | double-near-star family bound `Φ¹¹(DN(a,b))<1` ∀a,b≥2 (gluing submultiplicativity + a=2 ratio test) | **PROVEN** (family bound) | PROOF_ASSEMBLY §R2 |
| **R2 maximality** | "DN is the multi-hub Φ¹¹-maximizer at each n" | VERIFIED n≤13 — **OPEN** | PROOF_ASSEMBLY §R2 |
| **Two hardest near-1 families** | tie-recursive `hub + k·N(0,5)`; double-near-star — both strictly `< 1` | **PROVEN** | PROOF_ASSEMBLY |
| **The crux** | general competitor extremality (collective + archimedean-aware + integrality-based) | **OPEN** — the live lead is a 23-gate-strictness lemma | PROOF_STATUS §Open |

**Honest verdict** (PROOF_ASSEMBLY): the analytic content is proven; the
structural assembly is not complete. The wall is no longer an unbroken analytic
inequality — it is the completion of a strong-induction scaffold whose base and
every analytic step are individually sound, awaiting (1) review + merge of the
R1 g-step closure (PR #20 — `gstep_le_one_achievable`; on `main` the wiring
stands narrowed to that in-review theorem) plus the R1 leaf-child all-n rigor,
and (2) the R2 multi-hub maximality.

Separately machine-checked in Lean 4 (Mathlib, no `sorry`/added axioms) on the
[`proof/`](proof/) side: `per(L(T)) =` matching sum for acyclic graphs (H1
bridge) and the cavity recursion; `Φ ≤ 1` unconditional (`PotentialFinal.lean`)
including the six-point tie variety; the certified merge layer (36+36+72
positivity certificates); the (L)/(B) classification and R5/R6 shedding
lemmas (42+55 certificates); the capped-joint g-step layer
(`CappedJointAchievable.lean`, `GLemmaAssembly.lean` — the achievability
correction plus the any-arity reduction to the g-lemma). Open there: the
honest-conditional `R7'` assembly and independent review
(`proof/docs/design/R7_ARCHITECTURE.md`).

---

## Telperion — capability matrix

sympy → Lean 4 certificate pipeline. **The generator is untrusted by design;
the Lean kernel is the sole trusted component** — a defective certificate is a
compile failure, never a false theorem. Full detail in
[`telperion/README.md`](telperion/README.md).

| Area | What ships | Location |
|---|---|---|
| **Core pipeline** | `InequalityFamily` → `certify()` → validate → `emit()` → `lake build` → `freeze()`, enforced (no path from a family to Lean skips certification; `emit` refuses a red report) | `src/telperion/{family,certify,validate,emit,workflow,provenance}.py` |
| **Emitters / shapes** | Direct Pólya, Bilinear Box, SOS, ExactFact/Identity, ℕ-reparam (`Nat.cast_sub`), case-dispatch (`interval_cases`) assembly, subdivision glue, variable-map, dichotomy (`le_total`), symbolic-tail (`∀K≥K₀`), cone/Farkas, unimodal-max, telescoping potential, lattice box, log-concave single-point, monotone-ratio tail, interlacing (Newton), WZ (hypergeometric sums), custom | `emit.py`, `emit_facts.py`, `emit_adapters.py`, `tails.py`, `varmap.py`, `dichotomy.py`, `emit_*.py` |
| **Positivstellensatz / integer arithmetic** | Handelman (polytope), Putinar constrained-SOS (semialgebraic), Nullstellensatz (ideal membership), infeasibility (`1 ∈ ⟨gⱼ⟩` refutation), SOS refutation (`−1 =` SOS, real-unsat), real Nullstellensatz, equational consequence (Gröbner → `linear_combination`), Chvátal–Gomory integer rounding (`CGRoundEmitter`, VIPR-style, discharged by `omega`) | `emit_handelman.py`, `emit_constrained_sos.py`, `emit_nullstellensatz.py`, `emit_infeasible.py`, `emit_sos_refutation.py`, `emit_real_nullstellensatz.py`, `emit_consequence.py`, `emit_cg_round.py` |
| **Certificate finders (checker → searcher)** | `find_handelman_certificate` (exact, sympy-only basic-feasible enumeration) · `find_putinar_certificate` (numeric SDP → exact rational rounding, LDLᵀ + reconstruction check over ℚ). Untrusted by design: every found certificate is re-verified exactly; a search miss is a refusal, never a wrong theorem | `emit_handelman.py`, `emit_constrained_sos.py`, `sos_sdp.py` |
| **Pólya engine** | `polya_lift` (multiply through by `(1+Σxᵢ)^N`), recursive box subdivision, SOS for the rationalizable subset | `certify.py`, `sos.py` |
| **Diagnostics / honesty** | `diagnose` triage (FALSE-with-witness / NOT_POLYA / CERTIFIABLE), tie-variety + margins, counterexample hunt (incl. GA/MAP-Elites transfer), relax probe, nonvacuity gate (refuses reflexive/vacuous emitted statements; identity certificates must be load-bearing), witnessed-bound gate (anti-phantom: an existential bound must ship its witness) | `diagnose.py`, `margins.py`, `hunt.py`, `counterexample_hunt.py`, `relax.py`, `nonvacuity.py`, `witnessed_bound.py` |
| **Provenance / drift** | SHA-256 input-hash freeze, `verify` drift net (quick/heavy/audit groups), byte-stable rendering across sympy versions, `latex` sync (same hash), pure-stdlib third-party `recheck` | `provenance.py`, `recheck.py`, `latex.py`, `telperion.toml` |
| **Surfaces** | **CLI**: `init certify probe diagnose emit·via·verify margins ties latex hunt relax sharpen ledger status cilog recheck export-certs package review-brief`. **MCP**: `polya_probe certify_family emit_family diff_family read_manifest`. **Claude plugin/skill** | `cli.py`, `mcp_server.py`, `claude-plugin/` |
| **Production families (kernel-checked in CI)** | toy_box; R47 (216 thms); G1 floors (3260); R7 star-of-hubs (972); two-hub (4656); shed/legs/interp/h_floors | `examples/`, `.github/workflows/telperion-production.yml` |
| **CI gates** | `telperion-test` (unit + drift, sympy matrix) · `telperion-production` (compile gate over frozen Lean) · `telperion-casestudy` (R47 re-cert) · `telperion-lean-e2e` (regen→compile toy) · `telperion-audit` (heavy re-verify + hunt) | `.github/workflows/` |

Version `0.1.6`. Core dependency: sympy (`sdp` extra adds cvxpy for the SDP
finders). The BG graph-certificate modules additionally use networkx (lazy
import; install the `bg`/`dev` extra).
