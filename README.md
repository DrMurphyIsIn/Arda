# Arda

Machine-checked progress on a 42-year-old open problem in extremal graph theory,
and the tooling it produced.

**The question (Brualdi–Goldwasser, 1984).** Which tree `T` on `n` vertices
maximizes the Laplacian ratio

```
pi(T) = per(L(T)) / prod_v deg(v)
```

— the permanent of the Laplacian, normalized by the degree product? Equivalently
(since `per` is multilinear in rows): which tree's simple random walk maximizes
`per(I - P)`? The determinantal shadow of this quantity is identically zero
(`det(I - P) = 0` for every graph); all of its content lives in what the
determinant's sign cancellations destroy.

**Status, honestly stated: the conjecture is NOT claimed proved.** This
repository is a peer-review package for a proof campaign in progress. What *is*
machine-checked, in Lean 4 against Mathlib with no `sorry`, no added axioms, and
no `native_decide`:

- `per(L(T)) = ` matching sum for acyclic graphs (the H1 bridge), and the exact
  cavity recursion connecting it to a Branch model (`Matching.lean`,
  `CavityTree.lean`, `BridgeStep2`–`4j`);
- **`Φ ≤ 1`** — the central branch inequality, unconditional
  (`PotentialFinal.lean:phi_le_one`), including the six-point rational tie
  variety where `Φ = 1` exactly;
- the **certified merge layer**: every Balanced∧Capped hub-backbone state
  rewrites monotonically in `per L/∏deg` to an ordered-merge normal form
  (`R47StepMono.lean:chain_to_normalForm`), via 36 + 36 + 72 generated
  positivity certificates;
- the (L)/(B) classification layer, the R5/R6 shedding lemmas (42 + 55
  certificates), and the raw-tree → Branch rate-port parse;
- the **capped-joint g-step layer** (2026-08-20, `GStepCore.lean`,
  `CappedJointConfig.lean`, `CappedJointAchievable.lean`, `GLemmaAssembly.lean`):
  the achievability-corrected Case-2 hypothesis (the unconstrained form is
  *false* on `μ ∈ (1/2, 1)`; non-leaf cavity messages satisfy `μ ≤ 1/2`), the
  kernel-checked single-child (`0 < μ ≤ 1/2`) and two-child (unconditional,
  no achievability needed) g-step bounds, and the assembly bridge toward the
  abstract g-lemma `gV_le`, itself kernel-proven over the cavity model in the
  standalone
  [`telperion/examples/g1_floors/lean/`](telperion/examples/g1_floors/lean/)
  package. Landed via PR #20 (merged 2026-08-21): the `gV_le` port into
  `R3Cert` (`GArmExtAbstract.lean`, `GLemmaAbstract.lean`) **plus the full
  closure** — `CappedJointClosure.lean:gstep_le_one_achievable`, the config
  g-step `≤ 1` at **every arity**, unconditionally over achievable messages.

What remains open is the final honest-conditional assembly (`R7'`) and
independent review; the named-gap ledger lives in
[`proof/docs/design/R7_ARCHITECTURE.md`](proof/docs/design/R7_ARCHITECTURE.md)
and `proof/verification/conjecture1_status.py` (executable — the status calls
the certificates it cites).

A second, complementary track — the exact-arithmetic **certificate campaign** in
[`telperion/`](telperion/) — has since decomposed the `≤`-half into a strong
induction and proven its base and analytic steps:

- the **near-star spine** (the tie `Φ¹¹(N(0,5))=1`, the near-star tail
  `Φ¹¹(N(0,s))≤1 ∀s`, and the sub-unit asymptote) — **PROVEN**, arithmetic cores
  Lean CI-green;
- the **integrality gate** `tie ⟹ 11 | n` (23-adic) — **PROVEN** (necessary, not
  sufficient);
- **R1** single-hub extremality — the branching analytic steps (g-lemma
  unimodality over ℝ, two rational leaves) **PROVEN**; the inductive wiring's
  g-step crux **CLOSED** (PR #20, merged 2026-08-21: `gstep_le_one_achievable`,
  every arity, riding the kernel-proven abstract g-lemma `gV_le`); remaining:
  the leaf-child all-n case and composing the config-model closure into the
  rooted-tree master induction (see `telperion/PROOF_ASSEMBLY.md` §R1);
- **R2** the double-near-star family bound `Φ¹¹(DN(a,b))<1 ∀a,b≥2` — **PROVEN**;
  multi-hub *maximality* verified n≤13, **OPEN**.

The crux — general competitor extremality — remains open. For the enumerated,
tagged state of both tracks see **[`STATUS.md`](STATUS.md)** (the one-glance
index), with the piece-by-piece detail in
[`telperion/PROOF_STATUS.md`](telperion/PROOF_STATUS.md) and
[`telperion/PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md).

## Repository map

| Path | What it is |
|---|---|
| [`STATUS.md`](STATUS.md) | **One-glance index** — enumerated, tagged state of both the proof and the engine, each row linking to the document that owns the detail. Start here. |
| [`proof/`](proof/) | The peer-review package: Lean 4 formalization ([`proof/formalization/`](proof/formalization/)), exact-arithmetic Python verification harnesses ([`proof/verification/`](proof/verification/), entry point [`proof/verify.py`](proof/verify.py)), design/review documents, technical notes, figures. See [`proof/README.md`](proof/README.md). |
| [`telperion/`](telperion/) | **Telperion** — a **general-purpose, standalone tool** for proving families of mathematical statements (rational-function inequalities, polynomial nonnegativity, semialgebraic positivity via the Positivstellensatz family — Handelman, Putinar, Nullstellensatz/infeasibility, SOS refutation, real Nullstellensatz, equational consequence — integer Chvátal–Gomory rounding, exact identities, p-adic valuations, transcendental bounds, finite case analysis) in Lean 4, by exact-arithmetic certificate + kernel verification, with exact/SDP certificate *finders* (Handelman, Putinar, SOS-refutation, real-Nullstellensatz, rational-SOS, Bernstein) and a single-goal `telperion prove` backend exposing the pipeline to LLM/RL provers as a deterministic certificate-discharge step. Problem-agnostic: this proof was its first and largest case study, not its scope. Start at [`telperion/README.md`](telperion/README.md). BG proof-state maps: [`PROOF_STATUS.md`](telperion/PROOF_STATUS.md), [`PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md). |
| [`PUBLICATION_LEDGER.md`](PUBLICATION_LEDGER.md) | Conservative, provisional novelty tally — what could plausibly stand up in a venue, and what is explicitly still open. |
| [`CITATION.cff`](CITATION.cff) | How to cite. |

## Verifying the claims

Three independent one-command checks:

```bash
# 1. The Lean formalization (the trusted component; ~20 min with Mathlib cache)
cd proof/formalization && lake exe cache get && lake build

# 2. The Python verification harness (every claim an assert; ~20-40 min)
pip install -r proof/requirements.txt
python3 proof/verify.py

# 3. The unit tests (two independent permanent engines must agree, exactly)
cd proof && python3 -m pytest verification/tests -q
```

Both also run in CI on every push (`.github/workflows/`).

## Trust model

The Lean kernel is the sole trusted component. The Python layers (including the
certificate generator that emitted ~200 of the Lean theorems) are untrusted by
design: a defective certificate manifests as a Lean compile failure, never as a
false theorem. The generator's sympy self-checks exist to catch errors early,
not to establish truth. This design principle — and the discipline of validating
every identity numerically in exact rationals *before* formalizing it — is
generalized in [Telperion](telperion/).

## Provenance

This repository is a snapshot of an active campaign; development happens on the
origin repository and is re-imported here at green milestones. Origin commit,
CI pipeline evidence, and the re-import procedure:
[`proof/PROVENANCE.md`](proof/PROVENANCE.md).

## License

Code: [Apache-2.0](LICENSE). Documentation, notes, and figures:
[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).
