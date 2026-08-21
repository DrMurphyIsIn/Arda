# Arda

This repository is a working research program, kept honest in public form:
machine-checked progress on a 42-year-old open problem in extremal graph
theory, the general-purpose proof engine that campaign forged, and — most
recently — a second front in proof complexity built with the same discipline.
Nothing here is presented as more finished than it is. The status flags
(`conjecture1_proved = False`) are load-bearing, the dead ends are documented
with reasons, and every "proven" comes with the artifact that proves it.

## The problem

In 1984, Brualdi and Goldwasser asked a deceptively simple question: among all
trees `T` on `n` vertices, which one maximizes the Laplacian ratio

```
pi(T) = per(L(T)) / prod_v deg(v)
```

— the *permanent* of the Laplacian, normalized by the degree product?
Equivalently (because the permanent is multilinear in rows): which tree's
simple random walk maximizes `per(I - P)`?

Why is this hard? Because the determinantal shadow of the same quantity is
identically zero — `det(I - P) = 0` for every graph — so every tool that
works through determinants sees nothing at all. The entire content of the
problem lives in exactly the sign cancellations that the determinant
destroys. Permanents don't factor, don't telescope, and don't respect the
spectral theorem, and this conjecture sits right where those failures bite.

The conjectured maximizer is a *near-star* (a hub carrying cherries), with
equality — remarkably — exactly at six eleven-vertex trees where the
normalized invariant `Φ¹¹` hits `1` on the nose, via the integer identity
`64·243·23 = 621·576`. That an extremal problem over all trees ties at an
exact integer coincidence is the first hint of what the campaign eventually
established in detail: the obstruction is *arithmetic*, not analytic. There
is provably no smooth certificate — the continuous relaxation of the
near-star envelope exceeds `1` between integers — so the proof has to be
integer-tight, and that is what makes it interesting.

**The conjecture is NOT claimed proved.** What follows is what is actually
in hand.

## Where the proof stands

The campaign runs on two complementary tracks that meet in the middle.

**The Lean track** ([`proof/`](proof/)) is the peer-review package: a single
Lean 4 library (`R3Cert`, 109 modules) that builds clean against pinned
Mathlib with no `sorry`, no added axioms, and no `native_decide`. Reading it
bottom to top, the kernel has verified:

- `per(L(T)) = ` matching sum for acyclic graphs (the H1 bridge), and the
  exact cavity recursion connecting it to a Branch model (`Matching.lean`,
  `CavityTree.lean`, `BridgeStep2`–`4j`);
- **`Φ ≤ 1`** — the central branch inequality, unconditional
  (`PotentialFinal.lean:phi_le_one`), including the six-point rational tie
  variety where `Φ = 1` exactly. No smooth certificate can prove this; the
  proof is arithmetic, a discharging hinge super-solution;
- the **certified merge layer**: every Balanced∧Capped hub-backbone state
  rewrites monotonically in `per L/∏deg` to an ordered-merge normal form
  (`R47StepMono.lean:chain_to_normalForm`), via 36 + 36 + 72 generated
  positivity certificates;
- the (L)/(B) classification layer, the R5/R6 shedding lemmas (42 + 55
  certificates), and the raw-tree → Branch rate-port parse;
- the **capped-joint g-step layer** (2026-08-20/21, `GStepCore.lean`,
  `CappedJointConfig.lean`, `CappedJointAchievable.lean`,
  `GLemmaAssembly.lean`): a correction-and-reduction arc worth telling
  honestly. The originally-posed Case-2 hypothesis turned out to be *false
  as stated* on `μ ∈ (1/2, 1)`; the fix — non-leaf cavity messages satisfy
  `μ ≤ 1/2` — is exactly the relocated integrality content. With
  achievability in place the per-arity pieces went through kernel-clean
  (`single_child_le_one`, `two_child_le_one` — for two or more children no
  side condition is even needed; the integrality wall is a single-child
  phenomenon), and PR #20 (merged 2026-08-21) landed the abstract g-lemma
  `gV_le` (ported from the standalone
  [`telperion/examples/g1_floors/lean/`](telperion/examples/g1_floors/lean/)
  package) **plus the full closure** —
  `CappedJointClosure.lean:gstep_le_one_achievable`, the config g-step `≤ 1`
  at **every arity**, unconditionally over achievable messages.

What remains open on this track is the final honest-conditional assembly
(`R7'`) and independent review; the named-gap ledger lives in
[`proof/docs/design/R7_ARCHITECTURE.md`](proof/docs/design/R7_ARCHITECTURE.md)
and `proof/verification/conjecture1_status.py` — which is executable: the
status file calls the certificates it cites, so it cannot silently drift.

**The certificate track** ([`telperion/`](telperion/)) decomposed the
`≤`-half into a strong induction and proved its base and analytic steps:

- the **near-star spine** (the tie `Φ¹¹(N(0,5))=1`, the near-star tail
  `Φ¹¹(N(0,s))≤1 ∀s`, and the sub-unit asymptote) — **PROVEN**, arithmetic
  cores Lean CI-green;
- the **integrality gate** `tie ⟹ 11 | n` (23-adic) — **PROVEN** (necessary,
  not sufficient);
- **R1** single-hub extremality — the branching analytic steps (g-lemma
  unimodality over ℝ, two rational leaves) **PROVEN**; the inductive
  wiring's g-step crux **CLOSED** (the PR #20 closure above); remaining: the
  leaf-child all-n case and composing the config-model closure into the
  rooted-tree master induction (see
  [`telperion/PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md) §R1);
- **R2** the double-near-star family bound `Φ¹¹(DN(a,b))<1 ∀a,b≥2` —
  **PROVEN**; multi-hub *maximality* verified n≤13, **OPEN**.

And the crux? As of 2026-08-21 the campaign knows something sharper about
it: every remaining open thread — the R3 branching tail, the homogeneous
face, the g-step's tight content — has been shown to be **one and the same
object**, the master inequality: an integer-tight, non-monotone arithmetic
core, tight exactly at the arm
([`proof/docs/GSTEP_STEP1_IS_THE_CRUX.md`](proof/docs/GSTEP_STEP1_IS_THE_CRUX.md)).
One crux, many costumes. It remains open, and it is genuinely hard for a
reason the campaign can now state precisely: it needs an argument that is
simultaneously collective (not a sum of local terms), archimedean-aware (it
is a growth rate), and integrality-based (the exact-1 locus is carved by a
23-adic gate).

For the enumerated, tagged state of both tracks, start at
**[`STATUS.md`](STATUS.md)** — the one-glance index — with piece-by-piece
detail in [`telperion/PROOF_STATUS.md`](telperion/PROOF_STATUS.md) and
[`telperion/PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md).

## The engine: Telperion

The campaign needed hundreds of kernel-checked inequalities, and writing
them by hand does not scale. [Telperion](telperion/) is the answer, and it
outgrew its origin: a **general-purpose, standalone tool** for proving
families of mathematical statements in Lean 4 by exact-arithmetic
certificate plus kernel verification. You describe your problem as a
parameterized family; Telperion certifies each instance in exact rational
arithmetic, then emits Lean that Mathlib's kernel re-proves from scratch.

The design principle throughout: **the generator is untrusted**. A wrong
certificate is a compile error, never a false theorem — so you get
machine-checked proofs without having to trust (or even read) the tool that
wrote them. The certificate shapes now span rational-function inequalities,
polynomial and semialgebraic positivity (the full Positivstellensatz family:
Handelman, Putinar, Nullstellensatz and its infeasibility/refutation forms,
real Nullstellensatz, equational consequence), integer Chvátal–Gomory
rounding, Sturm strict-interval positivity, Bernstein interval certificates,
rational SOS with Artin denominators, exact identities, p-adic valuations,
transcendental brackets, and finite case analysis — with exact/SDP
certificate *finders* for the shapes where you'd rather not construct the
certificate yourself, and a single-goal `telperion prove` backend that
exposes the whole pipeline to LLM/RL provers as a deterministic
certificate-discharge step. This proof was its first and largest case study,
not its scope: start at [`telperion/README.md`](telperion/README.md).

## The third arc: proof complexity

The same discipline — exact validation first, kernel-checked Lean second,
honesty gates throughout — is now climbing a different ladder:
**kernel-checked lower bounds in proof complexity**, starting with a
symbolic-*n* formalization of Grigoriev's knapsack SOS degree lower bound
(51 theorems, axioms clean) and a certified 3XOR structure theorem with
Tseitin-on-Petersen as the fully-certified canonical instance. The front
door, with the pipeline write-up and the honest novelty positioning, is
[`proof-complexity/README.md`](proof-complexity/README.md).

## Repository map

| Path | What it is |
|---|---|
| [`STATUS.md`](STATUS.md) | **One-glance index** — enumerated, tagged state of the proof, the engine, and the proof-complexity arc, each row linking to the document that owns the detail. Start here. |
| [`proof/`](proof/) | The BG peer-review package: Lean 4 formalization ([`proof/formalization/`](proof/formalization/)), exact-arithmetic Python verification harnesses ([`proof/verification/`](proof/verification/), entry point [`proof/verify.py`](proof/verify.py)), design/review documents, technical notes, figures. See [`proof/README.md`](proof/README.md). |
| [`telperion/`](telperion/) | **Telperion** — the general-purpose sympy → Lean certificate engine described above. Start at [`telperion/README.md`](telperion/README.md). BG proof-state maps: [`PROOF_STATUS.md`](telperion/PROOF_STATUS.md), [`PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md). |
| [`proof-complexity/`](proof-complexity/) | **The P-vs-NP certificate ladder** — index of the kernel-checked proof-complexity arc: the Grigoriev knapsack pipeline paper, the 3XOR structure theorem, the Petersen certificate, and the emitter shapes the arc fed back into the engine. |
| [`PUBLICATION_LEDGER.md`](PUBLICATION_LEDGER.md) | Conservative, provisional novelty tally — what could plausibly stand up in a venue, and what is explicitly still open. |
| [`CITATION.cff`](CITATION.cff) | How to cite. |

## Verifying the claims

Don't take this README's word for any of it — the repository is built to be
checked. Three independent one-command verifications:

```bash
# 1. The Lean formalization (the trusted component; ~20 min with Mathlib cache)
cd proof/formalization && lake exe cache get && lake build

# 2. The Python verification harness (every claim an assert; ~20-40 min)
pip install -r proof/requirements.txt
python3 proof/verify.py

# 3. The unit tests (two independent permanent engines must agree, exactly)
cd proof && python3 -m pytest verification/tests -q
```

All of it also runs in CI on every push (`.github/workflows/`).

## Trust model

The Lean kernel is the sole trusted component. The Python layers — including
the certificate generator that emitted a couple hundred of the Lean theorems
— are untrusted *by design*: a defective certificate manifests as a Lean
compile failure, never as a false theorem. The generator's sympy self-checks
exist to catch errors early, not to establish truth. The one thing a kernel
cannot catch is vacuity (a true-but-empty theorem compiles green), which is
why the emitters carry nonvacuity and load-bearing gates on top. This design
principle — and the discipline of validating every identity numerically in
exact rationals *before* formalizing it — is generalized in
[Telperion](telperion/).

## Provenance

This repository began as a snapshot of an active campaign and has since
become a live development surface in its own right; new work lands here via
CI-gated PRs. Origin commit, pipeline evidence, the re-import procedure, and
the record of post-snapshot native development:
[`proof/PROVENANCE.md`](proof/PROVENANCE.md).

## License

Code: [Apache-2.0](LICENSE). Documentation, notes, and figures:
[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).
