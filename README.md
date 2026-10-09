# Arda

[![proof-lean](https://github.com/DrMurphyIsIn/Arda/actions/workflows/proof-lean.yml/badge.svg)](https://github.com/DrMurphyIsIn/Arda/actions/workflows/proof-lean.yml)
[![proof-verify](https://github.com/DrMurphyIsIn/Arda/actions/workflows/proof-verify.yml/badge.svg)](https://github.com/DrMurphyIsIn/Arda/actions/workflows/proof-verify.yml)
[![telperion-lean-e2e](https://github.com/DrMurphyIsIn/Arda/actions/workflows/telperion-lean-e2e.yml/badge.svg)](https://github.com/DrMurphyIsIn/Arda/actions/workflows/telperion-lean-e2e.yml)

> **TL;DR** — The Brualdi–Goldwasser problem (1984: which tree on `n` vertices
> maximizes the Laplacian ratio `per(L(T))/∏deg`?) is **solved, and the answer is
> kernel-checked in Lean 4 / Mathlib**: for every `n ≥ 4` the maximizer is an
> explicit spider of cherry arms. The self-contained release lives in
> [**DrMurphyIsIn/brualdi-goldwasser**](https://github.com/DrMurphyIsIn/brualdi-goldwasser)
> ([doi:10.5281/zenodo.22983412](https://doi.org/10.5281/zenodo.22983412)); it has
> not yet been refereed by humans. This repository is where that proof was built:
> the research campaign that got there (dead ends included), the reusable
> certificate engine — [**Telperion**](telperion/) — that produced and packaged
> its certificates, and a second front in proof complexity. Everything is
> checked by the Lean kernel with **no `sorry`, no added axioms**. New here? Start at
> **[STATUS.md](STATUS.md)** for the proven-vs-open map, then see
> [Verifying the claims](#verifying-the-claims) to re-run the kernel checks yourself.
> Want to use the engine on your own problem? See
> [`telperion/docs/GETTING_STARTED.md`](telperion/docs/GETTING_STARTED.md).

This repository is a working research program, kept honest in public form:
the campaign on a 42-year-old problem in extremal graph theory, which ended
with a complete, kernel-checked answer; the general-purpose proof engine that
campaign forged; and a second front in proof complexity built with the same
discipline. Nothing here is presented as more finished than it is. The dead
ends are documented with reasons, and every "proven" comes with the artifact
that proves it.

A word about the flag you will see everywhere: `conjecture1_proved = False`.
It does **not** say the Brualdi–Goldwasser problem is open. It tracks the
campaign's *own* first route to the answer, the conditional capstone
`R3Cert.Step3.conjecture1_of_layers` and the pinned `BGBackboneConjecture`
(the claim that every tree is beaten by a same-size multi-hub
cherry-backbone). Those still rest on named open hypotheses (Hnorm/Hdom, and
the straightening obligation `StraightProgress_sized`), and nothing has wired
the final answer back into them, so the flag stays `False` and the tests that
assert it stay green. The problem itself was settled by a different route,
described below.

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
spectral theorem, and this problem sits right where those failures bite.

For a long time the working guess inside this campaign was a *near-star*
(a hub carrying cherries). The first real clue was arithmetic: the
normalized invariant `Φ¹¹` hits `1` on the nose at an eleven-vertex block,
via the integer identity `64·243·23 = 621·576`. That an extremal problem over
all trees ties at an exact integer coincidence told us early that the
obstruction is *arithmetic*, not analytic. There is provably no smooth
certificate (the continuous relaxation of the near-star envelope exceeds `1`
between integers), so the proof had to be integer-tight. Meanwhile the
literature moved too: Wu, Dong and Lai proposed an answer, and Pant (2026,
arXiv:2605.14176) refuted it with caterpillars of hubs.

## The answer: solved, and kernel-checked

The eleven-vertex block turned out to be the whole story. For every `n ≥ 4`
the maximizer is a **spider of cherry arms**: one centre, and hanging from it
only *arms*, each arm a vertex carrying some number of cherries (pendant paths
of length two). Almost every arm carries **five** cherries. An arm with five
cherries is exactly that eleven-vertex block, contributing `621/64 = ρ¹¹` to
the ratio, and `ρ = (621/64)^(1/11) ≈ 1.2295` is the exact exponential growth
rate of the maximum. For `n ≥ 492` the shape follows a short rule in
`6(n − 1) mod 11`; for `4 ≤ n ≤ 491` it comes from an explicit,
kernel-checked table (at `n = 21` two different trees tie).

Here is what is established, and how strongly:

- **The maximum value and a maximizer, for every `n ≥ 4`**, are kernel-checked
  in Lean 4 / Mathlib using only Lean's three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`). The
  headline theorem is `R3Cert.BGMaximizerAll.bg_maximizer_all`. It was built
  here, in [`proof/formalization/R3Cert/BGMaximizerAll.lean`](proof/formalization/R3Cert/BGMaximizerAll.lean),
  and its axioms are guarded by name in
  [`proof/formalization/AxiomGuard.lean`](proof/formalization/AxiomGuard.lean).
- **A second kernel.** In the standalone release, the same statement, written
  purely in Mathlib's vocabulary, was re-checked by the Lean FRO's
  [Comparator](https://github.com/leanprover/comparator): both Lean's kernel
  and [nanoda](https://github.com/ammkrn/nanoda_lib), an independent kernel
  written in Rust, accepted the proof.
- **Uniqueness up to graph isomorphism**, for every `n ≥ 4` except `n = 21`,
  where there are exactly two maximizers (`T(3,3,3)` and the subdivided star
  `S(21,10)`), is formalized in `formalization/BGUnique` of the release. It is
  checked by Lean's kernel. Comparator confirmed only that its statement
  matches; the second-kernel replay for uniqueness has **not** been completed,
  so no two-kernel claim is made for it.
- **The λ-family.** Weighting each matched edge by `λ` gives a family of
  ratios with `λ = 1` as the original. Its uniform theorem, parts (A) and (B)
  with their equality clauses, is kernel-checked in `formalization/cherry` of
  the release.

The public, self-contained home of all of this is
**[DrMurphyIsIn/brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser)**,
archived on Zenodo under the concept DOI
[10.5281/zenodo.22983412](https://doi.org/10.5281/zenodo.22983412) (which
always resolves to the latest release; v1.4.1 is
[10.5281/zenodo.23210967](https://doi.org/10.5281/zenodo.23210967)). It carries
the Mathlib-vocabulary statement, the certificates and their byte-for-byte
regeneration, the Comparator record, and build instructions. Start there if
you want to check the answer.

What a kernel cannot do is tell you that the statement says what we think it
says. The result **has not yet been refereed by humans**: the statement, the
definitions, and the correspondence between the formal ratio and
`per(L(T))/∏deg` all deserve independent scrutiny, and review is very
welcome. The release repository includes a public preprint
([`paper/paper.pdf`](https://github.com/DrMurphyIsIn/brualdi-goldwasser/blob/main/paper/paper.pdf)),
archived with its Zenodo releases, and a paper is in preparation.

## How the campaign got there

What follows is the story of the campaign's first route, the one the
`conjecture1_proved` flag still tracks. It is worth reading because most of
the final proof's machinery was forged here, and because it shows honestly
where that route stalled. The route that finally closed the problem (a
reduction to spiders, envelope certificates for small `n`, and an exact
optimization over spiders) is summarized in
[STATUS.md](STATUS.md) and laid out in full in the
[brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser)
release.

The first route ran on two complementary tracks that meet in the middle.

**The Lean track** ([`proof/`](proof/)) is the peer-review package: a single
Lean 4 library (`R3Cert`, whose modules live under
[`proof/formalization/R3Cert/`](proof/formalization/R3Cert/)) that builds
clean against pinned Mathlib with no `sorry`, no added axioms, and no
`native_decide`. Reading it
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

What remained open on this route is the final honest-conditional assembly
(`R7'`), and it still is: `conjecture1_of_layers` is conditional on the two
named layers Hnorm/Hdom, which were never discharged (an early form of Hnorm
was even refuted in the kernel). The problem was answered around it, not
through it; the named-gap ledger lives in
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

And the crux? As of 2026-08-21 the campaign knew something sharper about
it: every remaining open thread — the R3 branching tail, the homogeneous
face, the g-step's tight content — has been shown to be **one and the same
object**, the master inequality: an integer-tight, non-monotone arithmetic
core, tight exactly at the arm
([`proof/docs/GSTEP_STEP1_IS_THE_CRUX.md`](proof/docs/GSTEP_STEP1_IS_THE_CRUX.md)).
One crux, many costumes. At the time it was genuinely hard for a reason the
campaign could state precisely: it needed an argument that is simultaneously
collective (not a sum of local terms), archimedean-aware (it is a growth
rate), and integrality-based (the exact-1 locus is carved by a 23-adic gate).
The campaign later got past it in two steps: the sharp rate ceiling
`Φ¹¹ ≤ 1` was proved through an additive subaction (`bg_ceiling`, with its
equality case `bg_sharp`), part of the route that led to the final proof; and
the maximizer itself was pinned down by reducing to spiders and optimizing
over them exactly.

For the enumerated, tagged state of both tracks (and of the final answer), start at
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

Telperion also keeps a **missions registry** of formal statements about the
Riemann zeta function (`telperion/missions/`), with a browsable
[Registry Explorer](docs/explorer/index.html) built from it. Its
headline as of 2026-10-09: the first machine-checked bound on the de Bruijn–Newman
constant below de Bruijn's 1/2, `Λ ≤ 9/32`, obtained by composing OpenAI's kernel-checked
quasi-Riemann hypothesis (`ζ(s) ≠ 0` for `Re s > 7/8`, [openai/math](https://github.com/openai/math),
Apache-2.0) with de Bruijn's heat-flow theorem in one Lean environment, then judged by an
independent Comparator run with two kernels. It is weaker than the numerical 0.22 and it
is not a proof of the Riemann Hypothesis; `conjecture1_proved = False` throughout. The paper and
the Lean sources are released at [DrMurphyIsIn/qrh-debruijn-newman](https://github.com/DrMurphyIsIn/qrh-debruijn-newman)
(Zenodo DOI [10.5281/zenodo.23269134](https://doi.org/10.5281/zenodo.23269134)).

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
| [`proof/`](proof/) | The BG campaign's working package, where the kernel-checked answer (`R3Cert/BGMaximizerAll.lean`) was built: Lean 4 formalization ([`proof/formalization/`](proof/formalization/)), exact-arithmetic Python verification harnesses ([`proof/verification/`](proof/verification/), entry point [`proof/verify.py`](proof/verify.py)), design/review documents, technical notes, figures. See [`proof/README.md`](proof/README.md). |
| [`telperion/`](telperion/) | **Telperion** — the general-purpose sympy → Lean certificate engine described above. Start at [`telperion/README.md`](telperion/README.md). BG proof-state maps: [`PROOF_STATUS.md`](telperion/PROOF_STATUS.md), [`PROOF_ASSEMBLY.md`](telperion/PROOF_ASSEMBLY.md). |
| [`proof-complexity/`](proof-complexity/) | **The P-vs-NP certificate ladder** — index of the kernel-checked proof-complexity arc: the Grigoriev knapsack pipeline paper, the 3XOR structure theorem, the Petersen certificate, and the emitter shapes the arc fed back into the engine. |
| [`PUBLICATION_LEDGER.md`](PUBLICATION_LEDGER.md) | Conservative, provisional novelty tally — what could plausibly stand up in a venue, and what is explicitly still open. |
| [brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser) (separate repository) | The standalone, public release of the answer: Mathlib-vocabulary statement, certificates, Comparator record, uniqueness, and the λ-family. Concept DOI [10.5281/zenodo.22983412](https://doi.org/10.5281/zenodo.22983412). |
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

To check the Brualdi–Goldwasser answer itself, the shortest path is the
standalone release,
[brualdi-goldwasser](https://github.com/DrMurphyIsIn/brualdi-goldwasser): its
README walks through building the proof, printing the axioms of every headline
theorem, regenerating every certificate byte for byte, and running the
Comparator second-kernel check. Fair warning: the heaviest certificate file
alone needs about 63 GB of memory.

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

Split model — see [LICENSING.md](LICENSING.md) for details:

- **All mathematics** (proof campaign, Lean formalizations, examples,
  emitted certificates, docs): [Apache-2.0](LICENSE) /
  [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/) — 
  unconditionally open, mathlib-compatible.
- **The Telperion engine** (`telperion/src/` and tooling):
  [Business Source License 1.1](telperion/LICENSE) — free for research,
  teaching, and evaluation; commercial production use requires a license;
  every version converts to Apache-2.0 three years after release.
  Certificates you emit with it are yours.
- Contributions to the engine require the [CLA](telperion/CLA.md);
  contributions to the mathematics do not.
