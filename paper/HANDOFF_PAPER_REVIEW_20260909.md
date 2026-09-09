# HANDOFF: paper review + 2026-09-09 emitter work to fold in

**To:** the session that owns `paper/` (whitepaper construction)
**From:** review session, 2026-09-09
**State reviewed:** paper sources as of `origin/main` @ `ea27ac22` (post PR #396;
PR #397 open). The paper's last content change is the epilogue (PR #368); the
`paper/` tree is unchanged since, so everything from PR #369 onward is not yet in
the text. The PDF build check was run at `abc78357` (post #394); no paper files
changed between the two heads.

`conjecture1_proved = False` throughout; nothing in this handoff changes that.

---

## 1. Review verdict

The paper is in strong shape. It builds clean (pdflatex + bibtex, 14 pages, zero
undefined references; every `\cite` key exists in `references.bib` and vice versa).
The numbers are internally consistent everywhere I checked: 89 bands = 1 (height-100)
+ 38 (height-50, to T=2000) + 50 (height-40 segment); 3474 = 1517 + 1957; abstract,
intro, conclusion, and the Turing subsection all agree on 3474 zeros to height 4000.
The honesty posture (trust boundaries stated per claim, "we do not claim RH" in
abstract/intro/sec 5/conclusion, Borel-Caratheodory fenced off as a draft) is uniform
and load-bearing. The Dyson reframe with RH results leading and Telperion as methods
reads as one coherent story.

Two staleness bugs, two freshness items, and a large content gap. Details below.

### 1a. Fixes required (small, do these first)

1. **`paper/sections/05-rh.tex:11`** -- the section preamble says "a complete finite
   Turing verification to height $1000$". Everywhere else (abstract, intro,
   conclusion, and the Turing subsection itself) says **4000**. Stale from two
   milestones ago.
2. **`paper/sections/05-rh.tex:148-154`** -- "the current milestone" appears twice:
   first for `AllZeros_h2000`, then two sentences later for `AllZeros_h4000`. The
   h2000 clause is a leftover; demote it to past tense ("a further stack extended...").
3. **`paper/sections/02-system.tex:59`** -- "more than eighty emitters" is still true
   but stale: the registry is at **119 classified emitters, 0 unclassified** as of
   PR #396 (was 114 after #394). Consider "well over a hundred".
4. **Housekeeping:** `paper/telperion-whitepaper/` is the superseded 8-section draft,
   with its own PDF, sitting inside `paper/`. A stray reader can mistake it for the
   current paper. One line in its README ("superseded by `../main.tex`") fixes that.

---

## 2. Content gap A: the RvM program (PRs #365-391, all merged 2026-09-09)

This is the big one. Since the epilogue landed, a second major storyline has been
built stone by stone in the kernel: **the Riemann-von Mangoldt counting formula**.
None of it appears in `05-rh.tex`. All of it is kernel-clean
({`propext`, `Classical.choice`, `Quot.sound`}, zero `sorryAx`, CI-guarded).

The arc, in paper order:

- **S(T) and theta, branch-free** (#365-367): argument-change infrastructure with no
  branch cuts; S(T) defined; theta identified as the critical-line argument change;
  the S-difference counting identity -- *S counts the zeros*.
- **The fold toolkit** (#369-372): logDeriv under Schwarz reflection; edge
  integrability of logDeriv zeta / Gamma_R on general vertical lines; the symmetric
  fold identity (left-edge argChange = minus the Archimedean part); integral form.
- **The pole "+1"** (#373, #378-385): extract zeta's simple pole from its
  log-derivative; the companion **H = (s-1)zeta is ENTIRE**; the three
  argument-principle prerequisites ported from zeta to H; a **generic Blaschke
  split** and the **generic box argument principle (count = winding)** instantiated
  at H; integrated pole extraction on the box boundary; the meromorphic argument
  principle for zeta *with the pole*; the strip-count capstone.
- **The band-difference capstone** (#374): `zero_count_band_edge_decomp` on the
  classical rectangle [-1,2] x [T0,T1]:
  `2pi * N_band = 2*AV(zeta,2) + AH(zeta,T1) - AH(zeta,T0) + AV(Gamma_R,-1) + AV(Gamma_R,2)`
  -- **the difference form of RvM, which is exactly the object the height-ladder
  tiling consumes as numeric input today.** This is the trust-shrink story: right now
  the per-band winding integers enter as documented numeric hypotheses; this
  machinery is the path to *deriving* the count identity, shrinking the numeric
  surface the same way `left_edge_prime_reflection` did for the left edge. That
  connection is the natural way to write the subsection.
- **xi-doubling** (#375-377): the entire-Lambda_0 reflection + fold, the theta/S
  split of the completed-zeta argument change -- and note that **#377 is a
  correction PR** ("Lambda_0 does NOT carry the nontrivial zeros -- honesty fix").
  Worth citing in the posture/evaluation material as lived practice, not just policy.
- **The completed-zeta path decomposition** (#387-391): the conjugation fold (one of
  RvM's two symmetry folds); **THE theta identification** (the Archimedean part of
  the right-half path IS theta); the piS half and **Delta_L Lambda = theta + piS**;
  the reflection-conjugation fold **Delta_box = 2 * Delta_L** -- proved on
  Lambda = completedRiemannZeta, whose strip zeros *are* zeta's (unlike Lambda_0).
  121 theorems on the guard as of #391.

**Honest ceiling, state it exactly:** the literal N(T) = theta(T)/pi + 1 + S(T)
still needs the box argument principle for Lambda with its poles at 0 and 1 (the
source of the +1) plus the T0 -> 0+ base. Genuine construction, NOT claimed, and
the PRs say so explicitly -- carry that scoping into the text verbatim in spirit.

**Suggested placement:** a new subsection in `05-rh.tex` between the Turing
verification and the explicit formula (it consumes the former's band counts and
shares the latter's contour machinery), presented as the trust-boundary payoff
rather than as a fifth standalone shape. Alternatively a short "since this draft"
paragraph if you want to hold the full treatment for the next revision.

---

## 3. Content gap B: today's emitter + research work (PRs #392-397)

- **#393 -- Li positivity ladder (RH-roadmap Track 2).** Certifies finite prefixes
  of **Li's criterion** onto the already-formalized upstream reduction
  (`nicholasbulka/li-criterion-rh-equivalence-lean`:
  `RiemannHypothesis <-> forall n, 0 <= (taylorCoeff riemannXi n).re`). Per rung:
  a certified positive rational lower bound, Arb enclosure carried as hypothesis
  (the trust seam). Natural companion to the Jensen-Polya subsection -- same
  criterion-prefix certificate shape, second independent criterion. **Caveat that
  must travel with it:** emitted-but-NOT-yet-CI-compiled (the Lean compile needs
  the upstream lib as a lake `require`; see `LI_POSITIVITY_LADDER.md`), so it
  cannot yet join the CI-axiom-guarded list -- if added to the paper, flag it the
  way the Borel-Caratheodory draft is flagged. Honest ceiling: the uniform
  `forall n` IS RH (the iff's right side); rungs are a finite prefix, NOT RH.
- **#394 -- four second-pass zeta-23-lean catalog emitters**
  (`enclosure_interval_fold`, `reflection_halving`, `spacing_tail_bound`,
  `autocorr_support`): honest concrete-instance / `decide` certs, the uniform
  analytic lemmas they instantiate cited not claimed; emitted Lean locally
  kernel-verified under Mathlib v4.32.0. Registry at 114 after this PR.
- **#395 -- two research docs, one directly paper-relevant.**
  `telperion/docs/DYSON_QUASICRYSTAL_CERTIFICATES.md` is an adversarially-verified
  triage of Dyson's quasicrystal framing into certificate shapes. Findings that
  constrain the paper's framing: the genuine iff (the N-valued FQ classification)
  provably does not cover zeta; the claim that {log p^k} pure-point support is
  unconditional was **refuted 0-3 (it is RH-conditional)**; a contested Shaughnessy
  "proof" is flagged as not established. The paper as written does NOT overclaim --
  it stays at the explicit-formula identity, which the triage supports -- but
  **cross-check sections 1, 5, and 9 against this doc before any revision, and do
  not add any "pure-point diffraction on the prime powers, unconditionally"
  phrasing.** The abstract's "supported on the logarithms of prime powers" sentence
  is inside Dyson's conditional reading ("If RH is true..."), which is fine; keep
  it conditional. Second doc: `AXIOM_MATH_BGP212_REVIEW.md` -- Axiom Math's
  H_1 <= 212 prime-gaps paper is certificate-shaped, and its Appendix A leaves the
  variational certificate as an out-of-kernel hypothesis, precisely Telperion's
  in-kernel specialty. Possible future related-work sentence; not urgent.
- **#396 -- four Axiom-bgp212 + Dyson emitters** (`rayleigh_gram` -- the bgp212
  Thm 11.1 Gram/generalized-eigenvalue shape their appendix leaves out-of-kernel;
  `polytope_moment`; `admissible_tuple` (decide-checked, {0,2,4} negative control);
  `lee_yang_stable_pair` -- Schur-Cohn/Jury chain, the Kurasov-Sarnak
  zeros-on-line analogue **by construction, not zeta's RH**). Registry now **119
  emitters, 0 unclassified**. One anecdote worth the methods section: local kernel
  verification caught a real pre-commit bug live (missing Q ascription caused
  integer elaboration, 63/64 = 0, a provable False) -- the untrusted-generator/
  trusted-kernel loop doing exactly its job.
- **#392** -- Python 3.9 compat fix for `zeta_zero_localization/generate.py`. No
  paper impact.
- **#397 (OPEN at handoff time) -- bgp212 published-surface kernel verification.**
  Uses the just-merged #396 emitters to kernel-verify, locally, the complete
  published exact-rational surface of the Axiom Math H_1 <= 212 paper:
  `H45Admissible.lean` (the paper's actual 45-tuple from Section 12 -- admissible
  + diameter 212, core-Lean `decide` over derived primes <= 43, standalone
  compile ~2 s, the 14 omitted-residue witnesses of Lemma 12.1 independently
  re-verified pre-emission) and `AppendixBLedger.lean` (the full 21-row Appendix B
  slack ledger, Table 6, exact fractions with slacks down to 163/(2*10^12),
  `norm_num` over Q under Mathlib v4.32.0, every slack re-verified in exact
  arithmetic pre-emission). Its README makes **the collaboration ask**: the
  paper's Appendix A leaves the Theorem 11.1 variational certificate (846-dim
  P-star coefficient vector, rational Gram matrices I_T/J_T, J - 4I > 0) as an
  out-of-kernel hypothesis, and that data is unpublished; `rayleigh_gram` +
  `polytope_moment` are wired to consume exactly it, so sharing the data turns
  the hypothesis into a kernel-verified theorem. Honest caveat carried in the PR:
  the 846-dim contraction needs a scaling pass beyond the current dim-25
  `norm_num` cap. Prime-gaps mathematics, not RH -- but it is the
  "check the witness, don't trust the author" thesis applied to *someone else's
  published proof*, which is a strong candidate for a paragraph in the evaluation
  or related-work section once merged. Track its merge before citing.

---

## 4. Verified during review (no action needed)

- Paper == `origin/main` (no drift in any checkout I touched).
- Full latex + bibtex cycle clean; no missing/unused bib keys (including the
  epilogue's `nasar1998` and `montgomery1973`).
- Cross-references resolve; section order in `main.tex` (01, 05, 02, 03, 04, 06,
  07, 08, 09, 10, A) renders correctly.
- Open PRs at handoff time: #397 (bgp212 published-surface verification, covered
  above) and #305 (stale frozen input-hashes, unrelated).

## 5. Suggested priority order

1. The two staleness fixes in `05-rh.tex` (five minutes, removes real
   contradictions).
2. The RvM subsection (the substantive gap; the PR bodies for #374 and #391 contain
   statement-level detail sufficient to draft at exact strength).
3. A Li-criterion paragraph appended to the Jensen-Polya subsection, with the
   not-yet-CI-compiled flag.
4. Emitter-count refresh in `02-system.tex` + the Dyson-triage cross-check of
   sections 1/5/9.
5. The superseded-draft README pointer.

**Footgun reminder** (bit us before, see repo history): the CI scan greps for the
bare word; in any `.lean` or docstring text write "no `sorry`" with backticks,
never the bare hyphenated adjective form.
