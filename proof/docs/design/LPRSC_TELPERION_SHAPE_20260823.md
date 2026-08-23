# LPRSC: a new Telperion shape for the Brualdi–Goldwasser irreducible nucleus (2026-08-23)

`conjecture1_proved = False`. This designs and prototypes **LPRSC** — the *Lattice Power-Ratio
Single-Crossing* certificate — the first Telperion shape aimed squarely at the one irreducible core of
the BG problem: the **23-adic marginal tie** (R3 / `Φ≤1`). Every prior route (ours + the literature's)
dies there; the literature synthesis (`LITERATURE_SYNTHESIS_20260823.md`) proved it is the shared wall of
*both* certificate and transformation proof families. LPRSC is built to be the certificate class that
works *at* that wall.

## Why every existing shape fails, precisely

All existing Telperion emitters (Bernstein, Handelman, SOS, potential) certify **continuous**
(semialgebraic) positivity. The nucleus defeats them for one structural reason, now verified exactly
(`verification/lprsc_emitter.py`, PROBE 1):

> The near-star value `R(s) = RHS/LHS` (`RHS=23^{2s+1}(s+1)^{11}`, `LHS=3^{5s-14}2^{s+6}(4s+3)^{11}`) has
> **lattice** minimum at `s=5` with `R(5)=1` **exactly** (the integer identity `64·243·23 = 621·576`),
> yet its **continuous** relaxation dips to `R̃(4.82) = 0.99954 < 1`.

So `Φ̃ > 1` on the continuous relaxation — any smooth/SOS/Handelman certificate that would bound the
continuous problem is bounding a **false** statement, hence cannot exist. The crossing sits *between*
integers 4 and 5; the nearest lattice point `s=5` lands exactly on the threshold. This is a pure
integrality fact. **LPRSC is the first Telperion shape that certifies a lattice inequality which is false
on the continuous relaxation.**

## The shape

A one-parameter family value `R : ℕ → ℚ_{>0}` whose consecutive ratio has the closed form
```
    r(n) = R(n+1)/R(n) = C · (P(n)/Q(n))^p,   C ∈ ℚ,  p ∈ ℕ,  P,Q ∈ ℤ[n]
```
is certified `R(n) ≥ 1 ∀n`, equality iff `n = n*`, from five checkable hypotheses:

| # | hypothesis | discharged by |
|---|---|---|
| H1 | `0 < P(n) < Q(n)` (base in (0,1)) | poly positivity (`P>0`, `Q−P>0`) |
| H2 | `P/Q` strictly increasing: `P(n+1)Q(n) − P(n)Q(n+1) > 0` | **Handelman** poly-positivity on `n≥0` (reuses existing Telperion) |
| H3 | `C > 1` | rational compare |
| H4 | single crossing `r(n*−1) < 1 ≤ r(n*)` | two rational evals |
| H5 | `R(n*) = 1` | exact rational identity (`norm_num`) |

**Assembly lemma** (`R3Cert/LPRSC.lean`, proven, no `sorry`): H1–H5 ⟹ `r` strictly increasing (base
increasing in (0,1), `C>1`) ⟹ `R` strictly decreasing on `[0,n*]`, nondecreasing after ⟹ minimum at
`n*`, value 1 ⟹ `R ≥ 1`, equality iff `n=n*` (`family_ge_one`, `family_gt_one_off_tie`). The Lean core
is fully abstract over the sequence; the per-family H1–H5 are the emitter's job.

## Unification (PROBE 3, exact-verified)

The two **independently-proven** BG near-tie closures are the *same* LPRSC shape:

| family | `C` | `p` | `P(n)/Q(n)` | `n*` |
|---|---|---|---|---|
| near-star `R_ns(s)` (`near_star_arithmetic_proof`) | 529/486 | 11 | `(4s²+11s+6)/(4s²+11s+7)` | 5 |
| per-child base `B(kp)` (`near_star_broom_proof`) | 529/486 | 11 | `((kp+1)(4kp+7)−1)/((kp+1)(4kp+7))` | 5 |

Both share `C = 529/486 = 23²/(2·3⁵)` (the 23-adic tie signature) and `p = 11 = 2·5+1`. They differ only
in `g(n)` (the denominator polynomial). LPRSC is their common primitive; the two bespoke proofs become one
instantiated lemma.

## Reach — honest

- **What LPRSC closes:** any 1-parameter near-tie family of the `C·(P/Q)^p` form. It *composes*
  (per-parameter + telescoping) exactly as `near_star_broom` composes over `(s,j,kp)`; PROBE 5 confirms
  deep near-star chains telescope per level (constant per-level margin, `k=5` optimal at every depth), so
  LPRSC + telescoping reaches the depth/fractal tail.
- **What it does NOT close:** the *reduction* of an arbitrary tree to these structured families — the
  depth-collapse / non-monotone-optimal-child problem. That glue is separate and remains the frontier
  (`caterpillar_collapse_probe`, `depth_collapse_probe`). LPRSC supplies the irreducible-core primitive;
  it is not the whole proof.

So LPRSC is the correct *atom* for the marginal tie — the piece no continuous certificate and no
transformation can supply — and it unifies every near-tie closure achieved so far into one reusable,
Lean-checked Telperion primitive. The remaining distance to `conjecture1` is the tree→family reduction,
now cleanly separated from the (LPRSC-solved) tie arithmetic.

## Files

- `verification/lprsc_emitter.py` — the emitter + exact validation (both families pass H1–H5 + conclusion).
- `formalization/R3Cert/LPRSC.lean` — the assembly lemma (`ge_min`, `family_ge_one`, `family_gt_one_off_tie`),
  wired into `R3Cert.lean` (CI-gated).

`conjecture1_proved = False`.
