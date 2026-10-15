# Telperion tools for the WALL-3 tracks (track T)

2026-10-15. conjecture1_proved = False. Nothing here is progress on RH. These tools certify *finite* facts. Every
invocation below was run by track T before this note was written, with the outputs shown.

This note extends the WALL-2 one (~/rh-team/wall2/T/TOOLS.md), which is still valid. Read that one for the Li
coefficients, the Bagchi grid and the Lean-text emitters.

## Trust classes

When you quote a number in your report, name the class it rests on.

- **COMPUTED.** Floats from numpy or mpmath, with a script path. This is your default.
- **EXACT.** Exact rational arithmetic in Python `Fraction`s. It is rigorous if the script is right, but it is not
  a kernel theorem.
- **ARB.** A python-flint ball certificate, stored as a `.cert.json` sidecar. It is rigorous if Arb and the code
  are right, but it is not a kernel theorem. Write "Arb-certified", never "proved". arb_fakes, with the pole guard, is MERGED: cite
  it as "arb_fakes, Arda main 2dfc6eeee" (PR #741; the arb_fakes.py there is byte-identical to 72470dd5f). bb
  audited its winding and judged it SOUND, apart from the pole guard, which has since been added.
- **KERNEL.** Lean `decide` / `norm_num` on a finite fact, checked by T alone via `leanlock.sh`. Use it only for
  small finite bookkeeping.

## Binding rule from the auditor (bb, via the lead)

**Only certify with arb_fakes at 72470dd5f (guarded) or later.**
- Use `rigorous_winding` or `certify_zero_box`.
- Wherever a box contains s = 1, acknowledge the pole with `poles=`.
- **Never** use `arb_dh.winding_number_sampled_heuristic`, formerly `arb_dh.winding_number`, for a certificate. It
  samples at nodes only and can undercount.

T's WALL-3 helpers (t3tools, scripts, certs) are on the UNPUSHED local branch `wall3/telperion-certs`, which is cut
from 72470dd5f, an ancestor of Arda main 2dfc6eeee. Cite them as "t3tools, unpushed branch wall3/telperion-certs".

## Setup

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
T=~/rh-team/wall2/T/venv/bin/telperion
PY=~/rh-team/wall2/T/venv/bin/python
```

Do not `pip install` into that venv. The WALL-3 helpers live in `~/rh-team/wall3/T/t3tools.py`. Import them like this:

```python
import sys, os; sys.path.insert(0, os.path.expanduser("~/rh-team/wall3/T"))   # or this checkout's examples/wall3
from t3tools import powersum_certify, BeurlingZeta, integers_from_primes
```

## 1. Arb values of ζ, EP5, EPQ2, DH

```python
from telperion.arb_fakes import fake_eval
fake_eval("EP5", "0.93", "15.67", prec=128)   # -> (re_lo, re_hi, im_lo, im_hi), exact Fractions
# names: "zeta", "EP5", "EPQ2", "DH"; decimal strings are read as exact rationals
from flint import acb, ctx; ctx.prec = 128
acb("0.8", "61.14").zeta()                     # plain zeta, as a ball
```

The normalisations are the same as track H's harness:
- EP5 = Σ' (m² + 5n²)^(-s), with a(1) = 2.
- EPQ2 = Σ' (2m² + 2mn + 3n²)^(-s), with a(2) = 2.
- DH is the Davenport–Heilbronn function with c = [1, κ, −κ, −1, 0] mod 5.

## 2. Zero boxes and off-line counts, with the pole rule

```python
from telperion.arb_fakes import rigorous_winding, certify_zero_box, count_offline
rigorous_winding("EP5", "0.9", "0.96", "15.6", "15.7")         # -> 1     (winding = zeros - poles)
certify_zero_box("EP5", "0.9", "0.96", "15.6", "15.7")         # sidecar dict, zeros_in_box = 1, off_line True
count_offline("DH", "0.6", "1.6", "1/20", "100", cuts=[50])    # -> total 2  (zeros in [0.6,1.6] x [1/20,100])
```

**The pole rule.** ζ, EP5 and EPQ2 have a declared simple pole at s = 1; DH has none.
- **A box whose CLOSED rectangle contains a declared pole is REFUSED**, unless you acknowledge the pole:
  ```python
  certify_zero_box("zeta", "0.9", "1.1", "-0.1", "0.1")
  #   ValueError: declared pole 1+0i lies in the closed box ... refused (pass poles=[(1, 0)] ...)
  certify_zero_box("zeta", "0.9", "1.1", "-0.1", "0.1", expected=0, poles=[(1, 0)])
  #   accepted: winding -1, zeros_in_box 0
  ```
- An acknowledged pole must lie strictly inside the box. On the boundary, the box is refused.
- `count_offline` never acknowledges poles. Keep its boxes at Im ≥ 1/20.
- **Callables** (your own function, see §4) carry NO declared pole. You are responsible for keeping them off, or
  for passing `poles=`. Otherwise the winding silently counts zeros minus poles.

**What a certificate says.**
- f is enclosed on every boundary segment by the centred form |f − f(m)| ≤ r·sup|f′|.
- A segment is accepted only if its image stays in |w − c| ≤ |c|/2.
- The winding is accepted only if it lies within 1/4 of a unique integer.
- `certify_zero_box` re-runs the winding at 1.5× precision with a different subdivision, and both runs must agree.
- If any of this fails, the routine REFUSES (it raises). It never returns a guess.

**Speed.** A small box takes about 1 s; a T = 1000 strip count takes minutes. Precision 96 is the default; use 144
near the knife edge.

## 3. Finite inequalities: `telperion hunt` / `probe` / `psd` / `sonc` / `prove`

```sh
$T hunt --symbols x --iters 200 "x**2-x+1/8"     # DISPROOF (exact witness): -1/8 at x = 1/2
$T psd '[[2,1],[1,2]]'                           # positive definite: A = L D Lᵀ with D = diag([2, 3/2])
$T probe --symbols x,y "<poly>"                  # Polya certificate on the orthant: yes/no
$T sonc --symbols x,y "1 + x**4*y**2 + x**2*y**4 - 3*x**2*y**2"   # exact AM-GM circuit certificate
$T prove --symbols x --name myname "x**2-2*x+1"  # Lean text for 0 <= p (SOS, exact rational rounding)
```

- `hunt` is a disproof engine. A hit is an exact rational counterexample; a miss proves nothing.
- `psd` covers Gram and Hankel positivity of a *rational* matrix, e.g. a resonator quadratic form whose entries
  you can write exactly. For a transcendental matrix, send it to T for an Arb Cholesky check.

## 4. Finite power sums (Turán-type lower bounds)

`powersum_certify(b, z, nus, lower=None, mode="min"|"max", prec=256, exact=False)` works with
S_ν = Σ_j b_j z_j^ν.
- `mode="min"` certifies min_ν |S_ν| ≥ lower: every ν in `nus` clears the bound.
- `mode="max"` certifies max_ν |S_ν| ≥ lower, Turán's form. The witness ν is recorded.
- |S_ν|² is compared with lower² in exact Fractions.
- With `lower=None`, it returns the best certified bound instead of a verdict.
- When a certificate fails, `refuted: True` means the claim is FALSE: an Arb upper bound lies below `lower`.

```python
from flint import acb, arb
Z = [(-acb(0, 1) * arb("14.13") * arb(p).log()).exp() for p in (2, 3, 5, 7)]     # z_p = p^{-i t}, ARB
powersum_certify([1, 1, 1, 1], Z, range(1, 51), lower="0.05", mode="max")
#   certified True, witness_nu 33, certified lower 3.8418...
powersum_certify([1, 1, 1, 1], Z, range(1, 51), mode="min")       # best bound: min |S_nu| >= 0.30322...
from fractions import Fraction as F                                # EXACT, Gaussian rationals
powersum_certify([(1, 0), (1, 0)], [(F(3, 5), F(4, 5)), (F(1), F(0))], range(1, 11),
                 lower=F(1, 10), mode="min", exact=True)          # certified, min |S| = 0.15168 at nu = 10
```

- **Rule.** Build nodes such as p^{-it} or e^{iθ} as Arb balls, as above, never from floats. A float node only
  certifies the float's sum, which is not your sum.
- **Scope.** This certifies the *finite* sum you give it. Turán's theorem, i.e. the bound for all node
  configurations, is a citation and is not certified here.
- **Sizes.** About 1e4 terms × 1e3 exponents is fine. Beyond that, ask T.

## 5. Your own analytic function, and Beurling ζ_P (track B)

Any `f(acb_series) -> acb_series` can be passed in place of the name. `rigorous_winding(f, ...)` and
`certify_zero_box(f, ...)` then work as in §2, with no declared poles (see the pole rule).

For a Beurling system, `BeurlingZeta(ints, A, C, theta, X)` gives an Arb enclosure of ζ_P on Re s > θ. Its inputs:
- the generalized integers n ≤ X, as Arb logs;
- a remainder hypothesis H: |N(x) − A x| ≤ C x^θ for all x ≥ X.

It uses

  ζ_P(s) = Σ_{n≤X} n^{-s} − N(X) X^{-s} + A s X^{1−s}/(s−1) + E(s),   |E| ≤ |s| C X^{θ−σ}/(σ−θ),

together with a matching bound on |E′|, so the winding segment test is rigorous.

```python
from flint import arb, fmpz
ps = [p for p in range(2, 20001) if fmpz(p).is_prime()]
ints = integers_from_primes([arb(p).log() for p in ps], 20000.5)   # all generalized integers <= X, Arb logs
Z = BeurlingZeta(ints, 1, 1, 0, "20000.5")                         # zeta itself: |floor x - x| <= 1
# Z at 0.8+10i = [1.45 +/- 8.3e-3] - [0.11 +/- 7.9e-3]i, which contains acb.zeta's 1.44628 - 0.11350i
rigorous_winding(Z, "0.8", "1.2", "10", "12")                      # -> 0  (15 s)
```

- **The certificate is CONDITIONAL on H.** H must hold for ALL x ≥ X. If you have only observed it up to some
  x_max, the result is COMPUTED-conditional, and the report must say so.
- **The ball radius scales like |s| X^{θ−σ}/(σ−θ).** That is small only for σ − θ not tiny and X large, so a
  zero box near σ = (1+θ)/2 needs X^{(1−θ)/2} ≫ |s|.
- **Pole.** s = 1, with residue A. Keep boxes off it, or pass `poles=[(1, 0)]`.
- **Send T your object.** T will run the box: the prime list (or its rule), A, C, θ, X, and the box you expect.

## How to ask track T

Write a file `~/rh-team/wall3/<track>/T_REQUEST.md`, or send a message to the lead naming T. Include:
- the exact statement;
- the object;
- the box, or the ν-range;
- the script that produced your float value;
- the float value itself.

T polls R/, P/, E/ and B/ every ~10 minutes. It returns the trust class, the sidecar path under
`~/rh-team/wall3/T/certs/`, and the outcome: ACCEPTED, REFUSED (not certifiable as stated), or CONTRADICTED (Arb
disagrees with your float, flagged loudly).
