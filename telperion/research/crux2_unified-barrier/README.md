# Crux round 2, lens "unified barrier": semi-locality is the relativization barrier

**conjecture1_proved = False.** Nothing in this directory says anything about where the zeros of
the Riemann zeta function lie. This work is about *arguments*. It asks which kinds of proof could
possibly establish RH, and it answers with explicit counter-models plus a sharp description of what
the counter-models cannot survive. Every claim below is tagged THEOREM-kernel-checked,
THEOREM-paper-proof, COMPUTED or HEURISTIC, and the tags are meant literally.

The Lean file is
`telperion/examples/li_positivity/lean/Crux/Crux2_unified_barrier.lean`: 2641 lines, 133 theorems
and lemmas, every one printed in the audit block at the end. Every axiom closure is a subset of
`[propext, Classical.choice, Quot.sound]`. There are no proof holes, no kernel-bypassing
evaluation, and no new postulates.

## The short story

Round 1 found four barriers:

- the fooling lemma and its barrier core `W1(29,11)`;
- Build B's golden fake;
- Build C's dynamics/channel no-go;
- the finite-range weakening of the class-P collapse.

Each came with its own cooked model. This lens shows they are one object. For a prime `p` and an
integer `c`, take the Euler product

    W_{p,c}(s) = zeta(s) (1 + c p^{-s} + p p^{-2s}).

This is zeta with a single local factor replaced. Its completion is `xi(s) * surg(s)`, where
`surg(s) = 2 cosh((s - 1/2) log p) + c/sqrt p`. That is an exact Gamma_R-shape functional equation
with conductor `p^2`.

Three numbers govern the family:

- the **Hasse bound** `c^2 <= 4p` (local RH at `p`);
- the **trivial bound** `|c| < p + 1`;
- the prime `p` itself.

Fakes live in the square-root gap `2 sqrt p < |c| < p + 1` at a prime the argument never looks at.

A semi-local argument can only look at:

- finitely many primes;
- a finite range of coefficient positivity;
- the channel axioms;
- Weil positivity at bounded support;
- a summable negative part of the von Mangoldt function.

Such an argument cannot tell `W_{p,c}` from zeta once `p` is large. Every global input that does
tell them apart forces the Hasse bound, and after that, "RH for the class" is literally "RH for
zeta". So relativization locates the crux precisely, but it has nothing to say about how to rank
global strategies.

## What is proved in the kernel (THEOREM-kernel-checked)

1. **The witness is an honest Euler product with the right completion.** The following theorems
   close the chain from the coefficients to the completed function:
   - `aW_isMultiplicative`;
   - `W_isDirExp`, where `a_W = exp*(b_W)` with `b_W = Lambda/log + b_loc`;
   - `LSeries_aW`, which gives `L(a_W, s) = zeta(s)(1 + c p^-s + p p^-2s)` on `Re s > 1`;
   - `W_completion_LSeries`, which gives `xi * surg = (1/2) s(s-1) Gamma_R(s) p^{s-1/2} L(a_W, s)`.

   The coefficient signs come from `bW_pow`, which gives `b_W(p^m) = (1 - t_m)/m` with `t` the
   Lucas power sums:
   - P2 holds on `[0, p^2)` (`bW_nonneg_below`);
   - P2 fails at `p^2` (`bW_sq`);
   - the signs are positive at odd powers and negative at even powers when off-line.

2. **Two of the round-1 axioms are exactly the local trivial bound.**
   - `channelAxioms_W_iff`: `xi * surg` satisfies all seven of Build C's channel axioms **iff**
     `|c| < p + 1`.
   - `robust_positivity_iff`: the de la Vallee Poussin defect `B = sum_n Lambda_W^-(n)/n` is
     finite **iff** `|c| < p + 1`.

   Neither condition can see the Hasse bound. (The contractivity identity behind the channel
   axioms is `Xi_contractive`.)

3. **The support-prime duality, now in the kernel** (`surg_explicit_formula`). Assume
   `c^2 != 4p` and pick `alpha` with `2 cos alpha = -c/sqrt p`. Then:
   - the zeros of `surg` are exactly `1/2 + i gamma` with `gamma = (+-alpha + 2 pi k)/log p`;
   - they are all simple, and the two branches are disjoint;
   - for every smooth test `g` supported in `(-log p, log p)`, the Weil sum of
     `h(gamma) = int g(x) e^{ix gamma} dx` over these zeros is `2 log p * g(0)`, with no
     dependence on `c`;
   - for support in `(-2 log p, 2 log p)` the sum is
     `2 log p (g(0) - (c/(2 sqrt p))(g(log p) + g(-log p)))`, so `c` becomes visible exactly at
     support `log p`.

   The engine is `lattice_poisson`, Poisson summation over a shifted lattice. It is built on
   Mathlib's `SchwartzMap.tsum_eq_tsum_fourier` and `HasCompactSupport.toSchwartzMap`. At the
   idea stage this duality was paper plus numerics.

4. **The semi-local barrier, all six clauses** (`semilocal_barrier_full`). Fix `N0`, a finite set
   `S` and a support radius `L0`. There is a prime `p` outside `S` with `p^2 > N0` and
   `log p > L0`, and an off-line `c`, such that `W_{p,c}` satisfies all six clauses:
   - **X1**: Euler product, a Dirichlet exponential, equal to zeta away from `p`;
   - **X2**: Gamma_R completion of conductor `p^2`, periodic coefficients, the FE top
     coefficient;
   - **X3**: P2 on `[0, p^2)`;
   - **X4**: the channel axioms;
   - **X5**: the support-prime duality, so Weil positivity on `[-L0, L0]` transfers from zeta with
     margin `+ 2 log p g(0)`;
   - **X6**: a finite defect.

   Yet the completion of `W_{p,c}` vanishes at a point with `1/2 < Re s < 1`.

5. **Unification.**
   - `XiA_eq_surg` and `XiH_eq_W55`: Build B's golden hybrid is the completion of the Dirichlet
     series of `W_{5,5}`.
   - `golden_unified_full`: that one object carries the pointwise layer, the channel axioms, the
     class-P data (P2 on `[0, 25)`, failing at 25), a finite defect, and an off-line zero.
   - `classP_sharp`: for every prime `p` and every integer `c`, `W_{p,c}` meets every hypothesis
     of `classP_eq_zeta` except positivity.

6. **LowHeightBox is not semi-local.** `W_{41,13}` satisfies the semi-local interface but has an
   off-line zero below height `sqrt 3/2` (`lowHeightBox_nonrelativizing`,
   `W41_semilocal_violates_box1`).

7. **Exhaustion** (`exhaustion`).
   - Each of the following forces `c^2 <= 4p`:
     - P2 at `p^2`;
     - P2 at all powers of `p`;
     - "no off-line surgery zero below `pi / log 2`".
   - The Selberg-class Euler axiom `b(n) = O(n^theta)`, `theta < 1/2`, fails for **every**
     surgery, on-line ones included (`surgery_not_selberg`). The proof uses the doubling identity
     `t_{2m} = t_m^2 - 2 p^m`, so the local roots have modulus at least `sqrt p`. Zeta satisfies
     the axiom with `theta = 0`.
   - `rh_W_iff`: RH for `xi * surg` is exactly RH for `xi` together with `c^2 <= 4p`.

8. **An incomplete global input is still fooled** (`prime_square_surgery`). Take
   `zeta(s)(1 + A p^{-2s} + p^2 p^{-4s})` with `A = 2p + 1` and `p >= 3`. It has:
   - an Euler product;
   - P2 at **every prime square** and on `[0, p^4)`, failing first at `p^4`;
   - an L-series whose completion has the Gamma_R shape with conductor `p^4`;
   - the channel axioms;
   - an off-line zero in the strip.

   So "P2 at all prime squares" does not pin zeta. The proof goes through a general local Newton
   identity, `locE_isDirExp`, valid for any finite local factor.

## What is paper-level, computed, or heuristic

- **THEOREM-paper-proof (local Weil criterion at support `2 log p`).** Consider positive-type tests
  `g = f * f~` with support in `(-2 log p, 2 log p)`. For these, `|Re g(log p)| <= g(0)/2`: split
  the support of `f` and apply Cauchy-Schwarz. Combined with item 3, the infimum of the surgery's
  Weil sum over such tests is `2 log p * g(0) * (1 - |c|/(2 sqrt p))`. That is negative exactly
  when `c^2 > 4p`.

  So inside the window `[log p, 2 log p)`, local Weil positivity **is** the local Hasse bound. The
  three-point formula is in the kernel; the extremal ratio 1/2 and the two-bump construction are
  on paper. They are checked in `numerics_build.py` N1b, where the sum is negative iff off-line.

  Caution: this concerns the surgery's own contribution. Whether the full `Z_W = Z_zeta + Z_surg`
  turns negative at that support also depends on zeta's part, and is not claimed.
- **THEOREM-paper-proof (membership in M).** The following are paper arguments valid on every
  model of X1 to X6:
  - de la Vallee Poussin with the additive defect `B`;
  - PNT;
  - the small-support Weil positivity results (Yoshida, Connes-Consani, Zhu's window).

  Their membership in the semi-local class is therefore paper-level, not kernel.
- **Bookkeeping.** `Z_W = Z_zeta + Z_surg` holds because the zeros of a product are the union of
  the zeros, with orders adding. It is used only at the level of the zero set.
- **Cited, not re-read.** Kaczorowski-Perelli 1999, degree-one structure: the claim that
  surgeries are all the degree-1 Euler fakes rests on it. If it failed, the exhaustion statement
  would weaken to "exhaustion among surgeries". The barrier and the killers would stand.
- **HEURISTIC.** The claim that relativization cannot rank global strategies, as a statement about
  all possible proofs. The kernel content is the classification of the known global inputs above.

## Negative controls and circularity

- **Davenport-Heilbronn is not in the family.** It has no Euler product, and `Lambda_D(3) < 0`.
  It is also the decisive control for exhaustion: it passes low-height certification (first
  off-line zero near `0.8085 + 85.70 i`) and still has off-line zeros. So low-height certification
  kills fakes only in the presence of the Euler product.
- **Not circular.** The barrier is unconditional and the witnesses have explicit zeros. The only
  input that couples archimedean positivity to all of N without pinning the model to zeta is Weil
  positivity at unbounded support, and that is Weil's criterion, labelled as such.

## Reproducing

```bash
# 1. once: compile the three round-1 modules this file imports (untracked build tree only)
./build_deps.sh
# 2. the official check (from the island)
cd ../../examples/li_positivity/lean
lake env lean Crux/Crux2_unified_barrier.lean
# 3. numerics (mpmath)
cd -; python3 numerics_build.py; python3 numerics_idea_stage.py; python3 numerics_degree4.py
```

Outputs are in `outputs/`:

- `lean_check_official.log`: the full check, exit 0;
- `lean_axiom_audit.txt`: 133 lines;
- `numerics_build.txt`: 88 PASS;
- `numerics_idea_stage.txt`, `numerics_degree4.txt`: the idea-stage checks;
- `build_*.log`: the dependency builds, whose axioms are also within the standard three.

**Why the build step exists.** The file imports `Crux.Crux_meta_barriers`,
`Crux.Crux_dynamics_ergodic` and `Crux.Crux_axiso_theorem`. That way `XiH`, `ChannelAxioms` and
`classP_eq_zeta` in the unification theorems are the round-1 objects themselves, not copies. Those
three modules are not `lean_lib` targets of the island, so `lake build` never compiles them.
`build_deps.sh` compiles them with the island's own toolchain into the untracked
`.lake/build/lib/lean/Crux/`, writing each olean under a temporary name and renaming it into place.

## Novelty

Not verified against the literature. The nearest references are:

- Davenport-Heilbronn 1936;
- Kaczorowski-Perelli 1999 and Conrey-Ghosh 1993 (degree one);
- the Selberg-class Ramanujan and Euler axioms;
- Diamond-Montgomery-Vorhauer 2006 (the Beurling barrier for dVP);
- Connes 1999 and Connes-Consani 2021 (semi-local trace formula, small-support positivity);
- Yoshida 1992 and Bombieri 2000;
- Weil 1948 (trivial bound versus Hasse bound for curves);
- Baker-Gill-Solovay 1975 (the relativization template).
