# BG finite range: feasibility of a small certificate (phase 1, Python only, 2026-09-25)

Goal: a certificate small enough for the Lean kernel that every non-spider tree on n <= 491 vertices has
pi < M(n), where M(n) is the exact best spider. This is the range the Lean theorems leave to computation
(`spider_dominates_of_maxDegreeRoot` needs n - 1 >= 491). The kernel budget is about 1e5-1e6 exact
checks.

Scripts are in `proof/verification/finite_cert/` (run from that folder; the first run caches M(n) for
n <= 520 exactly). **All numbers below are IEEE floats (exploration only).** `conjecture1_proved = False`.

## Short answer

1. **Tightness: yes.** The proposed scalar Bellman envelope, combined with an exact size-knapsack at the
   root and a root at a max-degree vertex (children capped at k-1 children per vertex, at least one child
   not an atom), bounds every n with **7 <= n <= 491** below the best spider. The worst margin is
   **4.4e-5 at n = 23 (k = 5)**. The one failure is n = 6, which is an artifact: P6 is itself the optimal
   spider and has a non-atom rooting. So n <= 6 must be checked directly, which is trivial. The best
   hybrid split is therefore **N_exact = 6**; no exact frontier DP is needed above that.
2. **Size: no.** In the tested form the certificate is far over budget. The max-plus knapsack
   verifications dominate: about 1.7e9 inner checks and 5.1e8 root checks. Every size-free or count-free
   relaxation I tried to remove them loses more than the margins allow (table below).

## 1. What was tested

**True envelope** (`rootcap.py`, reference). The inputs are the exact per-size envelopes
`W_s(mu) = max_{|b|=s} bell(b) + mu*y_b` and the non-atom version `W^na_s`, taken from Pareto frontiers
(`front_na.py`). The frontiers carry non-atom tracking and child caps C = 1..22, plus an uncapped one.
The root bound is

`B(n,k) = min_t [log t + 1/t - 1 + max over compositions of n-1 into k parts, >= 1 non-atom, of sum W_{s_i}(1/(kt))]`,

with child cap k-1. Result for n <= 120 (all k): the only failure is n = 6 (-7e-6). The minimum margin
for n >= 10 is **2.57e-4 (n = 23, k = 5)**.

**Scalar Bellman** (`bellman.py`, `rootbell2.py`). At a vertex with c children (d = c+1), the tangent of
the concave `phi(Y) = log(d+Y) + mu/(d+Y)` gives

`V_mu(b) <= [log(u/d) + mu/u - F* - nu*(u-d)] + sum_children V_nu(child)`, with `u = d + Y0` and
`nu = 1/u - mu/u^2`.

Here nu is taken on the same mu-grid and u is solved from nu, so there is no interpolation.
`W_s(mu) <= max_c min_nu [const + K_c(s-1, nu)]`, where K_c is the exact max-plus knapsack over
compositions. A second knapsack tracks whether the parent is a non-atom (some part != 2; for c = 1,
child size >= 3). Comparison with the true envelope (S = 120): the Bellman bound is never below the
truth, and it is looser by at most 0.0027 (H = 100). The root bound is as above, with t = 1/(k*mu_g) on
the grid.

Coverage of (n, k): n <= 491 for k <= 23 up to the per-k Lean thresholds (k = 2: 28, 3: 70, 4: 104,
5: 298, k >= 6: 491). For k >= 24, n <= 90, since n >= 91 there is the proven high-degree theorem.

| variant | result |
|---|---|
| Bellman, H = 100 uniform grid on (0, 1/2], caps C = k-1 | **fails only n = 6**. Smallest margins: 4.4e-5 (n=23,k=5), 7.0e-4 (39,8), 1.0e-3 (41,8), 1.0e-3 (45,9), 1.2e-3 (29,6) |
| same, H = 50 | 19 failures (n = 23, 39, 43, 45, 162-187 at k = 19, 219 at k = 23); worst -0.0020 |
| same, H = 30 | 244 failures; worst -0.025 |
| caps {1..8, 12, 16, 22} + uncapped (n <= 90), H = 100 | fails only n = 6 (11 cap tables are enough) |
| caps {1..5, 22} | 69 failures (k = 7, 8 need their own caps) |

The losses at H = 50 come from the root price mu = 1/(kt) near 0.04 for k = 19..23. A non-uniform grid
that is dense in [0.02, 0.15] should bring H down; this was not tested.

## 2. Relaxations tried to shrink the certificate (all fail)

| relaxation | test | result |
|---|---|---|
| Size-priced envelope at the root: `B <= (k-1)W^(mu,lam) + W^na(mu,lam) + lam(n-1)`, with `W^(mu,lam) = sup_b bell - lam|b| + mu*y` (size-free) | true envelopes, n <= 120 | 77 of 118 n fail, worst -0.0126 (integrality gap at the root) |
| Size-dual per child `W_s <= min_lam W^ + lam*s` for s > S1, exact for s <= S1 | true envelopes, n <= 120 | S1 = 0: 77 fail; 10: 45; 20: 17; **40: only n = 6 and n = 23 (-6e-5)** |
| Two exact levels (root and children exact, grandchildren size-relaxed via W^) | true W^, n <= 120 | 115 fail, worst -0.049 (atom structure lost) |
| Part-count Lagrangian at the root: k-part knapsack <= phi_kappa(N) + k*kappa | Bellman tables, n <= 491 | 102 fail (k = 7..10), worst -0.0065 |

So the size index cannot be dropped at the root or at the root's children, and only partly below that
(the S1 = 40 split roughly survives, with n = 23 marginal). The part count cannot be relaxed at the root
either.

## 3. Certificate size of the working scheme

Measured by `closure.py`. H = 100; the 11 caps above; the grid closure is the set of grid points reached
by the chosen witnesses, starting from the root choices.

| item | count |
|---|---|
| grid closure per cap | 18 (C=1), 47, 63, 70, 76, 77, 79, 81, 85 (C=12), 87 (C=16), 89 (C=22), 91 (uncapped): the witnesses spread over most of the grid |
| table entries W_s, W^na_s at closure points | 7.7e5 |
| Bellman witness checks (one per entry per child count c) | 8.3e6 |
| **inner max-plus knapsack checks** `K_c[N] >= K_{c-1}[N-m] + W_m` for all m | **1.7e9** |
| **root knapsack checks** (k parts, N <= threshold, per root grid point) | **5.1e8** |

What would need exact rechecks in a kernel version:
- Every table entry as a rational upper bound.
- The constants `log(u/d)`. Solving u from a grid nu introduces a square root, so use rational u from a
  finite set per c instead; that needs one log enclosure per (c, u), about 22 x |U| logs. nu then lands
  off the grid, which chords of the table handle soundly, because V_nu(child) is affine in nu.
- M(n) exactly (available).
- n <= 6 directly.

## 4. Assessment and suggested next steps

- The certificate idea is sound and tight: every 7 <= n <= 491 passes with H = 100. The obstacle is the
  max-plus knapsack verification, which is inherently about S^2 per (cap, part count, grid point).
- The most promising reduction measured is the S1 = 40 hybrid: exact per-size tables only up to size 40,
  and an affine-in-size dual `W^(mu,lam) + lam*s` for larger children, which turns all large parts into
  one "bulk" term. That cuts the inner knapsack to about C * 40^2 * H and the root knapsack to about
  k * N * 40 per root grid point.
  - Rough count: about 1e7-1e8 checks, still 10-100x over budget.
  - It needs W^(mu,lam) certified by its own size-free Bellman fixed point, with exact small children,
    and that bound's looseness is untested (the size-free two-level test above failed badly).
  - n = 23 is marginal (-6e-5 with true envelopes at H = 60) and needs a finer grid or an exact
    treatment of n <= about 30.
- The alternative remains the interval DP (12.3M states). Given the numbers above, a kernel certificate of
  about 1e6 checks for the whole range n <= 491 does not look reachable with envelope and knapsack
  methods alone. A realistic target is to lower the analytic threshold N1 (currently 492, set by a weak
  rate alpha = 1/3700 at degree 6 with root degree 6), so that the finite range becomes small enough for
  the existing exact DP to be kernel-checked.
