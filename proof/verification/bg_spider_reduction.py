"""BG spider reduction (part B1): evidence and cell checks for proof/formalization/R3Cert/BGSpiderReduction.lean.

Claim under study: every tree T on n vertices is dominated (pi(S) >= pi(T)) by a two-level spider S on n
vertices: a centre carrying leaves, cherries and arms (arm_j = a vertex whose j >= 1 other neighbours are
all cherries).  Notation as in the Lean files (namespace R3Cert.BGSCL):
  planted branch b: summary (T_b, y_b); leaf (1, 1); node with children c_1..c_p, D = p + 1:
      T = prod T_i * (D + sum y_i)/D,  y = 1/(D + sum y_i)
  root with child list b_1..b_k:  pi = prod T_i * (k + sum y_i)/k
  bell b = log T_b - |b| F*,  F* = log(621/64)/11;  V_mu(b) = bell b + mu y_b
  Phi(T) = log pi(T) - (n-1) F* = sum_i bell b_i + log(1 + sum_i y_i / k)      (Lean `phiRoot_eq`)
  atoms: leaf, cherry, arm_j (j >= 1).  A tree is a spider iff some root has only atom children.

Subcommands (run from proof/verification/):
  python3 bg_spider_reduction.py spider 300          exact (Fraction) best spider per n, n <= N
  python3 bg_spider_reduction.py maxcheck 200 [KC]   float DP over ALL trees (or max degree <= KC) vs exact
                                                     best spider: max_n (Phi_all(n) - Phi_spider(n))
  python3 bg_spider_reduction.py envelope 80 19      branch frontier DP (size <= S) with non-atom tracking:
                                                     sup V_mu over all branches vs over atoms, non-atom gap;
                                                     cross-checked against brute-force enumeration to size B
  python3 bg_spider_reduction.py cells               AtomCell0(1/75), AtomCellMu(23/624, 1/75),
                                                     SurchargeCell(23/624): exhaustive checks (see below)
  python3 bg_spider_reduction.py slack 300           size-free bound X(k) - gap vs the exact spider value;
                                                     gadget (arm_5/arm_4) lower bound per residue
  python3 bg_spider_reduction.py all                 everything at default sizes

Exactness.  Spider values (spider) are exact fractions.Fraction.  Everything involving log (bell, V_mu,
cells, envelope, maxcheck) is IEEE double; every reported margin is >= 1e-5 except the two exact ties
(arm_5 in SurchargeCell: margin 0 at the tie point, where the claim is an equality allowed by <=; and
arm_4 in SurchargeCell / the arm_4 threshold, margin 1.4e-5), which are also the cases proved or
bounded in Lean with rational log enclosures (`bell_arm4_ge`, `cherry_anchor_ge_tight`).  maxcheck is a
floating-point DP (pruning keeps near-ties within 1e-12); it agrees with the exact spider value to
<= 1.5e-14 relative for every n <= 200, and with the repo's exact FrontierDP (hwh_coverage_large_n.py)
for n <= 100.  It is evidence, not an exact certificate, for 100 < n.

RESULT (2026-09-24):
  * maxcheck: max over ALL trees == max over spiders (float, <= 1.5e-14) for every n <= 200
    (the exact DP in hwh_coverage_large_n.py gives it exactly for n <= 100).  In particular n = 31
    (T(5,5,4)) IS a spider: centre x_2 with 5 cherries + arm_5 (x_1) + arm_4 (x_3).
  * envelope (sizes <= 80, frontier == brute force for sizes <= 19): for mu in [0, 1/2] the sup of V_mu
    over ALL branches equals the sup over atoms; the non-atom gap is 0.014520 at mu = 0 (attained by
    node[cherry x5, arm_4], size 20) and 0.015157 at mu = 0.0372.
  * cells: AtomCell0 min gap 0.014520 >= 1/75; AtomCellMu(23/624) min gap 0.015151 >= 1/75;
    SurchargeCell(23/624) max(LHS-RHS) = 0 at d=6 (arm_5 tie), -1.43e-5 at d=5 (arm_4), < -0.002 else.
  * slack: best spider Phi_spider(n) - log(26/23) >= -10*0.0010264 via the arm_5/arm_4 gadget (n >= 91);
    the size-free root bound X(k) - gap(k) < -0.0104 for every k >= 22 (and exactly the k >= 24 case is
    what the Lean file uses, with the arm-only envelope).
conjecture1_proved = False.
"""
from __future__ import annotations

import itertools
import math
import pickle
import sys
import time
from fractions import Fraction as Fr

import numpy as np

F = math.log(621 / 64) / 11
ANCHOR = 2 * F - math.log(1.5)          # rho_wit(cherry) = -bell(cherry)
L26 = math.log(26 / 23)
MU0 = 23 / 624
DELTA = 1 / 75


# ============================================================================ atoms and rho_wit
def arm_exact(j):
    return Fr(3, 2) ** j * Fr(4 * j + 3, 3 * (j + 1)), Fr(3, 4 * j + 3)


def atoms_float(jmax=60):
    """(name, bell, y, bcc, size)."""
    out = [("L", -F, 1.0, 0, 1), ("C", math.log(1.5) - 2 * F, 1 / 3, 1, 2)]
    for j in range(1, jmax + 1):
        T, y = arm_exact(j)
        out.append((f"A{j}", math.log(T) - (2 * j + 1) * F, float(y), j, 2 * j + 1))
    return out


def rho_wit(bcc, y):
    """Lean `ρwit` (BGSCLSubaction.lean)."""
    if bcc == 0:
        return F
    if bcc == 1:
        return ANCHOR + (y - 1 / 3) / 4
    if bcc == 2:
        return y / 32
    if bcc == 3:
        return y / 384
    return 0.0


# ============================================================================ exact spider optimum
def _prune_exact(pts, k):
    D = max(k, 1)
    dec = sorted(pts, key=lambda p: (p[1], -(p[0] * (D + p[1]))))
    kept, best = [], None
    for p in dec:
        v = p[0] * (D + p[1])
        if best is not None and best > v:
            continue
        kept.append(p)
        if best is None or v > best:
            best = v
    return kept


def spider_max(N):
    """Exact best spider per n <= N: {n: (pi, [atom multisets])}."""
    A = [("L", 1, Fr(1), Fr(1)), ("C", 2, Fr(3, 2), Fr(1, 3))]
    j = 1
    while 2 * j + 1 <= N - 1:
        T, y = arm_exact(j)
        A.append((f"A{j}", 2 * j + 1, T, y))
        j += 1
    states = {(0, 0): [(Fr(1), Fr(0), ())]}
    for (nm, sz, T, y) in A:
        for s in range(0, N - sz):
            for k in range(0, s + 1):
                src = states.get((k, s))
                if not src:
                    continue
                key = (k + 1, s + sz)
                dst = states.setdefault(key, [])
                dst.extend((P * T, R + y, rep + (nm,)) for P, R, rep in src)
                states[key] = _prune_exact(dst, k + 1)
    best = {}
    for (k, s), pts in states.items():
        if k == 0:
            continue
        for P, R, rep in pts:
            v = P * (k + R) / k
            n = s + 1
            if n not in best or v > best[n][0]:
                best[n] = (v, [rep])
            elif v == best[n][0]:
                best[n][1].append(rep)
    return best


def phi_of(pi, n):
    return math.log(pi) - (n - 1) * F


# ============================================================================ float tree DP (numpy)
class _Store:
    def __init__(self):
        self.cap, self.n = 1 << 20, 0
        self.lp = np.empty(self.cap)
        self.R = np.empty(self.cap)

    def add(self, lp, R):
        m = len(lp)
        while self.n + m > self.cap:
            self.cap *= 2
            for a in ("lp", "R"):
                old = getattr(self, a)
                new = np.empty(self.cap, dtype=old.dtype)
                new[:self.n] = old[:self.n]
                setattr(self, a, new)
        idx = np.arange(self.n, self.n + m)
        self.lp[idx] = lp
        self.R[idx] = R
        self.n += m
        return idx


def _prune_state(lp, R, k):
    """Drop p1 iff some p2 has R2 <= R1 and lp2 + log(D+R2) > lp1 + log(D+R1) + 1e-12 (valid for every
    continuation, as in hwh_coverage_large_n._prune)."""
    D = max(k, 1)
    v = lp + np.log(D + R)
    o = np.lexsort((-v, R))
    v2 = v[o]
    prevmax = np.concatenate(([-np.inf], np.maximum.accumulate(v2)[:-1]))
    return o[v2 >= prevmax - 1e-12]


def _prune_front(lt, y):
    o = np.lexsort((-lt, -y))
    l2 = lt[o]
    prevmax = np.concatenate(([-np.inf], np.maximum.accumulate(l2)[:-1]))
    return o[l2 > prevmax - 1e-12]


def tree_dp(N, KC=None):
    """Best Phi over all trees on n <= N vertices, every vertex of degree <= KC (None = no cap).
    Exhaustive via the (S, r) Pareto-frontier argument of hwh_coverage_large_n.FrontierDP."""
    KC = KC or N
    st = _Store()
    states = {(0, 0): st.add(np.array([0.0]), np.array([0.0]))}
    t0 = time.time()
    for m in range(1, N):
        cl, cy = [], []
        for k in range(0, KC):                 # a non-root vertex has <= KC-1 children
            e = states.get((k, m - 1))
            if e is None:
                continue
            d = k + 1
            R = st.R[e]
            cl.append(st.lp[e] + np.log((d + R) / d))
            cy.append(1 / (d + R))
        cl, cy = np.concatenate(cl), np.concatenate(cy)
        keep = _prune_front(cl, cy)
        Il, Iy = cl[keep], cy[keep]
        for s in range(0, N - m):
            for k in range(0, KC):
                src = states.get((k, s))
                if src is None:
                    continue
                lp = (st.lp[src][:, None] + Il[None, :]).ravel()
                R = (st.R[src][:, None] + Iy[None, :]).ravel()
                key = (k + 1, s + m)
                old = states.get(key)
                if old is not None:
                    alp, aR = np.concatenate((st.lp[old], lp)), np.concatenate((st.R[old], R))
                else:
                    alp, aR = lp, R
                kp = _prune_state(alp, aR, k + 1)
                no = 0 if old is None else len(old)
                keep_old = old[kp[kp < no]] if old is not None else np.empty(0, dtype=np.int64)
                kn = kp[kp >= no] - no
                newidx = st.add(lp[kn], R[kn]) if len(kn) else np.empty(0, dtype=np.int64)
                states[key] = np.concatenate((keep_old, newidx))
        if m % 50 == 0:
            print(f"  [tree_dp N={N} KC={KC}] m={m} entries={st.n} t={time.time() - t0:.0f}s", flush=True)
    best = {}
    for (k, s), e in states.items():
        if k == 0 or k > KC:
            continue
        v = float(np.max(st.lp[e] + np.log((k + st.R[e]) / k))) - s * F
        n = s + 1
        best[n] = max(best.get(n, -1e18), v)
    return best


def run_maxcheck(N, KC=None):
    sp = spider_max(N)
    t0 = time.time()
    best = tree_dp(N, KC)
    worst = max((best[n] - phi_of(sp[n][0], n), n) for n in range(4, N + 1))
    print(f"[maxcheck] N={N} KC={KC}: max_n (Phi_trees(n) - Phi_spider(n)) = {worst[0]:.3e} at n={worst[1]} "
          f"({time.time() - t0:.0f}s)")
    return worst


# ============================================================================ branch envelope
def _prune_state_py(pts, k):
    D = max(k, 1)
    dec = sorted(pts, key=lambda p: (p[1], -(p[0] + math.log(D + p[1]))))
    kept, best = [], None
    for p in dec:
        v = p[0] + math.log(D + p[1])
        if best is not None and best > v + 1e-13:
            continue
        kept.append(p)
        if best is None or v > best:
            best = v
    return kept


def _prune_front_py(ents):
    dec = sorted(ents, key=lambda e: (-e[1], -e[0]))
    kept, best = [], -1e18
    for e in dec:
        if e[0] <= best + 1e-13:
            continue
        kept.append(e)
        best = e[0]
    return kept


def branch_frontier(S):
    """Pareto frontiers (log T, y) of all planted branches (Fa) and of non-atom branches (Gn) per size <= S.
    Atom status depends only on the child-SIZE multiset (non-atom iff some child has size >= 3, or a leaf
    child with >= 2 children), so frontier replacement of children preserves it."""
    items = []
    states = {(0, 0, 0, 0): [(0.0, 0.0, ())]}
    Fa, Gn = {}, {}

    def add(size, lT, y, ch):
        iid = len(items)
        items.append((size, lT, y, ch))
        for s in range(0, S - size + 1):
            touched = set()
            for k in range(0, s + 1):
                for big in (0, 1):
                    for lf in (0, 1):
                        src = states.get((k, s, big, lf))
                        if not src:
                            continue
                        key = (k + 1, s + size, max(big, int(size >= 3)), max(lf, int(size == 1)))
                        states.setdefault(key, []).extend((P + lT, R + y, rep + (iid,)) for (P, R, rep) in src)
                        touched.add(key)
            for key in touched:
                states[key] = _prune_state_py(states[key], key[0])

    for m in range(1, S + 1):
        cand, non = [], []
        for (k, s, big, lf), pts in list(states.items()):
            if s != m - 1:
                continue
            d = k + 1
            na = big or (lf and k >= 2)
            for (P, R, rep) in pts:
                e = (P + math.log((d + R) / d), 1 / (d + R), rep)
                cand.append(e)
                if na:
                    non.append(e)
        Fa[m], Gn[m] = _prune_front_py(cand), _prune_front_py(non)
        if m < S:
            for (lT, y, rep) in Fa[m]:
                add(m, lT, y, rep)
    return items, Fa, Gn


def brute_branches(B):
    """All planted branches of size <= B: {size: [(logT, y, nonatom)]} (A000081 counts)."""
    trees = {1: [(0.0, 1.0, False)]}
    for m in range(2, B + 1):
        allt = [(s, i) for s in range(1, m) for i in range(len(trees[s]))]
        out = []

        def rec(start, rem, P, R, k, big, lf):
            if rem == 0:
                d = k + 1
                out.append((P + math.log((d + R) / d), 1 / (d + R), bool(big or (lf and k >= 2))))
                return
            for j in range(start, len(allt)):
                s, i = allt[j]
                if s > rem:
                    break
                lT, y, _ = trees[s][i]
                rec(j, rem - s, P + lT, R + y, k + 1, big or s >= 3, lf or s == 1)
        rec(0, m - 1, 0.0, 0.0, 0, False, False)
        trees[m] = out
    return trees


def run_envelope(S=80, B=19):
    t0 = time.time()
    items, Fa, Gn = branch_frontier(S)
    tr = brute_branches(B)
    grid = [0, 0.005, 0.01, 0.02, 0.03, 0.0372, 0.04, 0.06, 0.08, 0.1, 0.12, 0.15, 0.2, 0.3, 0.43, 0.5]
    bad = 0
    for mu in grid:
        for s in range(1, B + 1):
            ba = max(l - s * F + mu * y for l, y, _ in tr[s])
            fa = max(l - s * F + mu * y for l, y, _ in Fa[s])
            nb = [l - s * F + mu * y for l, y, na in tr[s] if na]
            if abs(ba - fa) > 1e-12 or (nb and abs(max(nb) - max(l - s * F + mu * y for l, y, _ in Gn[s])) > 1e-12):
                bad += 1
    print(f"[envelope] frontier vs brute force (sizes <= {B}, {len(grid)} prices): mismatches = {bad}")
    AT = atoms_float(S)

    def desc(rep):
        return "[" + ",".join(desc(items[c][3]) for c in rep) + "]"
    for mu in grid:
        wa = max((b + mu * y, nm) for nm, b, y, _, _ in AT)
        wall = max(l - s * F + mu * y for s in Fa for l, y, _ in Fa[s])
        gb = max((l - s * F + mu * y, s, r) for s in Gn for l, y, r in Gn[s])
        print(f"  mu={mu:.4f} W_atoms={wa[0]:+.6f} ({wa[1]:>3})  W_all-W_atoms={wall - wa[0]:+.1e}  "
              f"non-atom gap={wa[0] - gb[0]:.6f} (size {gb[1]}: {desc(gb[2])[:70]})")
    print(f"[envelope] ({time.time() - t0:.0f}s)")


# ============================================================================ cell families
def run_cells():
    """AtomCell0 / AtomCellMu: children atoms, node not an atom.
      Reduction to finitely many cases: for K >= 4 children the node value is increasing in (sum bell,
      sum y) (rho_wit(node) = 0; and d/dS [log(1+S/d) + mu0/(d+S)] > 0), and arm_j (j >= 6) is dominated by
      arm_5 in both coordinates (bell_j < 0 = bell_5, y_j < 3/23), while replacing a non-cherry by arm_5
      keeps the node a non-atom.  So for 4 <= K <= 22 it suffices to enumerate multisets over
      {leaf, cherry, arm_1..arm_5}; K <= 3 is enumerated over arms up to j = 60 (rho_wit(node) is not
      monotone there); K >= 23 holds analytically: tangent at t = 26/23 (price 23/(26(K+1)) <= 23/624, where
      every ATOM a has V(a) <= 3 mu/23), giving value <= log(26/23) - F* ~ -0.0840.
    SurchargeCell(mu0): children arbitrary; they enter through (bcc, y) only; classes
      leaf (y=1), bcc=1 (y in [1/3,1/2]), bcc=2 ([1/5,1/3]), bcc=3 ([1/7,1/4]), bcc>=4 ((0,1/5], rho=0).
      For a class multiset the min of sum rho at fixed S = sum y is the greedy fill (slopes 0, 1/384,
      1/32, 1/4); f(S) = log(1+S/d) - F* + mu0 (1/(d+S) - 3/23) - rho_min(S) is concave, so its max on
      each linear piece is at an endpoint or at the root of f' = 0 (solved exactly).  d >= 8 follows from
      isSubaction_rhowit (the surcharge is <= 0 when d + S >= 23/3)."""
    AT = atoms_float(60)
    small = [a for a in AT if a[0] in ("L", "C", "A1", "A2", "A3", "A4", "A5")]

    def node_vals(ms):
        K = len(ms)
        d = K + 1
        S = sum(a[2] for a in ms)
        sb = sum(a[1] for a in ms)
        e = math.log(1 + S / d) - F
        y = 1 / (d + S)
        return sb + e + rho_wit(K, y), (sb + e + MU0 * (y - 3 / 23)) if K >= 3 else None

    def is_atom_node(ms):
        nm = [a[0] for a in ms]
        return len(nm) == 0 or nm == ["L"] or all(x == "C" for x in nm)
    w0, wm = (1e9, None), (1e9, None)
    for K in range(1, 23):
        pool = AT if K <= 3 else small
        for ms in itertools.combinations_with_replacement(pool, K):
            if is_atom_node(list(ms)):
                continue
            q0, qm = node_vals(ms)
            if -q0 < w0[0]:
                w0 = (-q0, [a[0] for a in ms])
            if qm is not None and -qm < wm[0]:
                wm = (-qm, [a[0] for a in ms])
    # K >= 23 tail: check the atom-wise premise V_mu(a) <= 3 mu/23 on mu in [0, 23/624] (affine: endpoints)
    prem = max(max(b, b + MU0 * (y - 3 / 23)) for _, b, y, _, _ in AT)
    print(f"[cells] AtomCell0  : min over non-atom atom-children nodes of -(bell+rho_wit) = {w0[0]:.6f} at {w0[1]}"
          f"  (need >= 1/75 = {DELTA:.6f})")
    print(f"[cells] AtomCellMu : min of 3mu0/23 - V_mu0 (K>=3)                   = {wm[0]:.6f} at {wm[1]}")
    print(f"[cells] tail K>=23 : max_atoms max(bell, V_mu0 - 3mu0/23) = {prem:.2e} (<= 0 needed); "
          f"tail value <= log(26/23)-F* = {L26 - F:.4f}")
    # SurchargeCell
    CL = [("L", 1.0, 1.0, F, 0.0), ("D2", 1 / 3, 1 / 2, ANCHOR, 0.25), ("D3", 1 / 5, 1 / 3, 1 / 160, 1 / 32),
          ("D4", 1 / 7, 1 / 4, 1 / (7 * 384), 1 / 384), ("D5", 0.0, 1 / 5, 0.0, 0.0)]
    for d in range(4, 8):
        best = (-1e9, None)
        for ms in itertools.combinations_with_replacement(range(len(CL)), d - 1):
            lo = sum(CL[i][1] for i in ms)
            r0 = sum(CL[i][3] for i in ms)
            segs = sorted((CL[i][4], CL[i][2] - CL[i][1]) for i in ms if CL[i][2] > CL[i][1])
            S, r = lo, r0
            pts = [(S, r)]
            cands = []
            for sl, w in segs:
                # critical point of f on this piece: 1/(d+S) - mu0/(d+S)^2 = sl  ->  sl u^2 - u + mu0 = 0, u=d+S
                if sl > 0:
                    disc = 1 - 4 * sl * MU0
                    for u in ((1 + math.sqrt(disc)) / (2 * sl), (1 - math.sqrt(disc)) / (2 * sl)):
                        Sc = u - d
                        if S < Sc < S + w:
                            cands.append((Sc, r + sl * (Sc - S)))
                S, r = S + w, r + sl * w
                pts.append((S, r))
            for (S, r) in pts + cands:
                v = math.log(1 + S / d) - F + MU0 * (1 / (d + S) - 3 / 23) - r
                if v > best[0]:
                    best = (v, [CL[i][0] for i in ms], S)
        print(f"[cells] SurchargeCell d={d}: max(LHS - RHS) = {best[0]:+.3e} at {best[1]} S={best[2]:.4f}")


# ============================================================================ slack / size-free bound
def run_slack(N=300):
    AT = atoms_float(60)

    def W(mu):
        return max(b + mu * y for _, b, y, _, _ in AT)
    items, Fa, Gn = branch_frontier(40)

    def Wna(mu):
        return max(l - s * F + mu * y for s in Gn for l, y, _ in Gn[s])
    print("[slack] size-free root bound Psi(k) = min_t [log t + 1/t - 1 + k W(1/(k t))];  X(k) = Psi(k) - log(26/23)")
    for k in list(range(2, 31)):
        best = (1e9, None)
        for i in range(1, 6001):
            t = 0.05 + i / 2000
            mu = 1 / (k * t)
            v = math.log(t) + 1 / t - 1 + k * W(mu) - (W(mu) - Wna(mu))
            if v < best[0]:
                best = (v, mu)
        print(f"  k={k:2d}: min_t [bound with one non-atom child] - log(26/23) = {best[0] - L26:+.5f} (mu={best[1]:.4f})")
    beta4 = -(math.log(float(arm_exact(4)[0])) - 9 * F)
    print(f"[slack] -bell(arm_4) = {beta4:.7f} (Lean: <= 1/960 = {1 / 960:.7f}); gadget cost q*beta4, q=(5(n-1)) mod 11 <= 10: "
          f"max {10 * beta4:.5f} < 1/75 = {DELTA:.5f}")
    sp = spider_max(N)
    rows = [(n, phi_of(sp[n][0], n) - L26) for n in range(91, N + 1)]
    print(f"[slack] exact best spider, n in [91,{N}]: min (Phi_spider - log(26/23)) = {min(r[1] for r in rows):+.5f}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    a = [int(x) for x in sys.argv[2:]]
    if cmd == "spider":
        N = a[0] if a else 100
        sp = spider_max(N)
        for n in range(1 + 1, N + 1):
            v, reps = sp[n]
            print(n, f"{phi_of(v, n):.10f}", sorted(set(tuple(sorted(r)) for r in reps)))
    elif cmd == "maxcheck":
        run_maxcheck(a[0] if a else 200, a[1] if len(a) > 1 else None)
    elif cmd == "envelope":
        run_envelope(a[0] if a else 80, a[1] if len(a) > 1 else 19)
    elif cmd == "cells":
        run_cells()
    elif cmd == "slack":
        run_slack(a[0] if a else 300)
    elif cmd == "all":
        run_cells()
        run_envelope(80, 19)
        run_slack(200)
        run_maxcheck(200)
    else:
        print(__doc__)
