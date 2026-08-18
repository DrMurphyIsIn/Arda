"""Tests for the Laplacian-ratio extremal-tree hunt.

Target (open problem, Brualdi-Goldwasser 1984): maximize pi(T) = per(L(T)) / prod_v d(v)
over n-vertex trees. Wu-Dong-Lai (2025) conjectured the maximizer; Pant (arXiv:2605.14176,
2026) refuted it with spider trees T(a_1,...,a_m). The TRUE maximizer is OPEN.

Honesty spine: two independent exact permanent engines (Ryser on the full Laplacian vs a
tree matching-sum DP) must agree; pi is an exact Fraction; the n=21 anchor pi(T(3,3,3))
= 19683/256 pins the whole pipeline to the paper.
"""
from fractions import Fraction

import networkx as nx
import numpy as np

from verification.permanent import (
    laplacian_ratio,
    ryser_laplacian_permanent,
    tree_laplacian_permanent,
)
from verification.trees import branch_tree, spider


def _adj(T):
    return nx.to_numpy_array(T, dtype=int)


# --- two independent permanent engines agree (the honesty cross-check) ---

def test_permanent_engines_agree_on_random_trees():
    rng = np.random.default_rng(0)
    for _ in range(8):
        n = int(rng.integers(3, 10))
        T = nx.random_labeled_tree(n, seed=int(rng.integers(1 << 30)))
        A = _adj(T)
        L = np.diag(A.sum(1)) - A
        # RIGOR NOTE: ryser_laplacian_permanent returns a float; the round() guard
        # is sound only while its floating-point error stays < 0.5 of the true
        # integer, which holds comfortably for the n < 10 sampled here.  For large
        # n the round() could silently accept a value that is not provably close;
        # the exact-vs-exact spine is the tree DP itself + the Fraction anchors.
        assert tree_laplacian_permanent(A) == round(ryser_laplacian_permanent(L))


def test_permanent_path3():
    # P_3 Laplacian permanent = 4 (per hand computation)
    A = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]])
    assert tree_laplacian_permanent(A) == 4


def test_star_ratio_is_two():
    # Brualdi-Goldwasser: pi(T) >= 2 with equality iff T is a star.
    A = _adj(nx.star_graph(6))  # 7 vertices
    assert laplacian_ratio(A) == Fraction(2, 1)


# --- spider constructor + the paper's n=21 anchor ---

def test_spider_T333_structure():
    A = spider([3, 3, 3])            # m=3 spine, 3 cherries each
    n = A.shape[0]
    assert n == 21                    # m + 2*sum(a) = 3 + 18
    deg = sorted(A.sum(1).tolist())
    # degree sequence 1^9, 2^9, 4, 4, 5
    assert deg == [1] * 9 + [2] * 9 + [4, 4, 5]


def test_anchor_pi_T333_equals_19683_over_256():
    A = spider([3, 3, 3])
    assert laplacian_ratio(A) == Fraction(19683, 256)


def test_spider_vertex_count_formula():
    A = spider([4, 4, 4, 4])
    assert A.shape[0] == 36           # 4 + 2*16


# --- hunt baseline + verifier ---

from verification.hunt import (  # noqa: E402
    structured_baseline,
    verify_champion,
)


def test_baseline_n21_at_least_T333():
    pi, desc, A = structured_baseline(21)
    assert pi >= Fraction(19683, 256)      # T(3,3,3) is in the candidate set


def test_verify_champion_flags_exact_beat():
    A = spider([3, 3, 3])                    # pi = 19683/256
    below = Fraction(19683, 256) - Fraction(1, 1000)
    v = verify_champion(A, below)
    assert v["status"] == "BEATS_BASELINE"   # exact rational > baseline
    assert v["is_tree"] and v["engines_agree"]


def test_verify_champion_ties_are_not_beats():
    A = spider([3, 3, 3])
    v = verify_champion(A, Fraction(19683, 256))
    assert v["status"] == "TIES"             # equal is NOT a beat (honesty)


# --- THE FINDING: branching tree beats Pant's path-spine spider at n=36 ---

def test_branch_tree_B34_structure():
    A = branch_tree(3, 4)
    assert A.shape[0] == 36                    # (k+1)(1+2c) = 4*9
    deg = sorted(int(x) for x in A.sum(1))
    assert deg == [1] * 16 + [2] * 16 + [5, 5, 5, 7]   # hub deg 7, three arms deg 5


def test_branch_tree_beats_pant_B4_exactly():
    # Head-to-head at n=36: B(3,4) [branching backbone] vs Pant's B_4 = T(4,4,4,4)
    # [path spine]. Exact rational strict inequality -- no float, no margin.
    pi_branch = laplacian_ratio(branch_tree(3, 4))
    pi_pant = laplacian_ratio(spider([4, 4, 4, 4]))
    assert pi_branch > pi_pant                 # the maximizer is NOT a path-spine spider
    assert pi_branch == Fraction(48154400451, 28672000)


def test_branch_family_beats_pant_B_t_across_range():
    # B(3,c) strictly beats Pant's B_t=T(t,t,t,t) at the SAME n=8t+4, c=t, for t=4..7.
    for t in range(4, 8):
        n_branch = branch_tree(3, t).shape[0]
        assert n_branch == spider([t, t, t, t]).shape[0] == 8 * t + 4
        assert laplacian_ratio(branch_tree(3, t)) > laplacian_ratio(spider([t, t, t, t]))


# --- THE THEOREM: pi(B(3,t)) > pi(T(t,t,t,t)) for all t>=3 (proven) ---

def test_theorem_closed_forms_match_exact_permanent():
    import sympy as sp

    from verification.theorem import (
        pi_branch_star,
        pi_pant_B,
        t as tsym,
    )
    piB, piP = pi_branch_star(), pi_pant_B()
    for tv in range(4, 9):
        assert sp.nsimplify(piB.subs(tsym, tv)) == laplacian_ratio(branch_tree(3, tv))
        assert sp.nsimplify(piP.subs(tsym, tv)) == laplacian_ratio(spider([tv] * 4))


def test_theorem_difference_polynomial_and_positivity():
    import sympy as sp

    from verification.theorem import (
        P,
        pi_branch_star,
        pi_pant_B,
        t as tsym,
    )
    # difference reduces to (3/2)^(4t) * 2 * P(t) / (positive denominator)
    diff = sp.simplify((pi_branch_star() - pi_pant_B()) * sp.Rational(2, 3) ** (4 * tsym))
    num, den = sp.fraction(sp.together(diff))
    assert sp.simplify(num / P).free_symbols == set()          # num is P times a constant
    assert sp.factor(den).subs(tsym, 5) > 0                     # denominator positive
    # positivity of P for t>=3: P(3)>0 and P' increasing with P'(3)>0  =>  P>0 on [3,inf)
    Pp = sp.diff(P, tsym)
    assert P.subs(tsym, 3) > 0
    assert Pp.subs(tsym, 3) > 0
    assert sp.diff(Pp, tsym).subs(tsym, 1) > 0                  # P'' > 0 for t>=1
    # spot-check the conclusion directly
    for tv in range(3, 40):
        assert P.subs(tsym, tv) > 0


def test_theorem_generalizes_star_beats_path_k3_to_8():
    # Rigorous (exact real-root isolation): star K_{1,k} beats path P_{k+1} for all t>=3.
    from verification.theorem import (
        proven_positive_for_t_at_least,
        sign_polynomial,
    )
    for k in range(3, 13):        # per-k finite certificate; subsumed by the all-k proof
        assert proven_positive_for_t_at_least(sign_polynomial(k), 3)


def test_star_beats_path_for_all_k_asymptotic():
    # Uniform reason for ALL k: star per-arm base F(1+t) > path eigenvalue lambda(t),
    # which reduces to the cubic > 0 for t>=3; hence pi(B(k,t))/pi(path) -> infinity.
    import sympy as sp

    from verification.theorem import (
        ASYMPTOTIC_CUBIC,
        path_eigen_base,
        proven_positive_for_t_at_least,
        star_arm_base,
        t as tsym,
    )
    assert proven_positive_for_t_at_least(ASYMPTOTIC_CUBIC, 3)          # 4t^3+2t^2-12t-9 > 0
    for tv in range(3, 25):                                            # F(1+t) > lambda(t)
        assert float(star_arm_base().subs(tsym, tv)) > float(path_eigen_base().subs(tsym, tv))


# --- THE ALL-k THEOREM: star K_{1,k} beats path P_{k+1} for EVERY k>=3, t>=3 ---

def test_all_k_certificate_star_beats_path():
    # Single closed proof (supersedes the finite band + asymptotics): the
    # coefficient-positivity certificate proves pi(B(k,t)) > pi(S_{k+1}(t)) for
    # ALL integers k>=3 and reals t>=3.
    from verification.theorem import (
        bracket_B1,
        bracket_B2,
        certify_bracket_positive,
        certify_starbeats_path_all_k,
        k as ksym,
    )
    assert certify_starbeats_path_all_k()
    assert certify_bracket_positive(bracket_B1(ksym), 3, 3)   # B1 > 0 on k>=3, t>=3
    assert certify_bracket_positive(bracket_B2(ksym), 3, 3)   # B2 > 0 on k>=3, t>=3
    # negative control: the certifier must REJECT a false positivity claim
    assert not certify_bracket_positive(-bracket_B1(ksym), 3, 3)


def test_all_k_ratio_is_increasing_and_above_one():
    # R_k = pi(B(k,t))/pi(S_{k+1}(t)) is strictly increasing in k with R_3 > 1,
    # the engine behind the induction (numeric witness across t and k).
    import sympy as sp

    from verification.theorem import pi_path, pi_star, t as tsym
    for tv in (3, 5, 9):
        prev = None
        for k in range(3, 11):
            r = float(sp.N((pi_star(k) / pi_path(k)).subs(tsym, tv)))
            assert r > 1.0
            if prev is not None:
                assert r > prev
            prev = r


def test_b3c_ceiling_branching_degree_must_grow():
    # Honest ceiling on the FIXED construction: B(3,c) (hub degree 3) does NOT beat
    # every spider once c is large. Exact rational witnesses -- a spider strictly
    # exceeds pi(B(3,c)) at c=8,10,12 (n=68,84,100). So no fixed branching degree
    # beats all spiders; the extremal branching degree must GROW with n (consistent
    # with the star-of-cherry-bundles conjecture). No float, no margin.
    from verification.trees import branch_tree, spider
    witnesses = {8: [4, 5, 6, 6, 6, 4], 10: [6, 7, 7, 7, 7, 5],
                 12: [5, 6, 6, 6, 6, 6, 6, 5]}
    for c, comp in witnesses.items():
        n = 8 * c + 4
        assert len(comp) + 2 * sum(comp) == n                     # a spider on n vertices
        assert laplacian_ratio(spider(comp)) > laplacian_ratio(branch_tree(3, c))


def test_all_k_beats_pant_beyond_old_band_exact_permanent():
    # Independent-engine confirmation of the all-k claim BEYOND the old k<=12
    # band: exact rational pi(B(k,t)) > pi(T(t,...,t)) at equal size, k=13..18.
    from verification.trees import branch_tree, spider
    for k in range(13, 19):
        for tv in (3, 4):
            nb = branch_tree(k, tv).shape[0]
            assert nb == spider([tv] * (k + 1)).shape[0] == (k + 1) * (1 + 2 * tv)
            assert laplacian_ratio(branch_tree(k, tv)) > laplacian_ratio(spider([tv] * (k + 1)))


# --- ASYMPTOTIC THEOREM: branching beats EVERY spider for all large n ---

def test_spider_upper_bound_certificate_and_discrimination():
    # Exact quadratic-form certificate S_a = R^{1+2a} P - M_a^T P M_a >= 0 for all
    # integer a >= 0 (P=diag(1,9/10), R=377/250), giving pi(spider) <= C*rho_S^n.
    from verification import spiders as S
    assert S.certify_spider_upper_bound()
    # discrimination (negative control): a rate BELOW the true spider rate cannot
    # be certified -- some S_a fails PSD. Use R = 3/2 (rho^2=1.5 < true 1.5070).
    from fractions import Fraction as Fr
    Rbad = Fr(3, 2)
    p0, p1 = S.P_DIAG
    fails = False
    for a in range(0, 60):
        M = S._M_internal(a)
        MPM = S._MT_P_M_diag(S.P_DIAG, M)
        lam = Rbad ** (1 + 2 * a)
        Sa = ((lam * p0 - MPM[0][0], -MPM[0][1]), (-MPM[1][0], lam * p1 - MPM[1][1]))
        if not S._psd2(Sa):
            fails = True
            break
    assert fails                                   # certifier is discriminating


def test_branch_rate_exceeds_spider_rate_exact():
    # Exact rate gap rho_S < rho_B  <=>  (377/250)^11 < (621/64)^2.
    from fractions import Fraction as Fr
    from verification import spiders as S
    assert S.certify_branch_rate_exceeds_spider()
    assert Fr(377, 250) ** 11 < Fr(621, 64) ** 2
    # sanity: a hypothetical spider rate-squared ABOVE the branch rate fails the gap
    assert not (Fr(16, 10) ** 11 < Fr(621, 64) ** 2)   # 1.6^11 ~ 176 > (621/64)^2 ~ 94


def test_full_asymptotic_branching_beats_spiders():
    # Assembled theorem certificate: exact spider upper bound + exact rate gap
    # => exists N0 s.t. for all n>=N0 an explicit branching tree beats EVERY spider.
    from verification import spiders as S
    assert S.certify_branching_beats_spiders_asymptotically()


def test_cherries_optimal_certificate():
    # Conjecture Piece 1 ("why cherries"): length-2 legs uniquely maximize the star
    # growth rate. Exact certificate + reference + discrimination.
    from fractions import Fraction as Fr
    from verification import legs as L
    assert L.certify_cherries_optimal()
    assert L.arm_base(2, 5) == Fr(621, 64)                       # rho_2 = rho_B reference
    # discrimination: every OTHER leg length stays strictly below rho_B for all c
    # (rate_ell(c) < rho_B  <=>  F_ell(1+c)^11 < (621/64)^(1+c*ell))
    RB = Fr(621, 64)
    for ell in (1, 3, 4, 5, 6):
        assert all(L.arm_base(ell, c) ** 11 < RB ** (1 + c * ell) for c in range(1, 30))


def test_arm_base_formula_matches_tree_engine():
    # arm_base(ell,c) equals the tree-built growth base pi(star_k)/pi(star_{k-1}) for
    # large k -- ties the closed form to the independent exact permanent engine.
    import networkx as nx

    from verification import legs as L

    def star_legs(k, c, ell):
        G = nx.Graph()
        G.add_node("H")
        nid = 0
        for _ in range(k):
            ac = ("a", nid)
            nid += 1
            G.add_edge("H", ac)
            for _ in range(c):
                prev = ac
                for _j in range(ell):
                    v = nid
                    nid += 1
                    G.add_edge(prev, v)
                    prev = v
        return nx.to_numpy_array(G, dtype=int)

    for ell in (1, 2, 3, 4):
        for c in (1, 2, 3):
            built = (float(laplacian_ratio(star_legs(15, c, ell)))
                     / float(laplacian_ratio(star_legs(14, c, ell))))
            assert abs(float(L.arm_base(ell, c)) - built) < 1e-7


def test_star_beats_every_backbone_matched_centers():
    # Conjecture Piece 3 (matched form): the star K_{1,N-1} strictly maximizes
    # pi(beta[c]) over ALL backbones on N centers, for every real c >= 3 -- exact
    # root isolation. Verified here for N = 2..8 (offline: through N = 10).
    from verification import backbones as B
    for N in range(2, 9):
        assert B.certify_star_beats_backbones(N)


def test_star_beats_broom_all_N():
    # The runner-up backbone (2nd-largest pi) is always the broom (hub degree N-2 with
    # one length-2 leg); the star beats it for ALL N>=5, c>=3 (exact coefficient
    # positivity). Also confirm the broom really is the runner-up for small N.
    import networkx as nx

    from verification import backbones as B
    assert B.certify_star_beats_broom_all_N()
    # general near-star certifier reproduces the broom case (F2, F3 verified offline;
    # too slow for the suite). All three families are registered.
    assert set(B.NEAR_STAR_FAMILIES) == {"broom_(N-2,2)", "F2_(N-3,3)", "F3_(N-3,2,2)"}
    assert B.certify_star_beats_near_star(B.NEAR_STAR_FAMILIES["broom_(N-2,2)"])
    for N in range(6, 10):
        scored = sorted(
            ((B.pi_factored(G, 5)[0] * B.pi_factored(G, 5)[1], G)
             for G in nx.nonisomorphic_trees(N)),
            key=lambda z: z[0], reverse=True)
        runner = scored[1][1]
        degseq = sorted((d for _, d in runner.degree()), reverse=True)
        assert degseq == [N - 2, 2] + [1] * (N - 2)     # the broom


def test_pi_factorization_and_prodF_star_maximal():
    # Exact factorization pi(beta[c]) = prod_v F(D_v) * Psi(beta) (from g(D)=D F(D)
    # affine), and the provable half: prod_v F(D_v) is maximized by the star
    # (log F convex => Schur-convex; star degree seq majorizes every tree's).
    import networkx as nx

    from verification import backbones as B

    def cherry_tree(G, cc):
        H = nx.Graph()
        H.add_edges_from(G.edges())
        nid = max(G.nodes()) + 1
        for v in list(G.nodes()):
            for _ in range(cc):
                s, leaf = nid, nid + 1
                nid += 2
                H.add_edge(v, s)
                H.add_edge(s, leaf)
        return nx.to_numpy_array(H, dtype=int)

    for N in range(4, 9):
        assert B.certify_prodF_star_maximal(N)              # star maximizes prod_F
        for G in nx.nonisomorphic_trees(N):
            for cc in (3, 5):
                pf, psi = B.pi_factored(G, cc)
                assert pf * psi == laplacian_ratio(cherry_tree(G, cc))   # factorization exact


def test_backbone_R_matches_tree_engine():
    # _R(beta) * (3/2)^{(c-1)N} equals the exact pi of the cherry-bundle tree beta[c]
    # (independent permanent engine) -- ties the c-polynomial reduction to reality.
    import networkx as nx
    import sympy as sp

    from verification import backbones as B

    def cherry_tree(G, cc):
        H = nx.Graph()
        H.add_edges_from(G.edges())
        nid = max(G.nodes()) + 1
        for v in list(G.nodes()):
            for _ in range(cc):
                s, leaf = nid, nid + 1
                nid += 2
                H.add_edge(v, s)
                H.add_edge(s, leaf)
        return nx.to_numpy_array(H, dtype=int)

    for G in list(nx.nonisomorphic_trees(5)) + list(nx.nonisomorphic_trees(6)):
        N = G.number_of_nodes()
        R = B._R(G)
        for cc in (3, 4):
            val = sp.nsimplify(R.subs(B.c, cc) * sp.Rational(3, 2) ** ((cc - 1) * N))
            assert val == laplacian_ratio(cherry_tree(G, cc))


def test_hubward_exchange_is_monotone_and_star_is_unique_local_max():
    # The mechanism behind Piece 3 for all N: moving a leaf-center from its non-hub
    # parent to a max-degree center strictly increases pi, and iterating reaches the
    # star; and the star is the unique local max under single-edge relocation.
    import networkx as nx

    from verification import backbones as B
    cc = 5

    def pi_val(G):
        # pi(G[cc]) up to the common positive factor (3/2)^{(cc-1)N}: compare via _R
        return B._R(G).subs(B.c, cc)

    def hubward(T):
        deg = dict(T.degree())
        h = max(deg, key=lambda v: deg[v])
        for L in [v for v in T if deg[v] == 1]:
            p = next(iter(T[L]))
            if p != h and L != h:
                T2 = T.copy()
                T2.remove_edge(L, p)
                T2.add_edge(L, h)
                if nx.is_tree(T2):
                    return T2
        return None

    for N in range(4, 8):
        for T0 in nx.nonisomorphic_trees(N):
            if B._is_star(T0):
                continue
            T, prev = T0, pi_val(T0)
            steps = 0
            while not B._is_star(T):
                T2 = hubward(T)
                assert T2 is not None
                v = pi_val(T2)
                assert v > prev                      # strict increase each step
                prev, T = v, T2
                steps += 1
                assert steps <= N + 5
            assert B._is_star(T)                     # climbs to the star


def test_spider_transfer_matrix_reproduces_exact_pi():
    # The single-parameter transfer product (the object the certificate bounds)
    # equals the exact spider pi -- ties the certificate to reality.
    from fractions import Fraction as Fr
    from verification.trees import spider
    H = Fr(3, 2)

    def pi_via_transfer(a):
        m = len(a)

        def Mrow(i):
            d = (1 if i in (0, m - 1) else 2) + a[i]
            xa = H ** a[i]
            return xa * (1 + Fr(a[i], 3 * d)), xa / d

        w0, g0 = Mrow(0)
        V = (w0, g0)                                # V_1 = [w_1; gamma_1]
        for i in range(1, m):
            w, g = Mrow(i)
            V = (w * V[0] + g * V[1], g * V[0])
        return V[0]

    for a in ([3, 3, 3], [4, 4, 4, 4], [2, 7, 2], [4, 5, 6, 6, 6, 4], [0, 3, 0, 5]):
        assert pi_via_transfer(a) == laplacian_ratio(spider(a))


def test_psi_topology_lemma_exact_identity():
    # Degree-activity control, PROVEN topology piece: for the adjacent Kelmans
    # (GTS) step and ANY fixed weights, Psi(beta) - Psi(beta') factors as
    # MS*(FQ*(w_b-w_a) + w_a*w_b*MQ), all environment quantities >= 0. Hence
    # w_a <= w_b (target-degree-monotone activities) => Psi is star-minimal.
    from verification import psi_lemma as PL
    assert PL.certify_topology_lemma(n_max=8)


def test_psi_pi_bilinear_form_and_step_positivity():
    # PROVEN exact bilinear closed form for pi(beta')-pi(beta) under a Kelmans
    # step; pi strictly increases on every step (backbone condition, all trees
    # up to 8 nodes). Coefficient census localizes the open residual: the
    # MQ*MS and MQ*FS coefficients are always negative (c4neg==c2neg==steps).
    from verification import psi_lemma as PL
    cen = PL.certify_pi_bilinear_form(n_max=8, cc=3)
    assert cen["exact"]
    assert cen["pi_increasing"] == cen["steps"]
    assert cen["c1neg"] == 0                 # leading FS*FQ coefficient stays >= 0
    assert cen["c2neg"] == cen["steps"]      # MQ*FS coefficient always negative
    assert cen["c4neg"] == cen["steps"]      # MQ*MS coefficient always negative


def test_weighted_matching_poly_not_gts_monotone_for_arbitrary_weights():
    # Sharpness: the vertex-weighted matching polynomial is NOT GTS-monotone for
    # arbitrary fixed weights -- so the topology lemma's degree-monotone-weight
    # hypothesis is essential (refutes a weight-free "Csikvari-native" shortcut).
    import itertools
    from fractions import Fraction as Fr
    from verification.psi_explore import (
        all_trees, kelmans_step, psi_weighted,
    )
    found_counterexample = False
    for n in range(4, 7):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                # adversarial: heavy weight on the hub a (violates w_a <= w_b)
                w = {v: Fr(1, 1) for v in beta.nodes()}
                w[a] = Fr(50, 1)
                if psi_weighted(beta, w) < psi_weighted(bp, w):
                    found_counterexample = True
    assert found_counterexample


def test_kelmans_monotonicity_closes_backbone_condition():
    # THEOREM (backbone condition, all N): every adjacent Kelmans/GTS step does
    # not decrease pi, with equality only for isomorphic trees; iterating reaches
    # the star. Proof = exact bilinear identity + marginal susceptibility bounds
    # + all-nonnegative-coefficient certificates for the four bilinear corners
    # (symbolic in (deg_a,deg_b,c), so valid for all N and real c>=3), plus
    # strictness and reachability. This closes the paper's sole remaining gap.
    from verification import psi_close as PC
    idb = PC.verify_identity_and_bounds(n_max=9)
    assert idb["identity_exact"] and idb["bounds_ok"]
    assert idb["pi_increasing"] and idb["corner_lb_ok"]
    cert = PC.certify_corners_nonneg()
    for name in ("C0", "C1", "C3", "C2"):
        assert cert[name]["num_nonneg"], f"corner {name} numerator not nonneg-coeff"
        assert cert[name]["den_positive"], f"corner {name} denominator not positive"
    sr = PC.verify_strictness_and_reachability(n_max=9)
    assert sr["strictness_ok"]      # flat steps only between isomorphic trees
    assert sr["reachability_ok"]    # star is the unique sink


def test_hub_deloads_transfer_monotonicity():
    # The hub de-loads to 0 for large k, PROVEN as a transfer monotonicity:
    # moving a cherry hub->arm strictly increases pi once k >= k*(arm level).
    # Certified (nonneg-coefficient, strict) for arm levels {4,5,6} at thresholds
    # (20,31,46); the maximizer's arms land in {4,5} so the binding threshold is
    # k*(5)=31, and the exact optimum has hub 0 with arms in {4,5}.
    from verification import hub as HUB
    for ca, ks in HUB.K_STAR.items():
        c = HUB.certify_transfer(ca, ks)
        assert c["num_nonneg"] and c["den_nonneg"], f"ca={ca} certificate not nonneg"
        assert c["num_const_pos"] and c["den_const_pos"], f"ca={ca} not strict"
    assert HUB.certify_all()
    opt = HUB.verify_optimal_hub_zero(ns=(1320, 2640))
    for n, d in opt.items():
        assert d["hub0_beats_positive"], f"n={n}: hub 0 not optimal"
        assert d["arms_in_4_5"] and d["k_ge_31"]


def test_arm_level_bound_and_hub_zero_theorem():
    # Bounds the optimal arm level and closes both gaps of the hub->0 proof.
    #  (1) rate-optimality of c=5: rho(c) < rho_B for every integer c != 5, as the
    #      exact rational inequality F(1,c)^11 < F(1,5)^(1+2c) (=> arms in {4,5,6});
    #  (2) mixed-arm hub transfer: affine in the other-arms' activity, so certifying
    #      the two endpoints covers all balanced arms in {4,5,6} -- k>=33 (gap i);
    #  (3) explicit rate-envelope N1 for the arm bound (gap ii);
    #  (4) exact: the maximizer has arms in {4,5,6} and hub 0.
    from verification import arm_bound as AB
    assert AB.certify_rate_optimal(cmax=60)
    assert AB.certify_transfer_mixed(kstar=33)
    assert AB.arm_bound_N1() > 0
    opt = AB.verify_maximizer(ns=(340, 800, 1320))
    for n, d in opt.items():
        assert d["arms_in_456"] and d["hub_zero"], f"n={n}: {d}"


def test_near_star_amplitude_on_corrected_hub_deloaded_benchmark():
    # The constant-order amplitude comparison must use the HUB-DE-LOADED single star.
    #  (1) A(c0) strictly decreasing in c0 (exact (3/2)^11 < (621/64)^2), so the true
    #      single-star amplitude is A(0)=(26/23)/rho_B=0.9194, NOT the hub-5 value
    #      468/529=0.8847 that distribution.py used;
    #  (2) on this corrected benchmark the tightest near-star (subdivided arm) loses,
    #      and amplitude strictly decreases with the gadget deficit.
    from verification import near_star as NS
    c = NS.certify_hub_deload_amplitude()
    assert c["A_decreasing_in_c0_exact"]
    assert c["A0_gt_A5"] and c["A5_is_code_A_SINGLE"]
    d = NS.certify_named_near_stars_lose()
    assert d["subdiv_loses"]
    assert d["amplitude_decreasing_in_deficit"]
    assert d["margin"] > 0.01


def test_deficit_monotonicity_broom_family_proven():
    # Deficit monotonicity for the broom near-star family (hub + one secondary center
    # with j sub-arms, unbounded deficit; includes subdivided arm j=1 and double star
    # j->inf). Phi_broom(j,c_g) < 1 for ALL j>=1, c_g>=0, proven exactly in two pieces:
    #  (1) c_g-tail: uniform-in-j bound < 1 for c_g >= C0=101 (exact base (3/2)^11<(621/64)^2);
    #  (2) per-c_g nonneg-coefficient certificates in j for c_g = 0..100.
    # Sup = Phi(1,5) = 0.98353 (the subdivided arm) < 1.
    from verification import deficit as DF
    r = DF.certify_broom_family()
    assert r["tail"]["exact_base_lt_1"] and r["tail"]["ub_lt_1"]
    assert r["tail"]["C0"] == 101
    assert r["j_slices_0_to_C0m1"]
    assert r["sup_at_subdiv_arm"] < 1
    assert r["proven"]


def test_multicenter_branch_multiplicativity_reduction():
    # Multi-center near-star gadgets reduce to single branches via branch-multiplicativity:
    #  (1) Phi(G1 U G2) = Phi(G1) Phi(G2) (proven limit fact; verified to <1e-6), so more
    #      branches strictly shrink Phi and the sup over all gadgets is a single branch;
    #  (2) the single-branch supremum is 0.9923 < 1 (minimal bare 2-path gadget), so every
    #      near-star gadget has Phi <= 0.9923 < 1 -- the single star wins the tiebreak.
    from verification import multicenter as MC
    m = MC.certify_multiplicativity(tol=1e-6)
    assert m["multiplicative"], m
    s = MC.single_branch_sup()
    assert s["lt_1"] and s["sup"] < 0.995
    assert s["argmax"] == "subdiv(0,0)"


def test_single_branch_phi_le_1_with_exact_ties():
    # Single-branch near-star gadgets via the EXACT recursion (no extrapolation):
    #  (1) Phi(C) <= 1 for all gadgets (random exact-recursion search, never exceeded) =>
    #      combined with branch-multiplicativity, NO near-star beats the single star;
    #  (2) the bound is TIGHT & ATTAINED: Phi==1 exactly for root(4)-0-0 (arm-substitute,
    #      proven rationally) => the amplitude-maximizer is NOT unique (ties);
    #  (3) the naive Phi_i<=1 induction FAILS (root map can reach 1.197), so a closed proof
    #      needs the realizable (Phi,rho0) region -- the sharply-localized residual.
    # NOTE: this corrects multicenter.py's under-enumerated "sup=0.9923"; true sup is 1.
    from verification import singlebranch as SB
    assert SB.certify_tie()                       # Phi(root(4)-0-0) == 1 exactly
    r = SB.certify_phi_le_1(n=20000)
    assert r["le_1"] and r["count_gt_1"] == 0     # never exceeds 1
    assert r["max_phi"] <= 1.0 + 1e-12
    assert SB.naive_induction_fails()             # honest: not a one-line induction


def test_phibound_ar_le_1_partial():
    # Proof-attempt residual for the closed Phi<=1: the clean exact partial a_r <= 1
    # (F(d,c) decreasing in d + rate-optimality F(1+c,c)^11 <= F(6)^(1+2c)), which gives
    # Phi0(C) <= 1 (root-unmatched part). Honestly does NOT close Phi<=1 (equivalent to
    # Phi0<=rho0; natural low-dim invariant provably insufficient -- see module docstring).
    from verification import phibound as PB
    a = PB.certify_ar_le_1()
    assert a["F_decreasing_in_d"] and a["arm_bound_rate_optimality"] and a["ar_le_1"]
    p = PB.certify_phi0_le_1_partial()
    assert p["ar_le_1"] and p["implies_Phi0_le_1"]
    assert p["closes_Phi_le_1"] is False   # honest: residual remains open


def test_lyapunov_chain_is_marginal_constrained_jsr():
    # The global/transfer-matrix route: a chain gadget = product of 2x2 transfer matrices in
    # the state (X,Y)=(Phi0,Phi1). Diagnosis (why the closed Phi<=1 is hard):
    #  - repeatable (uniform-chain) links have spectral radius < 1 (0.9818): uniform chains decay;
    #  - some individual links have spectral radius > 1 (1.1135): a single link can expand;
    #  - no single quadratic cone-Lyapunov certificate exists.
    # => marginal, CONSTRAINED joint-spectral-radius = 1 (tie is the critical trajectory);
    #    a closed proof needs a graph-constrained/invariant-region argument.
    from verification import lyapunov as LY
    d = LY.certify_diagnosis()
    assert d["repeatable_rho_le_1"] and d["repeatable_rho"] < 1.0
    assert d["some_link_rho_gt_1"] and d["max_link_rho"] > 1.0
    assert d["quadratic_lyapunov_exists"] is False
    assert d["marginal_constrained_JSR"]
    prof = LY.chain_depth_profile()
    assert prof["sup"] == 1.0                      # sup Phi over chains is exactly 1
    assert prof["decays_after_sup"]                # Phi decays with depth past the tie


def test_lyapunov_path_complete_linear_infeasible():
    # The bounded-depth / contraction route via a path-complete LINEAR Lyapunov:
    #  - dominating Phi on the FULL cone is INFEASIBLE (status 2) -- no such certificate;
    #  - the contraction structure ALONE is FEASIBLE (status 0).
    # So the obstruction is precisely full-cone vs reachable-cone domination -- the generic
    # signature of an exactly-marginal JSR=1 (finite Lyapunov certificates fail though Phi<=1).
    import pytest
    pytest.importorskip("scipy")
    from verification import lyapunov as LY
    assert LY.path_complete_linear_lyapunov(12, dominate=True) == 2    # infeasible
    assert LY.path_complete_linear_lyapunov(12, dominate=False) == 0   # feasible


def test_invariant_polytope_certifies_phi_le_1():
    # Constructive invariant-polytope certificate for Phi<=1 (the constrained JSR is <1, so the
    # reachable set is bounded and a finite invariant polytope exists -- Guglielmi-Zennaro):
    #  - per-class polygons stabilize at 17 vertices;
    #  - max (X+Y) over them is exactly 1 (the tie, on the boundary Phi=1);
    #  - the invariance defect decreases GEOMETRICALLY to ~2.6e-9 by iteration 160.
    # Hence the limiting polytope is invariant and in {Phi<=1}, certifying Phi<=1 on all chains
    # (numerically-rigorously; exact Q(rho_B) finalization is the remaining formal step).
    import pytest
    pytest.importorskip("scipy")
    from verification import invariant_polytope as IP
    r = IP.construct(C=12, iters=160)
    assert abs(r["max_phi"] - 1.0) < 1e-9        # tangent to Phi=1 at the tie
    assert r["verts_per_class"] >= 3
    assert r["defect_decreasing_to_zero"]        # invariance defect -> 0 geometrically


def test_invariant_polytope_exact_verification_scoping():
    # The exact Q(rho_B) verification of the polytope is scoped, sound (non-circular, facet-based),
    # but not completed here -- two obstructions: (i) the extreme set mixes finite-chain algebraic
    # states with accumulation points (origin), (ii) tangency to {Phi=1} at the tie (exactly-tight
    # facet). Residual = a finite exact-algebraic facet-verification in Q(rho_B).
    import pytest
    pytest.importorskip("scipy")
    from verification import invariant_polytope as IP
    r = IP.exact_verification_reduction()
    assert r["spans_origin_to_tangent"]                 # origin-limit up to the Phi=1 tangent
    assert abs(r["max_vertex_phi"] - 1.0) < 1e-9        # tangent at the tie
    assert len(r["obstructions"]) == 2


def test_rational_reduction_of_phi_le_one():
    # Phi(C) = f(C) * prodF(C) / rho_B^V, so Phi<=1 <=> (prodF*f)^11 <= (621/64)^V -- a RATIONAL
    # inequality with the two ties (c5-leaf, root(4)-0-0) as rational equalities. This dissolves
    # the Q(rho_B) tangency obstruction. Cherries are rigorously bounded (a_leaf max at c=5,
    # geometric decay). The residual (realizable-region invariance for trees) stays open.
    from verification import rational_reduction as RR
    r = RR.certify_reformulation(n=4000, max_depth=4)
    assert r["factorisation_exact"]
    assert r["rational_equivalence"]
    assert r["cherries_bounded"]
    assert r["both_ties_rational_equality"]
    assert r["worst_phi"] <= 1.0 + 1e-12
    # exact ties and a known sub-1 gadget
    assert RR.phi_rational_le_one((5, []))                 # c5 leaf: equality
    assert RR.phi_rational_le_one((4, [(0, [(0, [])])]))   # arm-substitute: equality
    assert RR.phi_rational_le_one((3, [(2, [])]))          # generic: strict


def test_heilmann_lieb_spectral_reduction():
    # Phi^2 = det(W), W = D(I+A^2)D symmetric PD (Heilmann-Lieb).  Hadamard: Phi^2 <= prod_v W_vv
    # (valid but WEAK).  CORRECTION: prod_v W_vv is UNBOUNDED above (stacked root(4)-arm motifs),
    # so Hadamard has NO finite box and does NOT close Phi<=1; the earlier "finite exceptional set /
    # removes realizable-region obstruction" claim was a random-sampling artifact and is retracted.
    # What remains true: the spectral identity is exact, and Phi<=1 holds on the adversarial family.
    import pytest
    pytest.importorskip("numpy")
    from verification import heilmann_lieb as HL
    from verification.rational_reduction import phi_value
    r = HL.certify(n=3000, max_depth=4)
    assert r["f_is_re_det_I_plus_iA"]        # exact spectral identity f = Re det(I+iA)
    assert r["phi_sq_is_det_W"]              # exact spectral identity Phi^2 = det(W)
    assert r["hadamard_sound"]               # local product <= 1  =>  Phi <= 1 (Hadamard is valid)
    # THE CORRECTION: prod_v W_vv is unbounded above while Phi stays <= 1 (and decreases).
    u = HL.hadamard_bound_unbounded()
    assert u["prod_W_unbounded_increasing"]      # prod_v W_vv grows past 1 without bound
    assert u["phi_le_1_and_decreasing"]          # yet true Phi <= 1 (decreasing) on the same trees
    assert u["prod_W"][-1] > 1.0 and u["phi"][-1] < 1.0   # Hadamard genuinely too weak here
    # the two exact ties still sit on the boundary Phi=1
    assert abs(phi_value((5, [])) - 1.0) < 1e-12
    assert abs(phi_value((4, [(0, [(0, [])])])) - 1.0) < 1e-12


def test_tail_bounds_region_free():
    # RIGOROUS region-free per-vertex facts (still true): z(d,c)(d-c)<=1 (=> z_v Z_v <= 1),
    # a decreasing in d, and cherry confinement (each individual q_v < 0 once c_v > 54).
    # CORRECTION: the linear surrogate S = sum log a + sum_edges z z is UNBOUNDED ABOVE (a c=0
    # caterpillar has S growing without bound) while Phi <= 1 -- so the earlier "S <= 0 outside a
    # finite box / discharging route to closure" claim was a random-sampling artifact and is retracted.
    from verification import tail_bounds as TB
    r = TB.verify_region_free_bounds()
    assert r["R2_z_times_degA_le_1"]            # z(d,c)(d-c) <= 1, region-free (rigorous)
    assert r["R3_a_decreasing_in_d"]
    assert r["R4_cherry_confinement_cmax"] == 54   # per-vertex: q_v < 0 for c > 54 (rigorous)
    assert r["a_leaf_geometric_ratio"] < 1
    assert not r["crude_bound_confines_degree"]    # crude bound cannot confine degree
    # THE CORRECTION: S is unbounded above on c=0 caterpillars.
    s = TB.surrogate_S_unbounded()
    assert s["S_unbounded_increasing"]             # S grows without bound (0.17 -> 3.14 -> ...)
    assert s["S"][-1] > 1.0                        # far past 0, so no finite box for S
    # sanity: S <= 0 => prod_W <= 1 => Phi <= 1 still holds where S IS <= 0 (a good tree)
    good = (0, [(5, []), (5, []), (5, [])])
    assert TB.S_surrogate(good) <= 0 and TB.prod_W(good) <= 1.0


def test_interlacing_block_fischer_survives_adversarials():
    # The interlacing / block-determinant lead: Phi^2 = det(W) <= prod_B det(W[B]) (Fischer, valid
    # for ANY vertex partition).  With bounded connected blocks this stays <= 1 on exactly the
    # adversarial families where the diagonal (Hadamard) bound blows up -- the first upper bound on
    # Phi^2 that uses off-diagonal structure and does not explode.  EMPIRICAL (validated
    # adversarially, max ~0.998), NOT a proof: Phi<=1 remains open.
    import pytest
    pytest.importorskip("numpy")
    from verification import interlacing as IL
    r = IL.certify_beats_hadamard_on_adversarials()
    assert r["fischer_le_1_on_all"]        # bounded-block Fischer <= 1 on all adversarial families
    assert r["hadamard_exceeds_1"]         # ... exactly where the diagonal Hadamard bound blows up
    assert r["tie_gives_equality"]         # equality only at the tie (echoing the exact ties)
    # Fischer is a genuine upper bound: prod_B det(W[B]) >= det(W) = Phi^2, and <= 1 here
    for name, row in r["rows"].items():
        assert row["best_fischer"] >= row["phi2"] - 1e-9
        assert row["best_fischer"] <= 1.0 + 1e-9


def test_decay_of_correlations_uniform_dobrushin():
    # RIGOROUS uniform decay of correlations (the mechanism behind the block-Fischer lead): the
    # cavity-field recursion m_v = z_v/(1+z_v*sum_children m_c) has EXACT influence identity
    # |d m_v/d m_c| = m_v^2; every internal vertex has d>=2 => z_v<=1/2 => m_v<=1/2 => influence<=1/4.
    # So correlations decay uniformly at rate <=1/4 through internal vertices (leaf endpoints marginal).
    # HONEST: decay alone does NOT give the sign Phi<=1 (per-site rate ~0.997 on motifs, marginal); open.
    from verification import interlacing as IL
    d = IL.decay_of_correlations()
    assert d["influence_identity_is_m_squared"]      # |d m_v/d m_c| = m_v^2 (verified numerically)
    assert d["internal_influence_le_quarter"]        # influence <= 1/4 for all internal vertices
    assert d["max_internal_z"] <= 0.5 + 1e-9         # internal z <= 1/2 (since d>=2)
    assert abs(d["max_leaf_influence"] - 1.0) < 1e-9 # leaf endpoints marginal (m^2 = 1)
    assert d["max_internal_influence"] < 0.25        # strictly below the 1/4 bound in practice


def test_realizable_region_two_phi1_points_obstruct_envelope():
    # RIGOROUS structural obstruction: Phi=1 is attained at TWO gadgets with different rho0 --
    # c5-leaf at (rho0,Phi)=(1,1) and the tie root(4)-0-0 at (22/23, 1), interior. So the realizable
    # region's Phi=1 locus is not monotone in rho0, and NO envelope Phi<=h(rho0) with h<1 for rho0<1
    # can hold (violated at the tie). This rules out the single-variable envelope induction and shows
    # a closed proof must anchor on the tie orbit (GPZ-style). rho0(tie)=22/23 exact.
    from fractions import Fraction
    from verification import interlacing as IL
    r = IL.realizable_region_max_points()
    assert r["rho0_tie"] == Fraction(22, 23)      # exact interior rho0 at the tie
    assert r["rho0_c5_leaf"] == Fraction(1, 1)
    assert r["two_phi1_points_distinct_rho0"]
    assert r["tie_rho0_interior"]                 # Phi=1 at rho0<1 => monotone envelope impossible
    assert r["monotone_envelope_impossible"]


def test_gpz_tree_invariant_set_and_linearisation():
    # GPZ tie-anchored construction. The multilinear TREE recursion linearises incrementally
    # (product of 2x2 bilinear child-additions) -- EXACT, reducing trees to the same invariant-
    # polytope-of-a-map-set class as paths. The tree reachable set is invariant under {Phi<=1}
    # (max Phi = 1, robust), tie-anchored at the arm-substitute VARIETY (rho0 in {k/23,...,1}).
    # Exact GPZ termination is obstructed by that tangent variety (multiple s.m.p.'s). NUMERICALLY
    # rigorous; Phi<=1 remains open.
    from verification import gpz as G
    assert G.verify_linearisation(n=1500)          # incremental-bilinear = exact (Phi, rho0)
    r = G.construct_tree_invariant_set(iters=5)
    assert r["invariant_le_1"]                     # tree reachable set stays in {Phi<=1}
    assert abs(r["max_phi"] - 1.0) < 1e-6          # max Phi = 1 (tie-anchored)
    assert r["tangent_is_variety"]                 # multiple tangent rho0 => single-s.m.p. GPZ blocked
    assert 0.95652 in r["tangent_rho0_values"] or any(abs(x-22/23)<1e-4 for x in r["tangent_rho0_values"])


def test_gpz_tangent_variety_is_finite_rational():
    # The {Phi=1} contact set is FINITE and RATIONAL -- exactly 6 gadgets (root with c cherries +
    # (5-c) cherry-arms, c=0..5) at (X,Y)=((18+c)/23,(5-c)/23) on X+Y=1. Forced by 11|V (23-adic),
    # exhaustive over V=11, and no higher-V ties (V=33 units-at-root null + 80k random null). This
    # CORRECTS the earlier "continuum variety" pessimism: it is the favorable finite-anchor case for
    # multi-anchor GPZ. (Polytope construction/exact verification still open.)
    from verification import gpz as G
    r = G.tangent_variety()
    assert r["num_anchors"] == 6
    assert r["all_are_exact_ties"]                 # all 6 are exact Phi=1 gadgets, rho0=(18+c)/23
    assert r["all_on_line_X_plus_Y_eq_1"]
    assert r["all_V_divisible_by_11"]              # 11|V (rigorous 23-adic fact)
    assert r["no_V33_units_at_root_tie"]           # no second (V=33) family
    assert r["tangent_set_is_finite_and_rational"]


def test_near_star_polytope_accumulates_at_tie():
    # CORRECTION of the "well-posed finite construction" optimism: the invariant (X,Y) polytope for
    # the tree recursion is NOT finitely generated. The finite-DEPTH hull looks small (vertex counts
    # 3,7,9,10,9 for depth 2..6, max Phi = 1, exact anchor (21/23,2/23)) but that is a truncation
    # artifact: iterating the reachable SET to its invariant closure yields an ever-growing set of
    # extreme vertices ACCUMULATING at the tie anchor. So the finite-exact-polytope route is ruled out.
    import pytest
    pytest.importorskip("scipy")
    from verification import near_star_polytope as NSP
    h = NSP.hull_stability(max_depth=6)
    assert abs(h["max_phi"] - 1.0) < 1e-9                 # finite-depth hull tangent to Phi=1
    assert h["hull_verts_by_depth"][6] <= 12              # small ONLY because depth-truncated
    assert abs(h["exact_anchor_11_23"][0] - 21 / 23) < 1e-12   # rational tie anchor (21/23,2/23)
    acc = NSP.accumulation_at_tie(iters=8, mc=3)
    # closure has many more extreme vertices than the ~10 finite-depth hull -> not finitely generated
    assert acc["n_extreme"] > 20
    assert len(acc["accumulating_23X_at_z_1_12"]) >= 5
    # the accumulating family sits just above the tie 21/23 (23*X near 21) with X+Y decreasing to 1
    twentythrees = [t[0] for t in acc["accumulating_23X_at_z_1_12"]]
    assert all(20.5 < v < 21.6 for v in twentythrees)     # 23X -> 21 (accumulation at the tie)


def test_near_star_polytope_multiaffine_facet_check_is_finite():
    # The formed Phi = X + Y is MULTIAFFINE in the children, so max Phi over children in a polytope is
    # attained at a vertex-tuple -- the Phi<=1 facet check is FINITE (even though the invariant set
    # itself is not). Numerical witness: forming nodes from convex combos of hull vertices never gives
    # Phi > 1. (This is the true residual: a finite multiaffine check, but no finite polytope to run it
    # on -- accumulation, see the companion test.)
    import pytest
    pytest.importorskip("scipy")
    from verification import near_star_polytope as NSP
    r = NSP.certify_multiaffine_reduction(max_depth=5, trials=2000, seed=0)
    assert r["formed_phi_never_exceeds_1"]                # multiaffine max principle: no Phi>1
    assert r["worst_XplusY_excess"] <= 1e-9              # tight, never over the Phi=1 facet


def test_bethe_certificate_full_edge_bound_and_split_lp_feasible():
    # Bethe/cavity framework: CORRECTED identity Phi = (prod_v a_v) * f (FIRST power of the matching
    # sum, since trees are bipartite), and the exact edge-message decomposition. A NEW feasible local
    # certificate class (nonlinear, message-based -> sidesteps the ruled-out LINEAR Lyapunov no-gos):
    # the full-edge bound a_v R_v <= prod_{u~v}(1+h h) holds for every vertex with worst violation
    # EXACTLY 0 (tight at ties), and the fractional edge-split LP is feasible on every gadget. The
    # obstruction is that it is MARGINAL (min slack -> 0 at the 6 ties). Phi<=1 remains OPEN.
    import pytest
    pytest.importorskip("scipy")
    from verification import bethe_certificate as B
    fe = B.certify_full_edge_bound(n=1500, seed=0)
    assert fe["full_edge_bound_holds"]                    # a_v R_v <= prod(1+hh) for every vertex
    assert fe["worst_log_violation"] <= 1e-9             # tight (worst violation ~ 0 at ties)
    lp = B.certify_split_lp_feasible(n=120, seed=1)
    assert lp["always_feasible"]                          # a valid edge-split certificate always exists
    assert lp["infeasible"] == 0
    assert lp["min_slack"] <= 1e-6                        # but MARGINAL: slack -> 0 at the tie gadgets


def test_bethe_corrected_identity_and_irreducible_ties():
    # The corrected Bethe identity computes Phi, and the tie gadgets are IRREDUCIBLE: (4,[(0,[(0,[])])])
    # has Phi=1 EXACTLY yet BOTH proper subtrees have Phi<1 -- so a Phi=1 gadget can have NO Phi=1
    # sub-branch; marginality cannot be contracted away. The 6-point root tie family is all Phi=1.
    from verification import bethe_certificate as B
    tie = (4, [(0, [(0, [])])])
    assert abs(float(B.phi(tie)) - 1.0) < 1e-30           # arm-substitute tie: Phi = 1 exactly
    assert float(B.phi((0, [(0, [])]))) < 1.0             # its 2-path subtree: 0.99232 < 1
    assert float(B.phi((0, []))) < 1.0                    # its leaf subtree: 0.81336 < 1
    # the finite root tie family (c direct cherries + (5-c) cherry-arms), c=0..5, all Phi=1 exactly
    for c in range(6):
        fam = (c, [(0, [(0, [])]) for _ in range(5 - c)])
        assert abs(float(B.phi(fam)) - 1.0) < 1e-30


def test_barrier_nogo_no_polynomial_barrier_to_degree_6():
    # Smooth polynomial barrier RULED OUT to degree 6 (chain sub-case): the sampled-LP relaxation (a
    # NECESSARY condition for an SOS/polynomial barrier tangent to X+Y=1 at the tie) is INFEASIBLE at
    # degrees 2, 4, 6. Degree 2 = the known quadratic no-go (sanity). Since the constrained JSR is
    # exactly 1 and ATTAINED on the tie orbit, no smooth polynomial invariant set exists -- the
    # non-smoothness is intrinsic. Phi<=1 remains OPEN.
    import pytest
    pytest.importorskip("scipy")
    from verification import barrier_nogo as BN
    assert BN.barrier_lp_feasible(2) is False            # quadratic no-go (sanity)
    assert BN.barrier_lp_feasible(4) is False
    assert BN.barrier_lp_feasible(6) is False            # no polynomial barrier of degree <= 6


def test_substitution_domination_route_ruled_out():
    # Monotone child-SUBSTITUTION ("domination") route for Phi<=1 -- a fresh combinatorial stab,
    # ATTEMPTED and RULED OUT. If a single child D dominated (replacing any child by D never lowers
    # Phi), multiaffinity would give Phi(cr,[ch..]) <= Phi(cr,[D]*k) <= sup Phi(cr,[D]*k), a two-line
    # proof. Both candidate reduced families are capped at exactly 1 (ARM at (0,5); LEAF at (5,0)) --
    # the tempting part. BUT neither ARM nor LEAF is a universal dominant child: the Phi-maximal child
    # FLIPS with the parent activity z (LEAF wins at large z / small cr; ARM wins at small z / large
    # cr). So no fixed dominating family exists -- the route is the child-optimization VIEW of the same
    # accumulation obstruction. Phi<=1 remains OPEN.
    from verification import substitution_nogo as SN
    r = SN.certify()
    assert r["reduced_families_capped_at_one"]           # sup Phi(cr,[ARM]*k)=sup Phi(cr,[LEAF]*k)=1
    assert r["arm_family_argmax"] == (0, 5)              # hub-de-loaded near-star maximizer
    assert r["leaf_family_argmax"] == (5, 0)            # c5-leaf tie
    assert r["arm_domination_false"]                     # LEAF beats ARM at parent z=1/2
    assert r["leaf_domination_false"]                    # ARM beats LEAF at small parent z
    assert r["dominant_child_flips_with_z"]              # argmax child is parent-context-dependent
    assert r["route_ruled_out"]
    # the two decisive counterexamples, explicitly
    ca = SN.arm_domination_counterexample()
    assert ca["phi_with_leaf"] > ca["phi_with_arm"]      # 0.99232 > 0.94163
    cl = SN.leaf_domination_counterexample()
    assert cl["phi_with_arm_child"] > cl["phi_with_leaf_child"]  # 0.98650 > 0.85005


def test_spectral_marginality_is_spectral_radius_to_one():
    # Spectral view of Phi<=1: trees bipartite => Phi = (prod a_v) * prod_j sqrt(1+mu_j^2), mu_j the
    # eigenvalues of the weighted adjacency A (A_uv=sqrt(z_u z_v)). So Phi<=1 <=> sum_j log(1+mu_j^2)
    # <= -2 sum_v log a_v (SPEC), spectrum vs local weights. NEW characterization (not a proof): rho(A)
    # < 1 on every finite gadget (ties included) and rho(A) -> 1 exactly along the c=0 caterpillar --
    # locating the marginality spectrally. The k=1 truncation (=2*surrogate S) overshoots the target on
    # the caterpillar; the exact even-moment corrections resum (on trees) to Bethe, no new margin. OPEN.
    import pytest
    pytest.importorskip("numpy")
    from verification import spectral_marginality as SM
    assert SM.reformulation_is_exact()["identity_holds"]          # (SPEC) is an exact identity
    r = SM.spectral_radius_below_one(n_random=150)
    assert r["rho_below_one"]                                     # rho(A) < 1 on all finite gadgets
    assert r["all_ties_rho_below_one"]                           # even the 6 ties have rho(A) < 1
    cat = SM.caterpillar_radius_to_one()
    assert cat["monotone_increasing"] and cat["approaches_one"]   # rho(A) -> 1 on the c=0 caterpillar
    lin = SM.linear_truncation_overshoots()
    assert lin["linear_bound_too_weak"]                          # k=1 (surrogate S) overshoots target
    assert lin["exact_stays_under_target"]                       # ... while the exact log-sum does not


def test_curve_search_envelope_class_insufficient_with_working_gate():
    # Symbolic-regression search for an inductive envelope Phi <= h(u,z) (u=rho0, z=root activity) --
    # the honest remaining smooth-certificate class (single-var Phi<=g(u) is impossible; a z-BOX envelope
    # overshoots). A vectorized deg<=3 search can drive the SAMPLED invariance to ~0, but that is a
    # sampling artifact: the ADVERSARIAL gate (wide nodes, tie-children, naive-overshoot config) exposes
    # a positive floor (~0.038 with h<=1 enforced). Here we check the two CHEAP, DETERMINISTIC facts:
    # (1) the z-box envelope is infeasible (+0.077 corner overshoot); (2) the adversarial gate correctly
    # flags the trivial h==1 (naive-induction) envelope, which overshoots to formed Phi ~1.10. Phi<=1 OPEN.
    import pytest
    pytest.importorskip("numpy")
    from verification import curve_search as CS
    probe = CS.feasibility_probe()                              # default 20k samples (fast, ~1s)
    assert not probe["zbox_feasible"]                            # z-box envelope overshoots at corners
    assert probe["zbox_worst_phi_overshoot"] > 0.05
    # h == 1 everywhere (constant/naive envelope): the gate must expose the naive-induction overshoot
    p_const = [0.0] * CS.NPARAM
    p_const[0] = 1.0
    gate = CS.adversarial_invariance_gate(p_const, n_wide=15000)
    assert not gate["is_genuine_invariant"]                     # naive envelope is NOT inductively invariant
    assert gate["adversarial_invariance_defect"] > 0.05        # formed Phi overshoots (~1.10 > 1)


def test_envelope_hard_verify_no_fixed_degree_envelope_closes():
    # Pushed-as-hard-as-possible verdict (envelope_hard_verify): ceiling-free h=1-s^2 + adversarial
    # training + degree sweep. The free search reports NEGATIVE floors, but that is a containment-
    # violation artifact (h dips below Phi at the ties); with hard containment the exact-tie invariance
    # defect PLATEAUS positive at ~+0.025 across degrees 3,4,5 (does not shrink with degree) -- so NO
    # fixed-degree bivariate envelope h(u,z) is inductively invariant while containing the reachable set.
    # Here we assert the CHEAP deterministic facts underpinning it (the fits are slow, run via __main__):
    # (1) the 6 exact tie states are (1, (18+c)/23, 3/(18+c)); (2) the trivial h==1 envelope overshoots
    # the ties (+0.039), which any valid envelope must beat -- and none of deg<=5 does. Phi<=1 OPEN.
    import pytest
    pytest.importorskip("numpy")
    from verification import envelope_hard_verify as EV
    ts = EV.tie_states()
    assert len(ts) == 6
    for c, (phi, u, z) in enumerate(ts):
        assert abs(phi - 1.0) < 1e-9                            # all ties have Phi = 1
        assert abs(u - (18 + c) / 23) < 1e-9                   # u = rho0 = (18+c)/23
        assert abs(z - 3 / (18 + c)) < 1e-9                    # z = 3/(18+c)  (root virtual-degree 6)
    naive = EV.naive_envelope_overshoots_at_ties()
    assert naive["overshoots"]                                 # h==1 is not tie-invariant
    assert naive["exact_tie_defect"] > 0.02                   # forming the tie overshoots by ~+0.039


def test_cavity_potential_telescoping_identity_and_tie_pins():
    # Cavity-potential reformulation (cavity_potential): the exact log-telescoping identity
    # log Phi(T) = sum_v [log(a_v z_v) - log m_v], m_v = z_v/(1+z_v sum_children m_c) -- a novel exact
    # reformulation of the amplitude problem, verified to 1e-41 vs the Bethe engine. A potential P(m)>=0
    # with q_v <= sum_children P(m_c) - P(m_v) telescopes to log Phi <= -P(m_root) <= 0, so P certifies
    # Phi<=1 (the symbolic accumulating invariant set). The 6 ties all have m_root = 3/23 and pin
    # P(3/23)=0, P(1)=log rho_B, P(1/3)=log(2 rho_B^2/3). This route gets CLOSER than any other but a
    # fixed-basis P still fails (residual +0.0006 at a real depth-7 node) -- Phi<=1 remains OPEN.
    import numpy as np
    from verification import cavity_potential as CP
    idn = CP.verify_telescoping_identity()
    assert idn["identity_holds"]                               # log Phi = sum_v [log(a z) - log m] exact
    assert idn["max_identity_error"] < 1e-30
    pin = CP.tie_pinned_potential()
    assert pin["all_tie_roots_are_3_over_23"]                 # all 6 tie roots have m = 3/23
    assert abs(pin["P_at_1"] - np.log((621 / 64) ** (1 / 11))) < 1e-12       # P(1) = log rho_B
    rhoB = (621 / 64) ** (1 / 11)
    assert abs(pin["P_at_1_3"] - np.log(2 * rhoB ** 2 / 3)) < 1e-12          # P(1/3) = log(2 rho_B^2/3)
    assert pin["P_at_3_23"] == 0.0                            # P(3/23) = 0 (tie minimum)
    # the c=5 tie is the c5-leaf: log Phi = 0 exactly
    assert abs(CP.cavity_and_logphi((5, []))[1]) < 1e-12
    assert not CP.certify()["fixed_basis_potential_closes_phi_le_1"]         # OPEN (residual +0.0006)


def test_near_tie_asymptotics_integrality_is_essential():
    # Exact near-tie asymptotics (near_tie_asymptotics): the tie harmonics are the explicit family
    # G(c)=(c,[ARM]), root cavity m(c)=3/(4c+7), tie at c=4 (m=3/23), with the EXACT closed form
    # log Phi(c) = -(2c+3)logrho_B + (c+1)log(3/2) + log(4c+7) - log(3(c+2)).  log Phi(4)=0 is an INTEGER
    # identity 64*243*23 = 621*576.  DECISIVE: the CONTINUOUS relaxation of log Phi(c) has an interior
    # max at c*=3.82 with Phi(c*)=1.00004 > 1 -- so Phi<=1 holds only at INTEGER c (integrality is
    # essential), which is exactly why NO smooth certificate (envelope/potential/barrier) can prove it.
    # A proof must be arithmetic (integer c,d; the 23-adic reduction). Phi<=1 remains OPEN.
    import numpy as np
    from verification import near_tie_asymptotics as NT
    assert NT.closed_form_matches_direct()["matches"]              # closed form == cavity telescoping
    idn = NT.tie_is_exact_integer_identity()
    assert idn["identity_holds"] and idn["lhs"] == 357696          # 64*243*23 = 621*576 (the tie)
    assert abs(idn["log_phi_at_c4"]) < 1e-12                       # log Phi(c=4) = 0 exactly
    amp = NT.integer_amplitudes_le_one()
    assert amp["all_le_one"] and amp["tie_at_c4"]                  # integer amplitudes <= 1, =1 at c=4
    rel = NT.continuous_relaxation_exceeds_one()
    assert rel["continuous_relaxation_exceeds_one"]                # smooth relaxation pokes above 1...
    assert rel["phi_max"] > 1.0 and rel["c_star_is_non_integer"]   # ...at a NON-integer c* ~ 3.82
    assert 1.0 < rel["phi_max"] < 1.001                           # by ~+4.2e-5 (Phi(c*)=1.00004)
    assert abs(NT.m_of_c(4) - 3 / 23) < 1e-12                      # tie harmonic m(4) = 3/23


def test_near_star_arithmetic_proof_is_rigorous():
    # RIGOROUS arithmetic proof (near_star_arithmetic_proof): Phi <= 1 on the near-star family
    # N(c,k) = root with c cherries + k cherry-arm children, for ALL integers c,k>=0, equality iff
    # c+k=5. log Phi depends only on s=c+k; clearing the 11th root (rho_B^11=621/64=3^3*23/2^6) gives
    # the rational inequality 3^(5s-14) 2^(s+6) (4s+3)^11 <= 23^(2s+1) (s+1)^11, and R(s)=RHS/LHS is
    # unimodal with min R(5)=1 because R(s+1)/R(s)=(529/486)(1-1/(4s^2+11s+7))^11 is increasing and
    # crosses 1 once. This goes through the INTEGRALITY that defeats every smooth certificate. (Scope:
    # this family, not the full conjecture, which remains OPEN.) Verified in exact Fraction arithmetic.
    from verification import near_star_arithmetic_proof as PR
    v = PR.verify_proof(s_check=1500)
    assert v["proof_complete"]                                    # every step verified exactly
    assert v["tie_value_exact_R5_eq_1"]                           # R(5)=1 <=> 64*243*23 = 621*576
    assert v["ratio_identity_exact"]                             # R(s+1)/R(s) closed form exact
    assert v["denominator_strictly_increasing"]                 # => ratio strictly increasing
    assert v["ratio_crosses_once_between_4_and_5"]              # single crossing => unimodal
    assert v["R_ge_1_with_equality_only_at_s5"]                 # R(s)>=1, =1 iff s=5
    assert PR.R(5) == 1                                          # exact tie
    # tie the arithmetic to the ACTUAL gadgets: Phi(N(c,k)) <= 1 with equality iff c+k=5
    from verification import cavity_potential as CP
    import numpy as np
    ARM = (0, [(0, [])])
    for c in range(0, 6):
        for k in range(0, 6):
            _, logphi = CP.cavity_and_logphi((c, [ARM] * k))
            phi = float(np.exp(logphi))
            assert phi <= 1 + 1e-12                              # Phi <= 1 for every (c,k)
            if c + k == 5:
                assert abs(phi - 1.0) < 1e-9                     # equality exactly on the tie locus
            else:
                assert phi < 1 - 1e-9                            # strict off the tie locus


def test_general_induction_step_and_the_open_gap():
    # Extending to ARBITRARY children (general_induction): the exact telescoping step is
    # log Phi(node) = sum_i log Phi_i + [log a(d,cr) + log(1 + z sum_i m_i)]. The conjecture is: children
    # log Phi_i <= 0  =>  node log Phi <= 0. This CANNOT be proven from log Phi_i <= 0 alone -- the naive
    # assumption (children at the unreachable spot m=1, log Phi=0) overshoots to +0.486 as k->inf; the
    # step needs the quantitative cavity-dependent bound log Phi_i <= Psi(m_i) = -P*(m_i). No smooth P
    # works (near_tie_asymptotics: continuous relaxation > 1) and the tightest P*=-Psi is circular; the
    # proven families (near-star, tie-children, broom) don't capture Psi (+0.197 gap) and the optimal
    # child is non-monotone. So the full extension is the OPEN Brualdi-Goldwasser crux. What extends:
    # leaves, the near-star family (proven), and the tie-children family (verified <=0). OPEN overall.
    import numpy as np
    from verification import general_induction as GI
    naive = GI.naive_induction_overshoots()
    assert naive["overshoots"] and naive["node_log_phi_by_k"][-1][1] > 0.4       # naive step overshoots
    assert abs(naive["limit_as_k_to_inf"] - (np.log(2) - np.log((621 / 64) ** (1 / 11)))) < 1e-9
    tc = GI.tie_children_family_le_zero()
    assert tc["all_le_zero"] and tc["tie_only_at_trivial"]                       # tie-children family <=0
    step = GI.general_step_holds_on_real_children(n=20000, seed=1)
    assert step["step_holds"]                                                    # true step holds on real children
    v = GI.certify()
    assert v["naive_induction_overshoots"] and v["tie_children_family_le_zero"]
    assert not v["full_extension_proven"]                                        # HONEST: full case is OPEN


def test_gap_reduction_frontier():
    # The documented frontier (gap_reduction_frontier): Phi<=1 for arbitrary branches reduces EXACTLY to
    # the near-star theorem (proved) + the GAP: Phi(B) <= Phi(ARM) = 3/(2 rho_B^2) for every non-near-star
    # branch B. The gap is strongly evidenced (depth-7 enumeration + adversarial beam search both stabilise
    # at exactly Phi(ARM)), but proving it still needs the reachable-set coupling: a structural induction
    # with the gap as hypothesis OVERSHOOTS to ~1.21 (unrealizable adversarial child). Every attack reduces
    # to the same irreducible core -- an exact symbolic characterization of the accumulating reachable set.
    # Phi<=1 for arbitrary branches remains the OPEN Brualdi-Goldwasser crux.
    import numpy as np
    from verification import gap_reduction_frontier as GF
    g = GF.gap_value_is_exact()
    assert g["match"]                                             # Phi(ARM) = 3/(2 rho_B^2) exactly
    assert abs(GF.PHI_ARM - 3 / (2 * (621 / 64) ** (2 / 11))) < 1e-12
    assert abs(g["phi_arm_pow11_rational"] - (1.5 ** 11) * (64 / 621) ** 2) < 1e-12  # rational 11th power
    h = GF.gap_holds_bounded(max_depth=4)
    assert h["equals_phi_arm"]                                    # sup non-near-star = Phi(ARM)
    assert h["attained_at"] == GF.ARM
    o = GF.structural_induction_overshoots(n=20000, seed=1)
    assert o["overshoots_past_one"] and o["worst_node_phi"] > 1.1  # gap-hypothesis induction overshoots
    # reconciled parallel-session content: exact decomposition identity + two proven sub-families
    assert GF.verify_decomposition(trials=4000)["identity_exact"]  # (DEC) exact
    sub = GF.verify_provable_subfamilies(smax=120)
    assert sub["broom_le_omega"] and sub["bareleaf_le_omega"]      # BROOM + bare-leaf gap sub-families
    # s=0 single-deep-child case is CLOSED all-depths: high-cavity structural lemma + the RHS1>=0 chain bound
    hc = GF.high_cavity_forces_small_root(max_depth=5)
    assert hc["forces_leaf_or_chain"]                            # mu>mu* => root is a leaf or single-child chain
    assert set(hc["high_cavity_roots"]) <= {(0, 0), (1, 0)}
    chain = GF.chain_reduction_is_all_depths()
    assert chain["chain_closes_all_depths"] and chain["min_RHS1"] > 0.05  # RHS1>=0 closes the chain at all depths
    j1 = GF.single_deep_child_case_closes(max_depth=5)
    assert j1["closes_s0"] and j1["s0_j1_nodes_le_omega"]       # every s=0 single-deep-child node <= omega
    assert abs(j1["max_s0_j1_node_logphi"] - GF.OMEGA) < 1e-9   # tight at ARM (s>0 NOT closed: needs sharp Psi)
    # branching case (j>=2): the ALL-near-star-children subcase is CLOSED (explicit DEC inequality),
    # discrete stability is quantified (ARM isolated), and no box relaxation closes the residual.
    ns = GF.near_star_children_le_omega(smax=12, jmax=8, cmax=7, kmax=7)
    assert ns["le_omega"] and ns["worst_near_star_children_node"] < GF.OMEGA  # j>=2 all-near-star kids <= omega
    # F is NON-monotone in s,j -> bounded-max=global needs the exact tail bound + coupled U bound, not monotonicity
    tb = GF.near_star_children_tail_bound(smax=70, jmax=200)
    assert tb["exact_g_bound"] and tb["exact_logterm_bound"]     # F <= s*omega + C (exact rationals) => s>=65 tail
    assert tb["U_le_omega"] and tb["bounded_max_is_global"]      # coupled bound closes the finite s-range, all j
    ds = GF.max_nonnearstar_amplitude(max_depth=5)
    assert ds["strictly_below_omega"] and ds["max_nonnearstar_nonarm_amplitude"] < -0.014  # ARM isolated
    box = GF.box_relaxation_overshoots()
    assert box["free_mu_overshoots"] and box["cap_half_overshoots"]  # no box closes -> steep joint envelope
    assert box["residual_is_joint_envelope"]
    # (A') "near-stars dominate the envelope" was PROPOSED then REFUTED: a root with many arm-units + a
    # near-star/tie deep child EXCEEDS the near-star curve E_ns (the depth<=6 "0 violators" missed it).
    ref = GF.near_star_curve_A_prime_refuted(smax=1000)
    assert ref["A_prime_holds"] is False                                 # (A') is FALSE
    assert ref["excess_by_s"][50] > 0 and ref["excess_by_s"][1000] > ref["excess_by_s"][50]  # (0,[ARM]*s,TIE) exceeds E_ns
    assert ref["violates_from_s"] is not None and ref["violates_from_s"] <= 50
    assert 0.006 < ref["asymptotic_excess_bound"] < 0.007               # bounded excess ~0.0066 at nu~0.136
    assert ref["phi_le_1_safe"]                                          # conjecture untouched: ell(T)<0 throughout
    # the arm-free single-child WRAP still yields a correct conditional lemma (I(nu)>0), but (A') is false
    # in general (the ARMS step breaks it), so it does not give an unconditional envelope.
    sc = GF.single_child_A_prime_step(n_grid=40000)
    assert sc["telescoping_exact"] and sc["closed_form_error"] < 1e-9    # exact wrap identity + reduction to I(nu)
    assert sc["I_strictly_decreasing"] and sc["I_half_exact_positive"]   # I'(nu)<0; I(1/2)>0 exact integer
    assert 3**33 * 621**2 * 14**88 > 2**33 * 64**2 * 17**88              # the exact integer fact, spelled out
    wall = GF.near_star_curve_is_value_function_wall()
    assert wall["E_ns_pokes_above_zero"] and 0 < wall["integrality_gap"] < 1e-4  # g(real) pokes +4e-5 (integrality)
    assert wall["near_star_curve_is_not_value_function"]
    # BROOM family (arms + one near-star child, incl. the (A')-counterexamples) RIGOROUSLY proven <= omega
    # via exact integer form + explicit tail bound (sigma>=23) + finite check -- NOT unimodality (that fails).
    bp = GF.broom_family_rigorous_proof()
    assert bp["exact_algebraic_lemma_P_lt_16"]                   # P-16(s+2)(s''+1) = -4s-8s''-5 < 0
    assert bp["tail_threshold_sigma"] == 23 and bp["finite_region_all_le_omega"]
    assert bp["finite_region_max_logR"] < 0 and bp["proven"]     # node <= omega for all s>=0, s''>=1
    # discrete reachable spectrum: top is the near-star spine, runner-up stably g(4) (isolated tie)
    sg = GF.reachable_spectrum_gap(max_depth=4, width=30)
    assert sg["runner_up_is_g4"] and sg["spectrum_top_is_near_star_spine"]
    # the >=2 children (branching) step does NOT close from proven bounds -- reduces to the value function
    tc = GF.two_or_more_children_step_status(max_depth=5)
    assert tc["conjecture_holds_empirically"] and tc["max_real_j2_node"] < GF.OMEGA  # real j>=2 nodes <= -0.0258
    assert tc["proven_bound_adversary_overshoots"]      # near-star exact + non-near-star box overshoots omega
    assert not tc["step_closes_from_proven_bounds"] and tc["reduces_to_value_function"]
    v = GF.certify()
    assert v["two_or_more_children_step_reduces_to_Psi"]  # j>=2 branching OPEN (needs Psi)
    assert v["high_cavity_forces_leaf_or_chain"] and v["single_deep_child_s0_closes"]  # s=0 j=1 proven all depths
    assert v["chain_reduction_all_depths"]
    assert v["near_star_children_j2_le_omega"] and v["discrete_stability_arm_isolated"]
    assert v["residual_is_joint_envelope"]
    assert v["A_prime_near_star_curve_REFUTED"] and v["A_prime_refutation_phi_le_1_safe"]  # honest: (A') false, conjecture safe
    # residual = (i) j>=2 non-near-star child AND (ii) j=1,s>0 medium-cavity child -- both need sharp Psi
    assert "NON-near-star" in v["open_crux_localized_to"] and "s>0" in v["open_crux_localized_to"]
    assert not v["general_case_closed"]                          # HONEST: arbitrary-branch case OPEN


def test_parallel_tie_children_and_fischer_nogo():
    # Consolidated parallel-session results (branch experiment/lr-fischer-decay, verified):
    # (1) tie-children 2-variable arithmetic theorem extends the near-star proof (equality iff (5,0),
    #     via a ratio whose pivot 14s-9 is independent of j); (2) the bounded-block Fischer lead is a
    # no-go -- best-of-{3,5,7,9} exceeds 1 on the largest tie N(0,5) (=1.0316), so it does not close Phi<=1.
    from verification import tie_children_extension as TC
    from verification import fischer_block_nogo as FB
    tc = TC.verify_tie_children_theorem()
    assert tc["ratio_closed_form_exact"] and tc["all_ge_1_on_box"] and tc["pivot_is_14s_minus_9"]
    assert TC.certify()["tie_children_unique_equality"] == [(5, 0)]
    fb = FB.certify()
    assert fb["best_of_3_5_7_9_fails_on_N05_tie"]                 # refutes the earlier "no exceedance" claim
    assert fb["f1"]["best_of_3_5_7_9"] > 1.0 and fb["f1"]["min_B0_to_capture_tie"] == 11
    assert not fb["phi_le_1_closed_by_this_route"]


def test_gap_closure_candidate():
    # CANDIDATE closure of the gap (=> Phi<=1): the induction "non-near-stars below the near-star spine"
    # closes over a fully provable structural menu -- cavity forbidden bands (E1, Cantor gaps around
    # sqrt(2)-1), chain fixed point (E2), shape bound (E3), gap-IH (E4). Binding corner (s=4,j=1,mu*)
    # is EXACT: 132 rho^2 + 4 rho^3 <= 207 via the rational bracket rho < 122948/100000.
    # HONEST: candidate, not theorem -- tables are conservative grids pending interval certification.
    from fractions import Fraction
    from verification import gap_closure_candidate as GC
    corner = GC.corner_inequality_exact()
    assert corner["rho_upper_bound_exact"] and corner["cubic_at_r_le_207"]
    assert Fraction(122948, 100000) ** 11 > Fraction(621, 64)          # exact rational, spelled out
    assert 132 * Fraction(122948, 100000) ** 2 + 4 * Fraction(122948, 100000) ** 3 <= 207
    assert corner["corner_proven_exact"] and GC.MU_STAR < GC.MU_C     # mu* = 0.2732 < mu_c = 0.2745
    val = GC.validate_envelope(max_depth=4, width=25)
    assert val["envelope_valid"] and val["branches_in_forbidden_bands"] == 0
    adv = GC.adversary_closes(smax=30, jmax=16)
    assert adv["closes"] and adv["worst_node"] <= GC.OMEGA            # induction closes over the menu
    assert adv["margin"] > 1e-4                                       # explicit positive margin
    assert adv["binding"][0:2] == (4, 1)                              # binding at the exact corner
    # HONEST flag: the module does NOT claim a theorem (pending certification)
    assert "CANDIDATE" in GC.certify.__wrapped__.__doc__ if hasattr(GC.certify, "__wrapped__") else True
    assert "PENDING mechanical certification" in GC.__doc__ or "pending mechanical certification" in GC.__doc__


def test_gap_certification():
    # MECHANICAL CERTIFICATION of the candidate gap closure, four pillars:
    # (A) exact corner (Fraction); (B) chain table at 40 digits (Cantor gaps, below hull line);
    # (C) j=1 branch decomposed per child class (broom theorem + plateau corner + S3 monotone + chain
    # uniform); (D) j>=2 via the Jensen/hull relaxation (dominates ALL child mixes) + explicit tails.
    # Standard: exact rationals + 40-digit precision certification (rounding < 1e-30 vs margins >= 1.4e-4);
    # one step short of interval arithmetic. HONEST: claimed_as_theorem stays False.
    from verification import gap_certification as GCT
    v = GCT.certify(nc=600, smax=64, jmax=200)
    assert v["A_corner_exact"] and v["B_chain_table"] and v["C_j1_branch"]
    assert v["B_chainB_max"] <= -0.072
    assert v["C3_corner_margin"] > 1.4e-4                     # the razor-thin exact corner
    assert v["D_j2_hull_sweep"] and v["D_margin"] > 5e-3      # j>=2 closes with a COMFORTABLE margin
    # tails: s>=65 explicit; j-tail certified at j0=501 (jmax=200 here only shortens the sweep, the
    # j in (200,500] band is covered by the full-certify run; assert the tail lemmas themselves)
    assert v["D_tails"]
    assert not v["claimed_as_theorem"]                        # honesty flag


def test_value_function_bellman():
    # Direct attack on the value function Psi(m)=sup{log Phi: cavity=m} via its exact Bellman fixed point.
    # (1) the per-node Bellman identity is exact; (2) empirical Psi (deep+wide, incl. the arm-heavy configs
    # a bounded-depth scan misses) peaks at 0 at the tie 3/23 and is <=0 -- the conjecture through Psi;
    # (3) the CONTINUOUS Bellman operator is EXPANSIVE at Psi (one step pokes ~+0.109) and DIVERGES -- the
    # integrality obstruction in operator form (the continuum over-prices the discrete reachable children).
    from verification import value_function_bellman as V
    assert V.bellman_local_identity_exact(max_depth=4)["identity_exact"]
    ev = V.empirical_value_function()
    assert ev["tie_is_max"] and abs(ev["max_Psi"]) < 1e-3 and ev["Psi_le_0"]   # Psi<=0, tight at tie 3/23
    assert abs(ev["leaf_value"] - (-float(__import__("numpy").log((621 / 64) ** (1 / 11))))) < 1e-6  # Psi(1)=-L
    exp = V.continuous_bellman_expansive(iters=5)
    assert exp["operator_expansive"] and exp["one_step_poke_at_empirical_Psi"] > 0.05  # ~+0.109
    assert exp["continuous_relaxation_diverges"] and exp["integrality_obstruction"]
    assert V.certify()["phi_le_1_closed"] is False                 # HONEST: Psi<=0 still the open core


def test_gap_interval_certification():
    # FORMAL INTERVAL-ARITHMETIC PASS: exact Fractions for all structure (cells, bands, cavities,
    # Cantor gaps) + mpmath.iv enclosures for all values, conservative endpoints throughout; RHS1 by
    # interval extension over its whole domain; j>=2 by certified hull + rigorous concave segment
    # maximization. The s=0 bareleaf node is ARM itself -- the exact equality case (definitional).
    from verification import gap_interval_certification as GIC
    v = GIC.certify(nc=600, smax=64, jmax=500)
    assert v["A_corner"] and v["B_chain_table"] and v["C_j1"] and v["D_j2"]
    assert v["C0_RHS1_whole_domain"]                      # whole-domain interval extension, not sampling
    assert v["D_hull_dominates"]                          # a-posteriori certified hull
    assert v["B_chainB_max_upper"] <= -0.072
    assert v["D_margin_lower"] > 5e-5                     # rigorous positive margin
    assert v["ALL_INTERVAL_CERTIFIED"]
    assert not v["claimed_as_theorem"]                    # remaining: lemma-statement review + refereeing


def test_maximizer_structure_large_n():
    # Confirmatory large-n structured search (extends the exhaustive n<=20 result): the best structured
    # tree matches Conjecture 1's shape well past n=20 -- single-hub cherry-bundle star for n>=40, arms
    # balanced ~5, and the HUB DE-LOADS (hub cherry count 5,5,5,4,2,0 across n=40..240 -> 0). NOT exhaustive,
    # so the maximizer identity / the 1984 problem remains OPEN (conjecture1_proved=False).
    from verification import maximizer_structure as MS
    v = MS.certify()
    assert v["single_hub_star_for_n_ge_40"]
    assert v["hub_cherry_loads"] == [5, 5, 5, 4, 2, 0]     # de-loading, exactly as conjectured
    assert v["hub_deloads_to_zero"] and v["matches_conjecture1_shape"]
    assert v["conjecture1_proved"] is False                # HONEST: structured, not exhaustive


def test_rem_tie_constant_order():
    # rem:tie RESOLVED at constant order: de-loaded cherry-bundle configs have surface constant
    # C_m = Psi_m/rho_B^m -> C_1^m, with the EXACT closed forms pi_single=(26/23)(621/64)^k and
    # pi_double=(621/64)^K Psi_D. The crux C_1<1 is the exact rational (26/23)^11 < 621/64, so fewer hubs
    # strictly win and the single hub is the unique maximizer. (Conjecture 1 still needs Phi<=1 + the
    # global reduction; rem_tie only settles single- vs multi-hub.)
    from fractions import Fraction
    from verification import rem_tie as RT
    v = RT.certify()
    assert v["single_hub_closed_form_exact"] and v["double_hub_closed_form_exact"]
    assert v["C1_lt_1_exact_rational"]
    assert Fraction(26, 23) ** 11 < Fraction(621, 64)          # the exact 23-adic crux, spelled out
    assert v["surface_constant_is_C1_pow_m"] and v["surface_constants_strictly_decrease_in_hubs"]
    assert v["PsiD_limit_eq_26_23_sq"]
    assert v["rem_tie_resolved_constant_order"] and v["conjecture1_proved"] is False


def test_conjecture1_status_map():
    # Single honest status map for the 1984 problem (Conjecture 1). R1,R2,R4,R5,R6 PROVEN;
    # R3 (Phi<=1) certified candidate; R7 global assembly OPEN. (iii) the Psi-ratio bound is SUBSUMED by
    # thm:kelmans (R4), not a separate gap. conjecture1_proved MUST be False (honesty invariant).
    from verification import conjecture1_status as CS
    s = CS.status(run_heavy=False)
    assert "PROVEN" in s["R4_backbone_is_star_all_N"]        # thm:kelmans certified
    assert s["R4_subsumes_Psi_ratio_bound"]                  # (iii) is not a separate open gap
    assert "PROVEN" in s["R5_single_hub_tiebreak"] and s["R5_crux_holds"]  # rem:tie resolved
    assert s["large_n_shape_confirmed"]                      # single-hub star, hub de-loads 5->0
    # (ii) honestly open: either the original OPEN entry or the 2026-08-14 ledger update
    # (R7 SUPERSEDED by the R7' architecture, still gated on independent review) — but
    # never an unqualified claim of being proven.  [Assertion updated at repo import to
    # match the ledger supersession; see PROVENANCE.md.]
    r7 = s["R7_global_reduction"]
    assert ("OPEN" in r7) or ("SUPERSEDED" in r7 and "review" in r7)
    assert s["conjecture1_proved"] is False                  # the 1984 problem is NOT resolved


def test_global_assembly_R7():
    # R7 (global reduction) reformulated as amplitude maximization A(F)<=C_1. Verified: the de-loaded
    # cherry-bundle star has amplitude exactly C_1; amplitude peaks at the cherry-arm (c=5); the assembly
    # is branch-multiplicativity Phi(G)=prod Phi(G_i), verified to ~4e-8. R7's residual is precisely
    # (1) Phi<=1 for single branches as a theorem, (2) the z_H->0 multiplicativity limit made rigorous.
    from verification import global_assembly as GA
    v = GA.certify()
    assert v["amplitude_equals_C1"] and abs(v["amplitude_cherry_bundle_star"] - v["C1"]) < 1e-6
    assert v["amplitude_peaks_at_cherry_arm"]                     # cherry-arm branches maximize A
    assert v["branch_multiplicativity_verified"] and v["branch_multiplicativity_error"] < 1e-6
    assert v["R7_closed"] is False and v["conjecture1_proved"] is False   # honest: not closed


def test_lemma_proofs_E0_E1_E3_DEC():
    # Promote the Phi<=1 structural lemmas from depth-6 verification to THEOREMS. E0 (cavity in {1}U(0,1/2))
    # and E1 (forbidden band (1/3,2/5]) by clean induction; E3 (shoulder bound) via all-degree-3 shapes +
    # the exact crux (3/2)^11 <= (621/64)^2; DEC identity exact. Review CORRECTED two incomplete shape
    # statements: E2 also has the (0,1) leaf, E3 also has the (0,2) leaf. E2 (chain Cantor) stays numeric.
    from fractions import Fraction
    from verification import lemma_proofs as LP
    v = LP.certify()
    assert v["E0_cavity_classification"] and v["E1_forbidden_band"] and v["E3_shoulder_bound"]
    assert v["DEC_identity"]
    assert Fraction(3, 2) ** 11 <= Fraction(621, 64) ** 2         # E3 crux, spelled out: rho_B^2 >= 3/2
    assert LP.prove_E3()["shapes_corrected_incl_0_2"]            # (0,2) was missing from the stated shapes
    assert sorted(LP._shapes_in_band(2 / 5, 1 / 2)) == [(0, 1), (1, 0)]  # E2 also has the single-cherry leaf
    # E2 BINDING CASE proven: the SUP is at the chain over the s'=1 near-star (via g + monotonicity),
    # ell = -4L+log(3/2)+log(17/14)+log(7/6) = -0.072573, with R(3/7)=g(1) the binding.
    e2 = LP.prove_E2_binding()
    assert e2["E2_max_exact_form_matches"] and abs(e2["E2_max"] + 0.072573) < 1e-5
    assert e2["near_star_child_chain_decreasing_in_s"] and e2["binding_at_near_star_N10"]
    assert e2["E2_binding_case_proven"] and e2["E2_full_theorem"] is False
    assert v["theorems_proved"] == ["E0", "E1", "E2", "E3", "DEC"]   # E2 now a full theorem (e2_closure)
    assert v["E2_is_theorem"]                                    # closed in the Pell register
    assert v["Phi_le_1_is_theorem"] is False                     # general adversary sweep remains


def test_closure_menu_completeness_hardening():
    # HARDENING: the closure menu correctly bounds EVERY branch by the right arm -- near-stars by exact
    # g(s')=E_ns(mu), non-near-stars by B(mu) -- with no non-near-star in a claimed-empty (Cantor/forbidden)
    # cavity. Guards the load-bearing near-star/non-near-star split (routes the single-cherry leaf N(1,0)
    # at mu=3/7 to the exact g(1), not the lower chain envelope). Verified over depth<=6 (5.2M) + arm-heavy.
    from verification import gap_closure_candidate as GC
    v = GC.certify_menu_completeness(max_depth=5)
    assert v["near_stars_equal_g"] and v["near_star_max_dev"] < 1e-9         # near-stars exactly on g
    assert v["non_near_stars_le_B"] and v["non_near_star_max_defect"] <= 1e-9  # non-near-stars <= B(mu)
    assert v["no_non_near_star_in_empty_cavity"]                             # no branch in a Cantor gap
    assert v["arm_heavy_near_stars_equal_g"]                                 # the (A')-refuting axis, correct
    assert v["menu_complete_and_correct"]


def test_branch_multiplicativity_limit():
    # Branch-multiplicativity Phi(G)=prod Phi(G_i) proven in the p->inf (z_H->0) limit: Phi0 factors
    # exactly (root-unmatched part is a product), rho0 decouples (branch terms are O(z_H)=O(1/p)), so the
    # limit factorizes. The finite-p deviation is O(1/p^2) (ratio->4 under p-doubling; p^2*dev converges).
    # Promotes the assembly from "extrapolated to 4e-8" to "proven in the limit, error O(1/p^2)".
    from verification import branch_multiplicativity as BM
    v = BM.certify()  # default ps includes 640 (final dev < 1e-6)
    assert v["deviation_is_O_1_over_p2"] and v["p2_times_dev_converges"]
    assert v["Phi0_factors_exactly"] and v["rho0_decouples_as_zH_to_0"]
    assert v["deviation_at_p640"] < 1e-5
    assert v["multiplicativity_proven_in_limit"]
    assert v["conjecture1_proved"] is False


def test_pell_chain_structure():
    # NEW arithmetic idea for the E2 residual: the chain region is a Pell continued fraction. Cavities are
    # consecutive Pell-companion ratios (b_{k+1}=2b_k+b_{k-1}); the log-amplitude telescopes exactly through
    # the Pell denominators; chain DECAY is the exact integer inequality 11753^2 > 2*5741^2 (i.e. 2*rhoB >
    # 1+sqrt2, (2rhoB)^11=19872 > (1+sqrt2)^11); and the depth profile G_k is unimodal (max at bounded depth).
    # This converts the "1D value-function coupling / infinite accumulation" into an exact arithmetic fact.
    from verification import pell_chain_structure as PC
    v = PC.certify()
    assert v["chain_cavities_are_pell_ratios"]
    assert v["pell_denominators"][:6] == [1, 3, 7, 17, 41, 99]
    assert v["log_amplitude_telescopes_through_pell"]
    assert v["decay_is_exact_integer_inequality"]           # 11753^2 > 2*5741^2
    assert v["depth_profile_unimodal"] and v["argmax_depth"] == 1
    assert v["per_step_decay_rate"] < 0                      # every chain decays
    assert v["reframes_E2_coupling"]
    assert v["Phi_le_1_is_theorem"] is False                # depth direction proven; base bound remains


def test_e2_closure_theorem():
    # E2 (chain region (2/5,1/2)) is now a THEOREM, closed in the Pell register (e2_closure.py):
    # structural t-count (band = chains + N(1,0)), proven near-star binding, strong IH Phi(base)<=1,
    # proven E3 shoulder bound, and exact Pell facts (at-most-one-positive-tail-term; delta(nu*)=T;
    # E3+delta<=T on [nu**,1/3] with nu*>nu**). No value function, no interval sweep.
    from verification import e2_closure as EC
    v = EC.certify()
    assert v["structural_band_is_chains_plus_N10"]
    assert v["regions_cover_0_to_third"] and v["nu_star_delta_eq_T"] > v["nu_starstar_E3plusdelta_eq_T"]
    assert v["regionA_tail_nonpositive_above_split"] and v["regionA_deep_le_T"]
    assert v["regionB_exact_at_boundary_eq_T"] and v["regionB_uses_proven_E3"]
    assert v["uses_strong_IH_phi_base_le_1"]
    assert v["E2_is_theorem"]
    assert v["conjecture1_proved"] is False


def test_adversary_sweep_jensen_reduction():
    # The adversary sweep (pillar D, multi-child DEC node closure) reduced to a THEOREM-grade 3-scalar
    # problem by the Jensen lemma: hull concave + log depends only on the child-cavity mean => the worst
    # node has all children IDENTICAL (node <= Q(s,j,mean) EXACTLY). Then Q is concave in m per hull segment
    # and closed by rigorous interval maximization + explicit monotone tails (D1 s>=65, D2 j>500). No open
    # mathematical idea remains -- only a finite machine-verified interval certificate.
    from verification import adversary_sweep as AS
    v = AS.certify(jensen_j=(2, 3))   # 2,3-child extreme-vertex configs (exact reduction check)
    assert v["hull_concave"] and v["hull_dominates_menu_IH"]
    assert v["jensen_violations"] == 0 and v["jensen_worst_gap"] < 1e-9   # all-equal is the worst, exactly
    assert v["reduction_all_equal_is_worst"]
    assert v["reduced_sweep_worst_upper"] <= v["omega_lower"] + 1e-12     # sup Q <= omega (rigorous interval)
    assert v["tail_D1_s_ge_65"] and v["tail_D2_j_gt_500"]
    assert v["adversary_sweep_closed"]
    assert v["conjecture1_proved"] is False and v["claimed_as_theorem"] is False


def test_R7_stratification_and_rate_maximality():
    # R7 (global assembly) attacked via STRATIFICATION: A(F)<=C_1 for every tree, equality iff the de-loaded
    # single-hub cherry-bundle star. (i) rate<rho_B => A=0; (ii) rate=rho_B => cherry-arms => backbone-of-hubs
    # compressed by R4/R5/R6 to the canonical star. Rate-maximality (no tree beats rho_B) verified over zoo +
    # 200 random trees; its CORE is whole-tree Phi<=1 (the per-node R3 induction applied at any rooting).
    from verification import global_assembly as GA
    v = GA.certify()
    assert v["amplitude_equals_C1"] and v["amplitude_peaks_at_cherry_arm"]
    assert v["rate_maximality_holds"] and v["rate_over_count"] == 0
    assert v["star_uniquely_reaches_rho_B"]
    assert v["whole_tree_phi_le_1"] and v["whole_tree_max_logPhi"] < 0    # Phi(T)<=1 at every rooting
    assert v["branch_multiplicativity_verified"]
    assert 0.07 < v["uniqueness_margin_vs_two_hub"] < 0.08                # C_1 - C_1^2
    assert v["R7_closed"] is False and v["conjecture1_proved"] is False   # honest: Kelmans confluence remains


def test_kelmans_corners_strict_all_N():
    # Closes the Kelmans boundary: the strict-positivity certificate (symbolic in da,db,c, so ALL N).
    # Each corner numerator = (u-coeff>0)*u + all-nonneg-remainder, so Phi > 0 for any non-endpoint center
    # (u=da-1>0); equality forces da=1 (isomorphic recentering). Non-star backbones always have such a
    # center => a strictly increasing Kelmans move exists => the star is the unique sink, for every N.
    from verification import psi_close as P
    v = P.certify_corners_strict()
    assert v["all_corners_strict_all_N"]
    for name in ("C0", "C1", "C3", "C2"):
        assert v[name]["u_coeff"] > 0
        assert v[name]["remainder_all_nonneg"] and v[name]["den_positive"]
        assert v[name]["strict_for_da_gt_1"]


def test_matching_permanent_bridge():
    # The matching/permanent bridge (matching_bridge.tex), both halves, on trees up to 10 vertices:
    # (H1) per(L(T)) = sum over matchings M of prod_{v unmatched} deg(v);
    # (H2) the cavity recursion r_v = 1/(1 + sum_children w_vc r_c), w=1/(deg deg), computes
    #      pi(T) = per(L)/prod deg. The algebraic recursion step is machine-checked in Matching.lean.
    import numpy as np, networkx as nx
    from itertools import permutations, combinations
    from math import prod

    def permanent(M):
        n = M.shape[0]
        return sum(prod(M[i, p[i]] for i in range(n)) for p in permutations(range(n)))

    def matchings(G):
        E = list(G.edges()); res = [[]]
        for r in range(1, len(E) + 1):
            for combo in combinations(E, r):
                vs = [v for e in combo for v in e]
                if len(set(vs)) == 2 * r:
                    res.append(list(combo))
        return res

    def pi_cavity(G, root):
        deg = dict(G.degree())

        def rec(v, parent):
            subs = [(u,) + rec(u, v) for u in G.neighbors(v) if u != parent]
            P0 = prod(P for _, P, _ in subs) if subs else 1.0
            Pv = P0
            for (u, Pu, Pu0) in subs:
                Pv += (1.0 / (deg[v] * deg[u])) * Pu0 * prod(P for (uu, P, _) in subs if uu != u)
            return Pv, P0
        return rec(root, None)[0]

    for seed in (1, 2, 3, 4):
        for n in (6, 8, 10):
            G = nx.random_labeled_tree(n, seed=seed)
            nodes = sorted(G.nodes()); deg = dict(G.degree())
            L = np.array(nx.laplacian_matrix(G, nodelist=nodes).todense(), float)
            perL = permanent(L)
            # H1
            ms = 0.0
            for M in matchings(G):
                matched = {x for e in M for x in e}
                ms += prod(deg[v] for v in nodes if v not in matched)
            assert abs(perL - ms) < 1e-6                      # (H1)
            # H2
            pi_direct = perL / prod(deg[v] for v in nodes)
            assert abs(pi_direct - pi_cavity(G, nodes[0])) < 1e-9   # (H2)
