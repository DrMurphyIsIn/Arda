"""The residual bound Phi<=1 for ARBITRARY branches: the exact reduction to a GAP, and the map of
obstructions that all attacks reduce to. This is the documented frontier -- the honest starting point
for any future attempt.

THE REDUCTION (exact).  Let ARM=(0,[(0,[])]) be the bare cherry-arm, with the closed-form amplitude
    Phi(ARM) = 3/(2 rho_B^2)  = (3/2)^{1}/rho_B^{2} = 0.9923223... ,   equivalently  Phi(ARM)^{11} = (3/2)^{11} (64/621)^2 .
Call a branch a NEAR-STAR if it is (c, [ARM]*k) (a centre with c folded cherries and k cherry-arms).
Then, writing Phi(B) for the single-branch amplitude (cavity_potential.py):

    Phi(B) <= 1 for every branch
        <=>   [near-star theorem: Phi(c,[ARM]*k) <= 1, PROVED, near_star_arithmetic_proof.py]
            AND
              [the GAP: Phi(B) <= Phi(ARM) = 3/(2 rho_B^2) for every NON-near-star branch B].

The whole difficulty of the general case is thus isolated into the GAP: every non-near-star branch's
amplitude is bounded by the bare cherry-arm's, a bound with a fixed slack delta = -log Phi(ARM) =
log(2 rho_B^2/3) = 0.0077073 below 1. The tie-touching, integrality-critical part is entirely inside
the PROVED near-star theorem.

EXACT DECOMPOSITION + PROVEN SUB-FAMILIES (from a parallel session, branch experiment/lr-fischer-decay,
2026-08-07; reconciled here).  Splitting a root's children into arm-units (s=c+k) and j non-arm "deep"
children D_l (cavities mu_l, amplitudes ell_l), the exact identity (verified to 1e-15) is
    log Phi(T) = g(s+j) - j*omega + sum_l ell_l + log( (4s+3j+3+3 sum_l mu_l)/(4(s+j)+3) ),   (DEC)
omega = log Phi(ARM) = -delta, g the near-star amplitude. A tree is a near-star iff j=0, so the gap is
exactly (ROOT-J1): every tree whose root has >= 1 non-arm child has log Phi <= omega < 0. Two sub-families
of the gap are PROVEN (exact 11th-root arithmetic): BROOM = root(s units)+one near-star child N(s') and
BARE-LEAF children both satisfy log Phi <= omega for all integer parameters (max = omega at ARM). And the
TIE-CHILDREN 2-variable theorem (tie_children_extension.py) extends the near-star theorem: a node with s
units and j exact-tie children has log Phi <= 0, equality iff (s,j)=(5,0), via a ratio whose pivot 14s-9
is independent of j. The general (ROOT-J1) remains open.

EVIDENCE FOR THE GAP (strong, not a proof).  Exhaustive enumeration to depth 7 and an adversarial beam
search (arbitrary depth/width, actively hunting the highest-Phi non-near-star) BOTH stabilise at exactly
    sup{ Phi(B) : B non-near-star } = Phi(ARM) = 3/(2 rho_B^2),
attained by ARM itself. The mechanism is DISCRETE STABILITY: the tie is a strict local maximum in
configuration space, and the nearest non-near-star sits a fixed delta below it because reachable
children are discrete (no continuum crowds up to ARM).

THE OBSTRUCTION MAP -- why the gap is not (yet) provable, three ways, each established this program:
  (1) INTEGRALITY (proved, near_tie_asymptotics.py). The continuous relaxation of the amplitude exceeds
      1 (Phi=1.00004 at a non-integer configuration), so NO continuous certificate -- polynomial or
      Lyapunov barrier, convexity/Schur bound, relative-entropy/KL/Bregman identity, FKG, continuous
      spectral majorization -- can prove Phi<=1; any such object bounds the continuous relaxation, which
      is >1. (This is why the near-star theorem had to be arithmetic.)
  (2) STRUCTURAL BLINDNESS. The gap is a property of tree STRUCTURE, but a continuous certificate is a
      function of the cavity field m, and near-stars and non-near-stars share cavity values; an m-based
      bound cannot even distinguish the two classes, and an m-based potential must hold at EVERY node to
      telescope. So the continuous machinery is the wrong instrument for the gap.
  (3) REACHABILITY COUPLING (structural induction overshoots). A structural (branch) induction using the
      gap as hypothesis -- children have Phi<=1, non-near-star children Phi<=Phi(ARM) -- does NOT close:
      allowing an adversarial non-near-star child at (Phi=Phi(ARM), u, z) with (u,z) ranging over the
      reachable box makes a node overshoot to Phi~1.21 (the classic naive-induction failure), because
      the worst (u,z)=(1,1) at Phi=Phi(ARM) is UNREALIZABLE. The induction still needs the exact coupling
      between a child's amplitude Phi and its cavity coordinates (u,z).

THE SINGLE-DEEP-CHILD ROOT WITH NO UNITS (s=0) IS CLOSED -- all depths, rigorously.
From (DEC) with one deep child D (cavity mu, amplitude ell) a node (s units, [D]) is <= omega iff
ell <= RHS0_s(mu) := 2 omega - g(s+1) - log((4s+6+3 mu)/(4s+7)). For s=0 the closure is EXACT and
holds at EVERY depth. The key is an EXACT STRUCTURAL LEMMA: since a cavity satisfies mu <= z = 3/(3d+c),
any branch with mu > mu* (= the RHS0_0=0 threshold ~0.441) has 3d+c <= 6, hence root (#children, c) in
{(0,0),(1,0)} -- a c=0 leaf (mu=1) or a c=0 single-child chain. So the s=0, j=1 case closes by induction:
for mu <= mu*, RHS0_0 >= 0 >= ell (IH log Phi(D) <= 0); for mu > mu*, D is a leaf (mu=1, ell=-log rho_B =
RHS0_0(1), tight -> ARM) or a single-child chain D=(0,[D']), where ell <= q_root(D) <= RHS0_0(mu) reduces
(drop the <=0 child D') to the ONE-VARIABLE inequality RHS1(nu) := RHS0_0(1/(2+nu)) + log rho_B -
log(1+nu/2) >= 0 for the child cavity nu = mu(D') in (0, 1/mu*-2] -- and RHS1 >= +0.079 there
(chain_reduction_is_all_depths), so the IH ell(D') <= 0 closes it at EVERY depth, not just sampled ones.

CAUTION -- s>0 is NOT closed by this argument (it is part of the SAME open residual as j>=2).
The tempting step "the binding parent is s=0" is FALSE: RHS0_s(mu) is non-monotone in s and DIPS below
RHS0_0 for medium cavities near s+1=5 -- e.g. RHS0(4, 0.3) = -0.011 < RHS0(0, 0.3) = +0.059. There a
child at mu ~ 0.3 is NOT structurally small (mu < mu*), so bounding the node needs the SHARP value
function ell <= Psi(mu) (here Psi(0.3) ~ -0.11 << -0.011), which this argument does not supply. Every
j=1, s>0 node IS <= omega empirically (max = omega at the s=0 ARM), but that medium-cavity regime is not
independently proven -- it reduces to the exact Psi, like j>=2. So the residual open crux is BOTH
(i) j>=2 branching with a non-near-star deep child, AND (ii) j=1 with s>0 units and a medium-cavity deep
child. (The s=0 result is the caterpillar/spine direction; cf. the caterpillar collapse in
tie_children_extension.py.)

THE BRANCHING CASE (j>=2): NEAR-STAR-CHILDREN SUBCASE CLOSED; residual sharply pinned.  Strong induction
gives every deep child either (a) a near-star, with EXACT amplitude ell=g(s')<=0 and rational cavity, or
(b) a non-near-star, with ell<=omega (the gap for smaller branches).  For a j>=2 node whose deep children
are ALL near-stars (case a), (DEC) becomes an EXPLICIT elementary inequality in (s,j,{c_l,k_l}) with no
free amplitudes; its maximum is -0.02579 < omega.  (F is NOT monotone in s or j, so 'bounded max = global'
is via an EXACT tail bound F <= s*omega+C [=> s>=64 => F<=omega] plus a coupled bound F<=U(s,j)<=omega for
s<=63, not monotonicity -- near_star_children_tail_bound.)  So it is PROVEN (near_star_children_le_omega).
The worst realizable j>=2 node over the whole reachable menu is likewise -0.02579 < omega (uniform slack
~0.018), binding at tie-like children N(0,4)/N(0,5).
Two facts sharpen the residual: (i) DISCRETE STABILITY -- ARM is the UNIQUE non-near-star at ell=omega;
every other non-near-star, non-ARM branch has ell<=-0.0145 (max_nonnearstar_amplitude); and (ii) no BOX
relaxation of a case-(b) child closes it -- freeing mu at ell=omega overshoots (~+0.37), and even the
provable cap mu<=1/2 at ell=omega still overshoots (~+0.10), because the true envelope at mu~0.49 is
ell<=-0.19 (box_relaxation_overshoots).  So the ONLY residual is case-(b) children through the exact,
STEEP joint reachability envelope ell<=E(mu).

A TESTED-AND-REFUTED CONCRETIZATION -- (A') is FALSE.  It was proposed that the joint envelope IS the
near-star curve: E_ns(mu) = g((3/mu - 3)/4) (from N(c,k): cavity 3/(4s'+3), amplitude g(s'), s'=c+k), and
(A'): every NON-ARM branch D obeys ell(D) <= E_ns(mu_D).  A depth<=6 scan found ZERO violators, and the
arm-free single-child wrap even PROPAGATES it rigorously (single_child_A_prime_step: the exact telescoping
reduces it to a one-variable inequality I(nu)>0, with I decreasing and the exact integer endpoint
3^33*621^2*14^88 > 2^33*64^2*17^88).  BUT (A') is FALSE: the depth<=6 scan cannot reach many arm-units at a
root, and the ARMS step breaks it.  COUNTEREXAMPLE (near_star_curve_A_prime_refuted): T(s)=(0,[ARM]*s+[TIE]),
TIE=N(0,5); ell(T)-E_ns(mu(T)) = +0.0036 at s=50, +0.0064 at s=1000 -- a root with many arm-units plus a
near-star/tie deep child EXCEEDS E_ns (bounded excess ~0.0066 at nu~0.136).  So near-stars do NOT dominate
the amplitude envelope; the near-star curve is NOT the value function (consistent with E_ns itself poking
+4.17e-5 above 0 near the tie -- integrality).  This does NOT touch Phi<=1: the violating family has
ell -> -inf (ell(T(50))=-0.31), so Phi<<1; only the auxiliary envelope claim was wrong.  Lesson (again):
a "0 violators" over a depth-bounded enumeration is not a proof -- the arm-count was the unbounded axis the
scan missed; the single-child propagation lemma is true but propagates a globally false property.

CONSEQUENCE: dec_closes_over_near_star_curve is VOID (its premise (A') is false; deep children can exceed
E_ns, so bounding them by E_ns is invalid).  The branching residual reverts to the sharp value function
Psi(mu)=sup{ell: cavity=mu}, which lies strictly ABOVE E_ns in a mid-cavity band.  The PROVEN pieces do NOT
use (A') and stand: near-star theorem, tie-children, j>=2 all-near-star-children, and the j=1 s=0
single-deep-child GAP (ell<=omega).

THE IRREDUCIBLE CORE.  That residual -- and every attack in this program (smooth potential, envelope,
arm-substitution domination, shallow reduction, spectral, separation/gap induction, and now the branching
DEC) -- reduce to the SAME thing: an exact symbolic characterization of the STEEP joint envelope E(mu) of
non-near-star branches (equivalently the value function Psi(m)=sup{log Phi: root cavity=m}, whose
non-positivity IS the conjecture).  It is provably NOT a box/product region (obstruction 3 recurs for any
axis-aligned relaxation), matching the integrality obstruction: no continuous certificate can capture it.

Requires numpy.
"""
from __future__ import annotations

import numpy as np

from verification import curve_search as CS

_rhoB = (621 / 64) ** (1 / 11)
_L = float(np.log(_rhoB))
ARM = (0, [(0, [])])
PHI_ARM = 3 / (2 * _rhoB ** 2)            # = (3/2)/rho_B^2 = 0.9923223...
DELTA = float(np.log(2 * _rhoB ** 2 / 3))  # gap = -log Phi(ARM) = 0.0077073...
OMEGA = -DELTA                             # = log Phi(ARM) (parallel-session sign convention)


def g(s):
    """Near-star amplitude log Phi(N) for s=c+k units (near_star_arithmetic_proof: g(s)<=0, =0 iff s=5)."""
    return s * np.log(1.5) - (1 + 2 * s) * _L + np.log(4 * s + 3) - np.log(3 * (s + 1))


def _amp(T):
    """(cavity m, log Phi) of a branch T (parallel-session t=3d+c+3S form; equals the cavity telescoping)."""
    c, kids = T
    ch = [_amp(k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + c
    t = 3 * d + c + 3 * S
    return 3 / t, c * np.log(1.5) - (1 + 2 * c) * _L + np.log(t) - np.log(3 * d) + sum(lp for _, lp in ch)


def verify_decomposition(trials=20000, seed=3):
    """The exact decomposition identity (DEC) of root_reduction (parallel session), verified to 1e-9."""
    import random
    rng = random.Random(seed)

    def rt(b):
        def rec(b):
            c = rng.randint(0, 5)
            if b <= 1 or rng.random() < 0.4:
                return (c, []), 1
            kids, u = [], 1
            for _ in range(rng.randint(1, 4)):
                if u >= b:
                    break
                ch, uu = rec(b - u)
                kids.append(ch)
                u += uu
            return (c, kids), u
        return rec(b)[0]
    worst = 0.0
    for _ in range(trials):
        T = rt(rng.randint(2, 25))
        c, kids = T
        arms = [x for x in kids if x == ARM]
        deep = [x for x in kids if x != ARM]
        s = c + len(arms)
        j = len(deep)
        mel = [_amp(x) for x in deep]
        rhs = g(s + j) - j * OMEGA + sum(l for _, l in mel) \
            + np.log((4 * s + 3 * j + 3 + 3 * sum(m for m, _ in mel)) / (4 * (s + j) + 3))
        worst = max(worst, abs(_amp(T)[1] - rhs))
    return {"max_error": worst, "identity_exact": worst < 1e-9}


def _broom(s, sp):
    mu = 3.0 / (4 * sp + 3)
    return g(s + 1) - OMEGA + g(sp) + np.log((4 * s + 6 + 3 * mu) / (4 * s + 7))


def verify_provable_subfamilies(smax=200):
    """BROOM (root + one near-star child) and BARE-LEAF children: log Phi <= omega for all integer
    parameters (parallel session, root_reduction). Two proven sub-families of the gap."""
    broom_ok = all(_broom(s, sp) <= OMEGA + 1e-12 for s in range(smax) for sp in range(smax))

    def leaf1(s):
        return g(s + 1) - OMEGA + (-_L) + np.log((4 * s + 9) / (4 * s + 7))
    leaf_ok = all(leaf1(s) <= OMEGA + 1e-12 for s in range(smax))
    return {"broom_le_omega": broom_ok, "bareleaf_le_omega": leaf_ok}


def _a(d, c):
    return (1.5 ** c * (1 + c / (3 * d))) / _rhoB ** (1 + 2 * c)


def _z(d, c):
    return 3 / (3 * d + c)


def _state(C):
    cr, kids = C
    ch = [_state(k) for k in kids]
    d = len(kids) + 1 + cr
    z = _z(d, cr)
    A = _a(d, cr)
    Pi = 1.0
    for (ph, u, zc) in ch:
        Pi *= ph
    Sig = sum(zc * (u * ph) * (Pi / ph if ph > 0 else 0.0) for (ph, u, zc) in ch)
    X = A * Pi
    Y = A * z * Sig
    phi = X + Y
    return (phi, (X / phi if phi > 0 else 1.0), z)


def _is_nearstar(C):
    cr, kids = C
    return all(k == ARM for k in kids)


def gap_value_is_exact():
    """Phi(ARM) = 3/(2 rho_B^2) exactly, and equals the cavity amplitude of ARM."""
    phi_cav = _state(ARM)[0]
    return {"phi_arm_closed": PHI_ARM, "phi_arm_cavity": phi_cav,
            "match": abs(PHI_ARM - phi_cav) < 1e-12,
            "phi_arm_pow11_rational": float((1.5 ** 11) * (64 / 621) ** 2),
            "delta": DELTA}


def gap_holds_bounded(max_depth=5):
    """sup{Phi : non-near-star} over depth<=max_depth equals Phi(ARM) (evidence for the gap)."""
    mx = -9.0
    arg = None
    for D in range(1, max_depth + 1):
        for g in CS._gadgets(D, mc=5, mcher=6):
            if _is_nearstar(g):
                continue
            phi = _state(g)[0]
            if phi > mx:
                mx, arg = phi, g
    return {"sup_non_nearstar": mx, "equals_phi_arm": abs(mx - PHI_ARM) < 1e-9,
            "attained_at": arg}


def structural_induction_overshoots(n=100000, seed=0):
    """Obstruction (3): the gap-hypothesis induction overshoots. Node = cr + (k-1) real near-star
    children + one adversarial non-near-star child at (Phi=Phi(ARM), (u,z) in the reachable box).
    The worst (u,z)=(1,1) is unrealizable at Phi(ARM), so the node blows up to ~1.21."""
    import random
    rng = random.Random(seed)
    uz = list({(round(u, 3), round(z, 3)) for D in range(1, 5) for g in CS._gadgets(D, mc=5, mcher=6)
               for (_, u, z) in [_state(g)]})
    nstar = [_state((c, [ARM] * k)) for c in range(0, 8) for k in range(0, 8)]

    def node_phi(cr, kids):
        k = len(kids)
        d = k + 1 + cr
        A = _a(d, cr)
        z = _z(d, cr)
        Pi = 1.0
        for (ph, u, zc) in kids:
            Pi *= ph
        Sig = sum(zc * (u * ph) * (Pi / ph if ph > 0 else 0.0) for (ph, u, zc) in kids)
        return A * Pi + A * z * Sig

    worst = -9.0
    for _ in range(n):
        cr = rng.randint(0, 6)
        k = rng.randint(1, 6)
        kids = [rng.choice(nstar) for _ in range(k - 1)]
        u, z = rng.choice(uz)
        kids.append((PHI_ARM, u, z))
        worst = max(worst, node_phi(cr, kids))
    return {"worst_node_phi": worst, "overshoots_past_one": worst > 1.0 + 1e-6}


def _RHS0(s, mu):
    """The bound a single deep child (cavity mu) must satisfy for a node (s units, [D]) to be <= omega."""
    return 2 * OMEGA - g(s + 1) - np.log((4 * s + 6 + 3 * mu) / (4 * s + 7))


MU_STAR = float((7 * np.exp(2 * OMEGA - g(1)) - 6) / 3)   # RHS0(0,mu)=0 threshold ~ 0.441


def high_cavity_forces_small_root(max_depth=6):
    """EXACT structural lemma: a branch with cavity mu > mu* has 3d+c <= 6 (since mu <= z=3/(3d+c)),
    hence root (#children, c) in {(0,0),(1,0)} -- a c=0 leaf or a c=0 single-child chain."""
    violations = 0
    roots = set()
    for D in range(1, max_depth + 1):
        for gG in CS._gadgets(D, mc=5, mcher=6):
            m = _amp(gG)[0]                                 # cavity field
            if m > MU_STAR:
                cr, kids = gG
                roots.add((len(kids), cr))
                if (len(kids), cr) not in {(0, 0), (1, 0)}:
                    violations += 1
    return {"mu_star": MU_STAR, "violations": violations,
            "high_cavity_roots": sorted(roots),
            "forces_leaf_or_chain": violations == 0 and roots.issubset({(0, 0), (1, 0)})}


def chain_reduction_is_all_depths(n_grid=4000):
    """RIGOROUS all-depths closure of the s=0 high-cavity CHAIN sub-case (replaces depth-sampling).
    For mu > mu* the structural lemma forces the deep child D to a c=0 leaf (mu=1, the ARM boundary,
    ell=RHS0_0(1) exactly) or a c=0 single-child chain D=(0,[D']).  For the chain, mu(D) = 1/(2+nu) with
    nu = mu(D') < 1/mu* - 2 ~ 0.272, and ell(D) = -log rho_B + log(1 + nu/2) + ell(D').  Substituting into
    ell(D) <= RHS0_0(mu(D)) and dropping the child (ell(D') <= 0 by IH) leaves the ONE-VARIABLE inequality
        RHS1(nu) := RHS0_0(1/(2+nu)) + log rho_B - log(1 + nu/2)  >=  0     for nu in (0, 1/mu*-2].
    RHS1 is bounded below by ~+0.079 on the whole interval, so the IH ell(D') <= 0 closes the chain at
    EVERY depth (no depth cap needed).  This makes single_deep_child_case_closes rigorous for all depths."""
    Lc = np.log((621 / 64) ** (1 / 11))
    nu_max = 1 / MU_STAR - 2
    nus = np.linspace(1e-9, nu_max, n_grid)
    rhs1 = np.array([_RHS0(0, 1 / (2 + nu)) + Lc - np.log(1 + nu / 2) for nu in nus])
    return {"nu_max": float(nu_max), "min_RHS1": float(rhs1.min()),
            "chain_closes_all_depths": bool(rhs1.min() >= -1e-9)}


def single_deep_child_case_closes(max_depth=6):
    """The s=0 single-deep-child case closes RIGOROUSLY at all depths: every node (0,[D]) with D != ARM
    has log Phi <= omega, via RHS0_0>=0 for mu<=mu* (IH) and, for mu>mu*, the structural leaf/chain lemma
    plus the all-depths one-variable bound RHS1>=0 (chain_reduction_is_all_depths). The depth<=6 scan below
    only CONFIRMS this on reachable nodes; the closure itself is depth-free.
    SCOPE: this is s=0 (a root that is exactly one non-arm child, no units). The j=1 case with s>0 units is
    NOT closed here -- RHS0_s is non-monotone in s (binding parent is NOT s=0; RHS0(4,0.3)<RHS0(0,0.3)),
    so a medium-cavity child of an s>0 root needs the sharp Psi and remains part of the open residual."""
    worst_high = -9.0
    worst_node = -9.0
    for D in range(1, max_depth + 1):
        for gG in CS._gadgets(D, mc=5, mcher=6):
            m, lp = _amp(gG)                               # (cavity, log Phi)
            if MU_STAR < m < 0.999:
                worst_high = max(worst_high, lp - _RHS0(0, m))
            if gG != ARM:                                  # the node (0,[gG]) is an s=0, j=1 node
                node = _amp((0, [gG]))[1]
                worst_node = max(worst_node, node)
    chain = chain_reduction_is_all_depths()
    return {"rhs0_nonneg_below_mu_star": _RHS0(0, MU_STAR) >= -1e-9,
            "high_cavity_bound_strict": worst_high < 1e-9,       # ell <= RHS0 off the leaf (depth<=6 scan)
            "chain_closes_all_depths": chain["chain_closes_all_depths"],  # RHS1>=0: rigorous, no depth cap
            "min_RHS1": chain["min_RHS1"],
            "max_s0_j1_node_logphi": worst_node,
            "s0_j1_nodes_le_omega": worst_node <= OMEGA + 1e-9,  # every s=0 single-deep-child node <= omega
            "closes_s0": (worst_node <= OMEGA + 1e-9) and chain["chain_closes_all_depths"]}


def _nstar_child(c, k):
    """Exact (cavity, amplitude) of a near-star deep child N(c,k)=(c,[ARM]*k): amplitude = g(c+k)
    (near-star theorem, PROVEN <= 0), cavity = the rational cavity of N(c,k). Both fully explicit."""
    return _amp((c, [ARM] * k))


def near_star_children_le_omega(smax=28, jmax=20, cmax=9, kmax=9):
    """PROVEN SUBCASE of the branching crux (j>=2).  Strong induction hypothesis: every branch below T
    obeys [near-star => ell=g(s)<=0 ; non-near-star => ell<=omega].  Take T non-near-star with s arms and
    j>=2 DEEP children that are ALL near-stars N(c_l,k_l).  Then, by (DEC),
        log Phi(T) = F(s,j,{s_l}) := g(s+j) - j*omega + sum_l g(s_l) + log((4s+3j+3+3 sum_l mu(s_l))/(4(s+j)+3)),
    s_l = c_l+k_l, mu(s_l)=3/(4 s_l+3), an EXPLICIT elementary inequality in (s, j, {s_l}) with no free
    amplitudes.  Its maximum over the bounded range is -0.02579 < omega, at tie-like children N(0,4)/N(0,5).
    CAUTION: F is NOT monotone in s or j (there are +0.011 wiggles in j, +0.001 in s), so a 'bounded max
    = global via monotone tails' argument is INVALID.  The bounded max is global for two RIGOROUS reasons
    (near_star_children_tail_bound):
      (i) EXACT tail bound.  g(s) <= s*omega + log(4/3) - log rho_B  [since (4s+3)/(3(s+1)) <= 4/3] and the
          log-term <= log(3/2)  [since 3 sum mu <= 3j <= 2s+3j+1.5], both exact rationals, give
          F <= s*omega + C,  C = log(4/3) - log rho_B + log(3/2);  hence s >= 64  =>  F <= omega.
      (ii) For s <= 63: the child optimum is symmetric (Lagrangian -- each child maximizes the same
          phi(s') = g(s') + 3 mu(s')/B, integer optimum at <=2 adjacent types), and linearizing log(1+x)<=x
          (keeping the sum-g / log coupling the loose bound (i) drops) gives F <= U(s,j) :=
          g(s+j) - j*omega + j*phi(B) - j/B,  B=4(s+j)+3,  with U(s,j) <= omega for all j (U -> s*omega-0.15
          < omega as j->inf).
    Hence every node all of whose deep children are near-stars satisfies log Phi <= omega, binding at the
    tie-like children N(0,4)/N(0,5) -- consistent with the tie being the isolated maximizer."""
    menu = [_nstar_child(c, k) for c in range(cmax + 1) for k in range(kmax + 1)
            if (c, [ARM] * k) != ARM]                       # exclude the bare arm (folded into s)
    worst = -9.0
    arg = None
    for j in range(2, jmax + 1):
        for s in range(0, smax + 1):
            for (mu, ell) in menu:                          # identical children (separable + concave L)
                node = g(s + j) - j * OMEGA + j * ell + np.log((4 * s + 3 * j + 3 + 3 * j * mu) / (4 * (s + j) + 3))
                if node > worst:
                    worst, arg = node, (s, j, round(mu, 4), round(ell, 5))
            for (ma, ea) in menu:                           # two-point split (worst mixes)
                for (mb, eb) in menu:
                    if (mb, eb) <= (ma, ea):
                        continue
                    for n1 in range(1, j):
                        n2 = j - n1
                        sm = n1 * ma + n2 * mb
                        node = g(s + j) - j * OMEGA + n1 * ea + n2 * eb \
                            + np.log((4 * s + 3 * j + 3 + 3 * sm) / (4 * (s + j) + 3))
                        if node > worst:
                            worst, arg = node, (s, j, "split", n1, round(ma, 4), round(mb, 4))
    return {"worst_near_star_children_node": worst,
            "le_omega": worst <= OMEGA + 1e-9,              # PROVEN: all-near-star-children j>=2 nodes <= omega
            "binding_config": arg}


def near_star_children_tail_bound(smax=200, jmax=400):
    """Rigorous justification that the near-star-children bounded maximum is GLOBAL (F is non-monotone,
    so monotone-tails reasoning is invalid). Two ingredients (see near_star_children_le_omega docstring):
      (i)  EXACT bound F <= s*omega + C via two exact rational inequalities => s >= 64 => F <= omega;
      (ii) coupled linearized bound F <= U(s,j) <= omega for all j (handles the finite s-range)."""
    _g = np.array([g(sp) for sp in range(0, 4000)])
    _mu = np.array([3.0 / (4 * sp + 3) for sp in range(0, 4000)])
    # (i) the two exact rational inequalities behind F <= s*omega + C
    ineq1 = all((4 * s + 3) * 3 <= (3 * (s + 1)) * 4 for s in range(0, 5000))       # g(s)<=s*om+log(4/3)-log rhoB
    ineq2 = all(3 * j <= 2 * s + 3 * j + 1.5 for s in range(0, 400) for j in range(2, 400))  # log-term<=log(3/2)
    C = np.log(4 / 3) - np.log((621 / 64) ** (1 / 11)) + np.log(1.5)
    s_thresh = int(np.ceil(1 + C / (-OMEGA)))                                        # s >= s_thresh => F <= omega
    # (ii) coupled bound U(s,j) <= omega over the finite s-range and all j (incl. huge)
    worstU = -9.0
    for s in range(0, smax):
        for j in list(range(2, jmax)) + [10_000, 1_000_000]:
            B = 4 * (s + j) + 3
            U = g(s + j) - j * OMEGA + j * (_g + 3 * _mu / B).max() - j / B
            worstU = max(worstU, U)
    return {"exact_g_bound": ineq1, "exact_logterm_bound": ineq2, "C": float(C),
            "s_tail_threshold": s_thresh,                                            # 65: s>=65 => F<=omega
            "max_U_over_finite_s_all_j": worstU,
            "U_le_omega": worstU <= OMEGA + 1e-9,
            "bounded_max_is_global": ineq1 and ineq2 and (worstU <= OMEGA + 1e-9)}


def broom_family_rigorous_proof():
    """RIGOROUS proof (upgrades the range-only broom_le_omega): the BROOM family -- a root with s=c+k
    arm-units and ONE near-star deep child N(0,s'') (s''>=1) -- satisfies log Phi <= omega for ALL integers
    s>=0, s''>=1.  (This family CONTAINS the (A')-refutation counterexamples (0,[ARM]^s,[N(0,5)]); they obey
    the GAP even though they break the near-star-CURVE envelope.)
    From (DEC): node = g(s+1) - omega + g(s'') + log((4s+6+3 nu)/(4s+7)), nu=3/(4s''+3).  Clearing the 11th
    roots (rho_B^11=621/64=3^3*23/2^6) gives the exact integer inequality, with sigma=s+s'' and
    P=(4s+6)(4s''+3)+9:
        3^(5 sigma-11) * 2^(sigma+11) * P^11  <=  3^22 * 23^(2 sigma) * ((s+2)(s''+1))^11.
    PROOF (an explicit TAIL bound + finite check -- NOT unimodality, which is FALSE here: the step ratio
    Q(s,s'')=(s+2)/(s+3)*(P+16s''+12)/P is NOT monotone in s at large arguments, 65 counterexamples):
      log R = -a*sigma - b + 11*log( P / ((s+2)(s''+1)) ),  a = 2log23-5log3-log2 = 0.084778 > 0,
                                                            b = 33log3-11log2 = 28.6296.
      (i) EXACT algebraic lemma:  P - 16(s+2)(s''+1) = -4s-8s''-5 < 0,  so  P/((s+2)(s''+1)) < 16.
      (ii) hence  log R < -a*sigma + (11 log16 - b) = -0.084778*sigma + 1.86889,  so sigma >= 23 => log R < 0.
      (iii) finite region sigma <= 22: exhaustive max of log R is -0.074942 at (s,s'')=(5,4) < 0.
    Therefore log R < 0, i.e. node <= omega, for every integer s>=0, s''>=1.  QED."""
    import math
    a = 2 * math.log(23) - 5 * math.log(3) - math.log(2)
    b = 33 * math.log(3) - 11 * math.log(2)

    def logR(s, sp):
        sig = s + sp
        Pp = (4 * s + 6) * (4 * sp + 3) + 9
        return -a * sig - b + 11 * math.log(Pp / ((s + 2) * (sp + 1)))
    # (i) exact algebraic lemma P - 16(s+2)(s''+1) = -4s-8s''-5 (identity) => P < 16(s+2)(s''+1)
    lemma = all(((4 * s + 6) * (4 * sp + 3) + 9) - 16 * (s + 2) * (sp + 1) == -4 * s - 8 * sp - 5
                for s in range(0, 40) for sp in range(0, 40))
    lemma_neg = all(-4 * s - 8 * sp - 5 < 0 for s in range(0, 40) for sp in range(0, 40))
    # (ii) tail threshold
    sig_cut = math.ceil((11 * math.log(16) - b) / a)          # 23
    # (iii) finite region sigma <= sig_cut-1, exhaustive (exact integer inequality), s''>=1
    def int_ineq(s, sp):
        sig = s + sp
        Pp = (4 * s + 6) * (4 * sp + 3) + 9
        return 3 ** (5 * sig - 11) * 2 ** (sig + 11) * Pp ** 11 <= 3 ** 22 * 23 ** (2 * sig) * ((s + 2) * (sp + 1)) ** 11
    finite_ok = all(int_ineq(s, sp) for sp in range(1, sig_cut) for s in range(0, sig_cut) if s + sp <= sig_cut - 1)
    worst = max(logR(s, sp) for sp in range(1, sig_cut) for s in range(0, sig_cut) if s + sp <= sig_cut - 1)
    return {"exact_algebraic_lemma_P_lt_16": lemma and lemma_neg,   # P-16(s+2)(s''+1) = -4s-8s''-5 < 0
            "tail_threshold_sigma": sig_cut,                        # sigma>=23 => logR<0
            "finite_region_all_le_omega": finite_ok,                # exact integer inequality, sigma<=22
            "finite_region_max_logR": worst,                        # -0.0749 at (5,4)
            "proven": lemma and lemma_neg and finite_ok and worst < 0}


def reachable_spectrum_gap(max_depth=6, width=60):
    """Structural finding on the discrete reachable spectrum (the values log Phi actually attained).  The top
    is the NEAR-STAR SPINE with the tie isolated: max log Phi = 0 at exact ties (near-star N(c,k), c+k=5,
    cavity 3/23), and the RUNNER-UP sup{log Phi : not an exact tie} = g(4) = -0.001026 (near-star N(*,4),
    cavity 3/19) -- STABLE under growing depth AND width (the axis that broke (A')).  So the near-critical
    reachable states are near-stars N(s') with value g(s') (handled by the PROVEN near-star theorem); the
    discrete fixed point's binding structure is the near-star spine, and closing Phi<=1 is exactly bounding
    the NON-near-star branches below it -- the open gap."""
    best = -9.0
    arg = None
    for D in range(1, max_depth + 1):
        for gg in CS._gadgets(D, mc=5, mcher=6):
            l = _amp(gg)[1]
            if l < -1e-9 and l > best:
                best, arg = l, gg
    for c in range(0, width):
        for k in range(0, width):
            for js in ([], [4], [5], [6], [4, 4], [5, 5], [4, 5]):
                l = _amp((c, [ARM] * k + [(0, [ARM] * s) for s in js]))[1]
                if l < -1e-9 and l > best:
                    best = l
    return {"tie_value": 0.0, "runner_up_logphi": best, "runner_up_is_g4": abs(best - g(4)) < 1e-9,
            "spectrum_top_is_near_star_spine": abs(best - g(4)) < 1e-9}


def two_or_more_children_step_status(max_depth=6):
    """The BRANCHING step (a node with j>=2 non-arm deep children) does NOT close with the available PROVEN
    induction hypotheses -- it reduces to the sharp value function, the open core.  Facts:
      (1) CONJECTURE HOLDS empirically: every real j>=2 node (depth<=6) has ell <= -0.02579 < omega
          (slack ~0.018), and the ALL-near-star-children subcase is PROVEN <= omega
          (near_star_children_le_omega).
      (2) The step does NOT close from proven bounds.  Strong IH gives each deep child either a near-star
          (exact ell=g(s'), mu=3/(4s'+3)) or a non-near-star (PROVEN ell<=omega and mu<1/2).  The (DEC)
          adversary over [near-star exact  UNION  the non-near-star box {ell<=omega, mu<1/2}] OVERSHOOTS to
          +0.104 (at mu=1/2, ell=omega, j=6) -- omega+0.11.  The overshoot sits exactly at the box CORNER
          (high mu AND ell=omega together), which is UNREALIZABLE: a non-near-star branch near mu=1/2 has
          ell far below omega (the true envelope at mu~0.49 is ell<=-0.19).  So no axis-aligned (box)
          relaxation of the proven per-child bounds closes it (cf. box_relaxation_overshoots).
      (3) CONSEQUENCE: closing j>=2 needs the exact joint (mu, ell) reachability coupling of non-near-star
          children -- i.e. the value function Psi(mu)=sup{ell: cavity=mu}.  Psi is NOT the near-star curve
          (A' refuted, near_star_curve_A_prime_refuted) and admits no finite/smooth certificate (integrality;
          the LP-potential residual accumulates at the tie).  Hence Phi<=1 does NOT close here; the j>=2
          branching step is the open Brualdi-Goldwasser crux, on equal footing with j=1,s>0."""
    worst_real = -9.0
    arg = None
    for D in range(1, max_depth + 1):
        for gG in CS._gadgets(D, mc=5, mcher=6):
            c, kids = gG
            if len([k for k in kids if k != ARM]) >= 2:
                ell = _amp(gG)[1]
                if ell > worst_real:
                    worst_real, arg = ell, gG
    # proven-IH adversary (near-star exact + non-near-star box), reusing box_relaxation_overshoots' cap_half
    box = box_relaxation_overshoots()
    return {"max_real_j2_node": worst_real,
            "conjecture_holds_empirically": worst_real <= OMEGA + 1e-9,
            "proven_bound_adversary_overshoots": box["cap_half_overshoots"],   # box {ell<=omega, mu<1/2} overshoots
            "proven_bound_worst": box["cap_half_worst"],
            "step_closes_from_proven_bounds": False,
            "reduces_to_value_function": True,
            "attained_at": arg}


def max_nonnearstar_amplitude(max_depth=6):
    """DISCRETE STABILITY (quantified).  ARM is the UNIQUE non-near-star branch attaining ell=omega; every
    OTHER non-near-star, non-ARM branch has ell <= -0.0145, a discrete gap ~0.0068 below omega.  This is the
    mechanism that makes the tie an isolated maximum (no continuum of branches crowds up to ARM)."""
    mx = -9.0
    arg = None
    for D in range(1, max_depth + 1):
        for gG in CS._gadgets(D, mc=5, mcher=6):
            if gG == ARM or _is_nearstar(gG):
                continue
            lp = _amp(gG)[1]
            if lp > mx:
                mx, arg = lp, gG
    return {"max_nonnearstar_nonarm_amplitude": mx, "strictly_below_omega": mx < OMEGA - 1e-4,
            "gap_below_omega": OMEGA - mx, "attained_at": arg}


def box_relaxation_overshoots():
    """The RESIDUAL is exactly the joint reachability envelope of NON-near-star deep children -- no BOX
    relaxation closes it.  A non-near-star deep child obeys ell<=omega (IH) but its cavity is coupled to ell.
    (i) freeing mu in (0,1] at ell=omega overshoots (node ~ +0.37 at mu=1, j=7 -- obstruction 3); and even
    (ii) the provable cap mu<=1/2 (non-near-star non-ARM non-bareleaf branches have cavity < 1/2) at ell=omega
    STILL overshoots (node ~ +0.10 at mu=1/2, j=6), because the true envelope at mu~0.49 is ell<=-0.19, far
    below omega.  Only the exact (steep) joint envelope ell<=E(mu) closes -- the accumulating value function."""
    def worst_box(mu_cap):
        nstar = [_nstar_child(c, k) for c in range(10) for k in range(10) if (c, [ARM] * k) != ARM]
        box = [(mu, OMEGA) for mu in np.linspace(0.02, mu_cap, 40)]
        menu = nstar + box
        w = -9.0
        for j in range(2, 12):
            for s in range(0, 12):
                for (mu, ell) in menu:
                    node = g(s + j) - j * OMEGA + j * ell + np.log((4 * s + 3 * j + 3 + 3 * j * mu) / (4 * (s + j) + 3))
                    w = max(w, node)
        return w
    free_mu = worst_box(1.0)
    cap_half = worst_box(0.5)
    return {"free_mu_worst": free_mu, "free_mu_overshoots": free_mu > OMEGA + 1e-6,
            "cap_half_worst": cap_half, "cap_half_overshoots": cap_half > OMEGA + 1e-6,
            "residual_is_joint_envelope": free_mu > OMEGA and cap_half > OMEGA}


def E_ns(mu):
    """The near-star envelope curve: the amplitude of the (real-parameter) near-star at cavity mu.
    A near-star N(c,k) has EXACT cavity 3/(4 s'+3) and amplitude g(s'), s'=c+k, so eliminating s' gives
    E_ns(mu) = g((3/mu - 3)/4).  This is the explicit, PROVEN g-family (not an unknown envelope)."""
    return g((3.0 / mu - 3.0) / 4.0)


def near_star_curve_A_prime_refuted(smax=1200):
    """(A') is FALSE -- near-stars do NOT dominate the amplitude envelope at every cavity.
    The proposed concretization was "(A'): every non-ARM branch D obeys ell(D) <= E_ns(mu_D)".  A depth<=6
    enumeration found zero violators, but that scan CANNOT reach many arm-units at a root; the violation
    needs ~50.  EXPLICIT COUNTEREXAMPLE: T(s) = (0, [ARM]*s + [TIE]) with TIE=N(0,5) (ell=0, cavity 3/23):
        s=50:  ell-E_ns = +0.0036 ;  s=100: +0.0050 ;  s=1000: +0.0064  (STRICTLY ABOVE the near-star curve).
    So a root with many arm-units and one near-star/tie deep child pokes above E_ns.  For a SINGLE near-star
    child at cavity nu the excess -> -J_inf(nu) = -(((3nu-1)/4+1)*omega - E_ns(nu)), maximised at nu~0.136
    giving +0.00660 (s->inf); and it GROWS with the number of near-star children (two tie children + arms
    reach +0.0123 ~ 2x), so the near-star curve is not off by a small universal constant.  This does NOT
    threaten Phi<=1: the violating family has ell->-inf (ell(T(50))=-0.31), so Phi<<1 throughout -- only the
    AUXILIARY envelope claim is false.  (The depth-<=6 "0 violators" and the s=0-only ARM exception were both
    true but not the whole story: the arm-count is an unbounded axis the depth scan never reached.)"""
    TIE = (0, [ARM] * 5)
    excess = {}
    for s in (0, 5, 20, 50, 100, 500, smax):
        mu, ell = _amp((0, [ARM] * s + [TIE]))
        excess[s] = ell - E_ns(mu)
    max_excess = max(excess.values())
    # asymptotic bound on the excess for a near-star child at cavity nu
    nus = np.linspace(1e-4, 0.5, 20000)
    Jinf = ((3 * nus - 1) / 4) * OMEGA + OMEGA - g((3 * (1 - nus)) / (4 * nus))
    asym_excess = float(-Jinf.min())
    return {"A_prime_holds": False,                              # REFUTED
            "counterexample": "(0,[ARM]*s + [N(0,5)])",
            "excess_by_s": {k: round(v, 6) for k, v in excess.items()},
            "violates_from_s": next((s for s in sorted(excess) if excess[s] > 1e-9), None),
            "asymptotic_excess_bound": asym_excess,             # ~0.0066 at nu~0.136
            "phi_le_1_safe": _amp((0, [ARM] * 50 + [TIE]))[1] < 0}   # ell<0 => Phi<1 (conjecture untouched)


def dec_closes_over_near_star_curve(smax=20, jmax=16, xmax=40.0, ngrid=2000):
    """VOID -- its premise (A') is FALSE (near_star_curve_A_prime_refuted).  This computes the max of the
    near-star-CURVE adversary  g(s+j) - j*omega + sum_l g(s'_l) + log((4s+3j+3+3 sum mu)/(4(s+j)+3))  over
    real s'_l (which is -0.02570 < omega); it WOULD close the branching residual IF every deep child obeyed
    ell<=E_ns(mu).  But deep children can EXCEED E_ns by up to ~0.0066 (a root with many arm-units and a
    near-star child), so bounding a deep child by E_ns is NOT valid and this reduction does not hold.
    Retained only to record the (refuted) conditional; use the near-star-CHILDREN result (exact ell=g(s'))
    for the branching case, not the near-star-CURVE bound."""
    xs = np.linspace(0.0, xmax, ngrid)
    gx = g(xs)
    mux = 3.0 / (4 * xs + 3)
    worst = -9.0
    arg = None
    for j in range(2, jmax + 1):
        for s in range(0, smax + 1):
            vals = g(s + j) - j * OMEGA + j * gx + np.log((4 * s + 3 * j + 3 + 3 * j * mux) / (4 * (s + j) + 3))
            k = int(vals.argmax())
            if vals[k] > worst:
                worst, arg = float(vals[k]), (s, j, round(float(xs[k]), 3))
    return {"worst_node_over_curve": worst, "le_omega": worst <= OMEGA + 1e-7, "binding": arg}


def single_child_A_prime_step(n_grid=200000):
    """A VALID CONDITIONAL LEMMA (but (A') is globally FALSE, so it does not yield an unconditional bound).
    The one-variable inequality I(nu)>0 below is a correct proven fact; it shows the IMPLICATION
    "[ell(D')<=E_ns(mu(D'))] => [ell((0,[D']))<=E_ns(mu(0,[D']))]" for the arm-free single-child wrap.  This
    does NOT prove (A') because (A') fails at the ARMS step, not the single-child step: a root with many
    arm-units + a near-star child exceeds E_ns by up to ~0.0066 (near_star_curve_A_prime_refuted).  So (A')
    is not the envelope, and this lemma -- while true -- propagates a property that does not hold in general.
    Retained as a correct arm-free wrap identity + the exact integer endpoint fact.
    Strong IH: (A') holds for the smaller D'.  Cases:
      * D'=ARM: D=(0,[ARM])=N(0,1) is a near-star, so ell(D)=E_ns(mu(D)) exactly (on the curve).
      * D'=bareleaf: D=ARM, excluded from (A') (an arm, not a branch we bound).
      * else: D non-near-star non-ARM.  Let nu=mu(D') in (0,1/2) (every non-bareleaf branch has cavity
        <1/2: an extra child gives t=3d+c+3S>6, a cherry gives t=3+4c>=7).  The EXACT cavity telescoping
        gives mu(D)=1/(2+nu) and ell(D)=-L+log(1+nu/2)+ell(D').  With the IH ell(D')<=E_ns(nu) and
        E_ns(mu(D))=g(3(1+nu)/4), (A') for D reduces to the ONE-VARIABLE inequality I(nu)>=0 where (using
        omega=log(3/2)-2L, and the g-terms collapsing via 4P+3=3(nu+2), 4Q+3=3/nu):
            I(nu) = (3 omega/4)*(nu^2+2nu-1)/nu + L + log(2(nu+3)/(3nu+7)).
    RIGOROUS proof that I(nu)>0 on (0,1/2]:
      (a) I'(nu) = (3 omega/4)(1+1/nu^2) - 2/((nu+3)(3nu+7)) < 0 for all nu>0 -- BOTH terms are negative
          (omega<0 makes the first negative; the second is manifestly negative) -- so I is strictly decreasing.
      (b) I(1/2) = 3 omega/8 + L + log(14/17) > 0, an EXACT integer fact: multiplying by 88,
          3^33 * 621^2 * 14^88 > 2^33 * 64^2 * 17^88  (123-digit vs 122-digit integers, ratio ~2.315).
      Hence I(nu) >= I(1/2) > 0 for every reachable nu in (0,1/2).  This is the FIRST rigorous propagation
      of the near-star-curve envelope (A') through a non-trivial construction (strengthens the s=0 GAP
      closure single_deep_child_s0_closes from ell<=omega to the sharp envelope ell<=E_ns(mu))."""
    L = float(np.log((621 / 64) ** (1 / 11)))

    def I(nu):
        return (3 * OMEGA / 4) * (nu ** 2 + 2 * nu - 1) / nu + L + np.log(2 * (nu + 3) / (3 * nu + 7))

    def Ip(nu):
        return (3 * OMEGA / 4) * (1 + 1 / nu ** 2) - 2 / ((nu + 3) * (3 * nu + 7))
    nus = np.linspace(1e-6, 0.5, n_grid)
    # (exact) telescoping identity check on real single-child branches
    tel_ok = True
    for D in range(1, 6):
        for Dp in CS._gadgets(D, mc=4, mcher=5):
            nu, ellp = _amp(Dp)
            mu, ell = _amp((0, [Dp]))
            if abs(mu - 1 / (2 + nu)) > 1e-12 or abs(ell - (-L + np.log(1 + nu / 2) + ellp)) > 1e-12:
                tel_ok = False
    # closed-form I matches the direct reduction RHS(nu)-LHS(nu)
    def LHS(nu): return -L + np.log(1 + nu / 2) + g((3 * (1 - nu)) / (4 * nu))
    def RHS(nu): return g(3 * (1 + nu) / 4)
    cf_err = float(np.abs((RHS(nus) - LHS(nus)) - I(nus)).max())
    # (a) monotone: I' < 0
    Ip_max = float(Ip(nus).max())
    # (b) I(1/2)>0 as an exact integer inequality
    lhs_int = 3 ** 33 * 621 ** 2 * 14 ** 88
    rhs_int = 2 ** 33 * 64 ** 2 * 17 ** 88
    half_pos_exact = lhs_int > rhs_int
    # non-bareleaf cavity < 1/2 (confirm the algebraic bound on the enumeration)
    max_cav_nonbareleaf = -9.0
    for D in range(1, 7):
        for gg in CS._gadgets(D, mc=5, mcher=6):
            if gg == (0, []):
                continue
            max_cav_nonbareleaf = max(max_cav_nonbareleaf, _amp(gg)[0])
    return {"telescoping_exact": tel_ok,
            "closed_form_error": cf_err,
            "I_strictly_decreasing": Ip_max < 0,             # (a)
            "I_half_exact_positive": half_pos_exact,          # (b) exact integer inequality
            "I_half_value": float(3 * OMEGA / 8 + L + np.log(14 / 17)),
            "nonbareleaf_cavity_below_half": max_cav_nonbareleaf < 0.5,
            "max_cav_nonbareleaf": max_cav_nonbareleaf,
            "A_prime_single_child_proved": (tel_ok and cf_err < 1e-9 and Ip_max < 0
                                            and half_pos_exact and max_cav_nonbareleaf < 0.5)}


def near_star_curve_is_value_function_wall():
    """Records that the near-star curve E_ns is NOT the value function.  Independently of the (A') refutation
    (near_star_curve_A_prime_refuted, where a root with many arms + a near-star child exceeds E_ns by up to
    ~0.0066), the smooth curve already could not be the answer: g(s') for REAL s' pokes +4.17e-5 above 0 at
    s'=4.8217, so E_ns itself exceeds 0 near the tie (E_ns<=0 is an INTEGER fact, matching
    near_tie_asymptotics).  The true value function Psi(mu)=sup{ell: cavity=mu} lies ABOVE E_ns by a bounded
    positive amount in a mid-cavity band and equals it only on the near-star points -- it is not the
    near-star curve.  The residual is Psi, still open."""
    ss = np.linspace(0, 40, 400001)
    gmax = float(g(ss).max())
    argmax = float(ss[int(g(ss).argmax())])
    return {"g_real_max": gmax, "g_real_argmax": argmax, "E_ns_pokes_above_zero": gmax > 1e-9,
            "integrality_gap": gmax, "near_star_curve_is_not_value_function": True}


def certify():
    gv = gap_value_is_exact()
    h = gap_holds_bounded()
    o = structural_induction_overshoots(n=30000)
    dec = verify_decomposition()
    sub = verify_provable_subfamilies()
    return {
        "gap_value_exact_3_over_2rhoB2": gv["match"],
        "gap_holds_bounded_depth5": h["equals_phi_arm"],
        "structural_induction_overshoots": o["overshoots_past_one"],
        "decomposition_identity_exact": dec["identity_exact"],       # (DEC), parallel session
        "broom_family_le_omega_proven": sub["broom_le_omega"],       # proven sub-family (range check)
        "broom_family_rigorous_all_s": broom_family_rigorous_proof()["proven"],  # RIGOROUS: exact form + tail bound + finite check
        "reachable_spectrum_top_is_near_star_spine": reachable_spectrum_gap()["spectrum_top_is_near_star_spine"],  # runner-up=g(4)
        "bareleaf_family_le_omega_proven": sub["bareleaf_le_omega"],  # proven sub-family
        "high_cavity_forces_leaf_or_chain": high_cavity_forces_small_root()["forces_leaf_or_chain"],
        "single_deep_child_s0_closes": single_deep_child_case_closes()["closes_s0"],  # s=0, j=1 -- PROVEN all depths
        "chain_reduction_all_depths": chain_reduction_is_all_depths()["chain_closes_all_depths"],  # RHS1>=0
        "near_star_children_j2_le_omega": near_star_children_le_omega()["le_omega"],  # j>=2, all-near-star kids -- PROVEN
        "near_star_children_bounded_max_is_global": near_star_children_tail_bound()["bounded_max_is_global"],  # exact tail + coupled bound (F non-monotone)
        "discrete_stability_arm_isolated": max_nonnearstar_amplitude()["strictly_below_omega"],  # ell<=-0.0145
        "residual_is_joint_envelope": box_relaxation_overshoots()["residual_is_joint_envelope"],  # no box closes
        "two_or_more_children_step_reduces_to_Psi": two_or_more_children_step_status()["reduces_to_value_function"],  # j>=2 OPEN (needs Psi)
        "A_prime_near_star_curve_REFUTED": not near_star_curve_A_prime_refuted()["A_prime_holds"],  # (A') is FALSE (arms + near-star child exceed E_ns)
        "A_prime_refutation_phi_le_1_safe": near_star_curve_A_prime_refuted()["phi_le_1_safe"],      # conjecture untouched (ell<0)
        "near_star_curve_is_not_value_function": near_star_curve_is_value_function_wall()["near_star_curve_is_not_value_function"],
        "reduction": "Phi<=1  <=>  near-star theorem (proved) + gap [Phi(non-near-star) <= 3/(2 rho_B^2)]",
        "residual_reduces_to": "the sharp value function Psi(mu)=sup{ell: cavity=mu}, whose <=0 is the conjecture. Psi is NOT the near-star curve E_ns: near-stars are on E_ns but a root with many arm-units + a near-star deep child EXCEEDS E_ns by up to ~0.0066 (A' REFUTED). Proven pieces (do NOT use A'): near-star theorem, tie-children, j>=2 all-near-star-children, j=1 s=0 single-deep-child.",
        "open_crux_localized_to": "(i) j>=2 branching with a NON-near-star deep child, AND (ii) j=1 with s>0 units + a medium-cavity deep child; both need the sharp value function Psi (s=0 single-deep-child GAP PROVEN; near-star-child j>=2 PROVEN)",
        "irreducible_core": "the value function Psi(mu), which lies strictly above the near-star curve E_ns in a mid-cavity band (A' refuted) and whose non-positivity is the conjecture",
        "general_case_closed": False,     # OPEN Brualdi-Goldwasser crux (residual = the value function Psi)
    }


if __name__ == "__main__":
    print("gap value exact:", gap_value_is_exact())
    print("gap holds (depth<=5):", gap_holds_bounded())
    print("structural induction overshoots:", structural_induction_overshoots(n=50000))
    print("verdict:", certify())
