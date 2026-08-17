# Tier-B research targets: a non-separable-AND-integral certificate

The Brualdi-Goldwasser crux needs a certificate that is simultaneously **collective / non-separable**
(the per-node factors `{0.103, 1.53, 8.91}` multiply to 1 by cancellation, not term-by-term) and
**integral** (the exact-1 locus is a discrete/arithmetic event; the continuum overshoots to 1.00046).
p-adic tools are integral-but-separable; Hodge-Riemann is collective-but-smooth; the crux lives at their
empty intersection. This file inventories mathematical frameworks that DO marry the two -- each is a place
where **an archimedean/analytic quantity carries an intrinsic arithmetic gap or discreteness**, exactly the
`sup=1, reached only at resonances` structure. None is known to close BG; each is a research target with a
concrete telperion-testable first probe. `conjecture1_proved = False`.

Ranked by directness of the structural match.

---

## 1. Mahler measure & the Lehmer gap  (strongest structural match)

**Mechanism.** The Mahler measure `M(P) = prod max(1,|root|) = exp(int_torus log|P|)` is an ARCHIMEDEAN
quantity, yet `M(P)=1` **iff** `P` is cyclotomic (Kronecker) -- a pure INTEGRALITY -- and by Lehmer,
`M(P)` is either `1` or `>= 1.176...` (bounded away). "`=1` or a gap" is precisely BG's "density `=1` at
the tie or strictly below." Non-separable: `M` is a global product/integral over all roots.

**BG connection.** Find a polynomial whose Mahler measure `= 1` iff tie: the matching polynomial, the
characteristic polynomial of `D+iA`, or the amplitude polynomial. The 23-adic resonance and the
"continuum overshoots" both fit the cyclotomic/Lehmer-gap picture.

**First probe.** Compute `M(matching_polynomial)` and `M(det(xI-(D+iA)))` for near-stars `N(0,s)`; is it
`1` (roots on the unit circle / cyclotomic) at `s=5` and gapped-away off it?

**First probe RESULT (`mahler.py`, `MahlerLehmerProbe`): NEGATIVE for these two carriers.** Over
`s=2..8` both Mahler measures grow strictly monotonically (`M(matching) ~ s+1`: 3,4,5,6,7,8.05,9.20;
`M(D+iA)`: 24,108,432,1620,...) and the tie `s=5` is unremarkable -- no `M=1`, no cyclotomic factor,
no gap re-crossing. Reason: the raw Mahler measure of these polys is a spectral-radius growth,
SEPARABLE over roots -- the archimedean coordinate PROOF_STATUS dead-end #2 already refuted. The
Lehmer `=1-or-gap` SHAPE is the right analogy but the matching / `D+iA` polys are the wrong CARRIER;
BG's resonance appears only under the `(64/621)^n` normalization a bare Mahler measure lacks. Live
frontier: a Mahler measure of an *amplitude-derived* polynomial whose cyclotomic locus is the 23-gate.

## 2. Ehrhart theory / lattice-point counting  (integral by construction; telperion has `ehrhart`)

**Mechanism.** Ehrhart quasi-polynomials count lattice points in dilated polytopes -- INTEGER-valued with
an arithmetic quasi-period; the continuous VOLUME and the integer COUNT differ by boundary/error terms
("continuum overshoots, integers obey"). Ehrhart-Macdonald reciprocity is a discrete duality. The polytope
couples all coordinates (non-separable).

**BG connection.** The matching numbers `m_k` and the amplitude denominators live on an integer lattice;
express the tie as a lattice-point coincidence (a dilated matching/independence polytope hitting a lattice
point exactly). `ehrhart.is_quasi_polynomial` / `minimal_period` are already in telperion.

**First probe.** Compute the Ehrhart data of the matching (or fractional-matching) polytope of `N(0,s)`;
does the tie appear as a quasi-polynomial identity / a period-`23` phenomenon?

**First probe RESULT (`ehrhart_bg.py`, `EhrhartBGProbe`): NEGATIVE -- and it's a theorem, not a data
artifact.** The exact t-dilate count `L_P(t)` (tree-DP, validated vs brute force) has minimal Ehrhart
period **1** for every near-star s=2..6: `L_P` is a genuine POLYNOMIAL (N(0,5): degree 10, leading coeff
= volume 1627/518400). No period 11, no period 23. Reason: a tree is BIPARTITE, so its matching polytope is
INTEGRAL (Edmonds/Birkhoff); the Ehrhart period is the lcm of vertex-coordinate denominators, and integral
vertices give 1 -- so 23 is structurally unreachable through ANY tree matching polytope. Redirects to the
carrier `ehrhart.py`'s docstring already names: a NON-matching polytope with `23 | vertex denominators`
(cavity `m = 3/23`, or the signed `D-N` lattice count along `n = 11k+1`). `Phi^11 = 1` holds exactly at the
tie s=5 but `L_P` is blind to it.

## 3. Frustration-free Hamiltonians / MPS parent-Hamiltonian gap methods  (the collective-cancellation's exact name)

**Mechanism.** A frustration-free ground state realizes a GLOBAL minimum that is NOT a sum of
locally-minimized terms -- literally "no sum of non-positive local terms," the councils' verified
obstruction. Knabe/martingale/finitely-correlated (MPS) methods bound the global energy from local data
DESPITE non-decomposability. The exact ground state is an integer-bond-dimension tensor (integrality).

**BG connection.** Realize `Phi^11` (the dimer/monomer-dimer model on the tree) as a frustration-free
ground-state energy; bound it by a parent-Hamiltonian / gap argument. The tie is a critical (gapless)
point; `sup=1` is the closing of the gap in the unimodular limit.

**First probe.** Build the dimer-model parent Hamiltonian on the tree; does `Phi^11 <= 1` follow from a
frustration-free lower bound (Knabe-type) with equality only at the gapless tie?

**First probe RESULT (`frustration_free.py`, `FrustrationFreeGapProbe`): REFRAME + OBSTRUCTION.** The
framing is CORRECT and captured: the monomer-dimer ground state is an INTEGER-bond-dimension (=2) MPS
(verified -- the bond-dim-2 transfer reproduces the matching partition function), and `Phi^11 <= 1` is a
FRUSTRATION-FREE POSITIVITY `E_0 = -log Phi^11 >= 0` -- a global energy, NOT a sum of local non-positive
terms (exactly dead-end #1's shape). BUT the Knabe local-gap -> global route to a UNIFORM certificate is
OBSTRUCTED: the transfer gap `1 - D` closes not only at the isolated tie (near-star `D=1` at s=5) but along
the ENTIRE tie-recursive family `hub + k*N(0,5)` (`D -> 1` as `k -> inf`: gaps 0.111, 0.057, 0.036, ...,
0.0044 at k=20). Gapless on a positive-density set -> no uniform Knabe threshold -- the same archimedean
wall `transfer_tail` found (`sup D = 1`), now in parent-Hamiltonian language. Net: #3 supplies the
POSITIVITY / collectivity of the `<=` half, and `resonance_carrier.py` supplies the EQUALITY locus
(23-adic); together they ARE PROOF_STATUS's decomposition (open `<=` crux + 23-gate equality set). Neither
closes BG. conjecture1_proved = False.

**FOLLOW-ON (`family_martingale.py`, `TieRecursiveMartingaleCertificate`): the NON-uniform bound DOES close
the family the uniform one couldn't.** Where the Knabe uniform bound fails (the tie-recursive `D -> 1`
family), a family-adapted MARTINGALE argument succeeds: rooted at the hub, `prod a_v = a_root(k) *
(per_block)^k` with `per_block = (23/18)(3/2)^5 = 621/64`, so the per-block transfer factor
`F = ((64/621)*per_block)^11 = 1` EXACTLY (each block is a tie -> zero log-drift = martingale conservation).
All k-dependence is then the boundary `a_root(k) = 1 + 3k/(23(k+1))`, monotone and bounded by `26/23`
(= 1 + the `3/23` cavity fixed point), giving `Phi^11_hub(k) < (64/621)(26/23)^11 = L ~ 0.397 < 1` -- the
integer inequality `64*26^11 < 621*23^11`. Hub = argmax for `k >= 3`; `k = 1,2` are base cases. So
`Phi^11 < 1` STRICTLY on the whole canonical near-1 family, by a martingale + bounded boundary + integer
ceiling -- the strongest positive statement on the hardest known family. Family-adapted (F=1 is special to
tie blocks); general competitor extremality over ALL trees stays open. conjecture1_proved = False.

**GENERALIZATION (`mixed_block_martingale.py`, `MixedBlockMartingaleCertificate`): the per-block transfer
factor organizes ALL single-hub families.** One exact formula `Phi^11_hub = (64/621) a_hub^11 prod_b F_b`
(verified vs `phi11_rooted`) with `F_b = (64/621)^{n_b} alpha_b^11` the per-block factor. TRICHOTOMY:
`F_b < 1` subcritical (interior max), `F_b = 1` marginal, `F_b > 1` supercritical (would blow `Phi^11_hub`
up -> BG violation). **No supercritical block exists** in the census up to `n_b = 11`, so `F_b <= 1` is a
NECESSARY condition for BG, verified. Marginality first appears at `n_b = 11` and is the tie (`mu = 3/23`) --
the SAME 23-gate (`F_b=1 => alpha_b = (621/64)^{n_b/11}` rational => `11 | n_b`), tying this to
`resonance_carrier`. The near-star is RECOVERED as the length-2 ARM block's family (`F = 486/529`, the
fractal-tail factor): its interior maximum is `Phi^11_hub = 1` EXACTLY at `k = 5` (the tie), the unique
single-hub family touching 1. Unifies the tie-recursive marginal family and the near-star tie under one
transfer factor. Does NOT prove BG (`F_b <= 1` for ALL blocks, interior maxima, multi-level trees, non-hub
roots open). conjecture1_proved = False.

## 4. Cluster algebras / Y-systems & the Laurent-positivity phenomenon  (the cavity's natural home)

**Mechanism.** Cluster mutations are subtraction-free rational maps whose iterates are Laurent polynomials
with INTEGER, POSITIVE coefficients (Laurent phenomenon) -- global positivity (non-separable seed) married
to integrality. Y-systems exhibit Zamolodchikov PERIODICITY: finite-type points are exact integral
resonances.

**BG connection.** The cavity recursion `m_v = z/(1+z*S)` is subtraction-free -- is it a cluster/Y-system
mutation? The tie as a finite-type / periodic point; the integer-Laurent structure as the certificate of
the collective cancellation.

**First probe.** Test whether the cavity/amplitude recursion is a Y-system mutation and whether it is
periodic (finite type) exactly at the tie parameters.

## 5. Moment-cone extremality (atomic = integral)  (connects to the new `gibbs_free_energy` layer)

**Mechanism.** Valid matching measures satisfy Hankel positivity -- non-separable (the whole moment
sequence). The EXTREME POINTS of the moment cone are FINITELY-ATOMIC measures (integrality: finite
support, integer atom count). Extremality of a measure = a rank condition on its Hankel matrix.

**BG connection.** Is the tie's matching measure an EXTREME point of the moment cone (a minimal-rank Hankel
/ finitely-atomic measure)? Ties as the atomic extremizers of the free-energy variational problem.

**First probe.** Compute the Hankel rank of the near-star matching measure (from `gibbs_free_energy.
matching_measure`); is the tie's measure minimally-atomic among competitors?

## 6. eta-invariant / spectral flow of the FAMILY  (refined topological, after Levinson failed)

**Mechanism.** The APS eta-invariant is a zeta-REGULARIZED spectral asymmetry -- real-valued, but its
INTEGER JUMPS are spectral flow (an index): analytic married to integral. The 1D spectral-shift (Levinson)
was probed and does NOT localize the tie (flat Friedel phase); the eta of the parametrized family
`{D+iA(s)}` or an equivariant index is a distinct object.

**BG connection.** The tie as an eta-jump / APS integer of the near-star family.

**First probe.** Compute the eta-invariant / spectral flow of `D+iA(s)` across `s=5` (with the caveat that
the naive Levinson realization already came back negative).

---

## The unifying meta-target

Every candidate is a theorem of the form **"an analytic invariant is either at an exact resonance value or
strictly bounded away, and the resonance is arithmetic"**: Lehmer's `=1`-or-gap, Ehrhart's volume-vs-count,
the frustration-free gap, Y-system periodicity, moment-cone atomicity, eta integer-jumps. BG's
`sup density = 1, reached only at integer resonances` IS such a theorem. **The Tier-B target is to find the
framework whose native gap/discreteness theorem specializes to the BG resonance -- and Mahler/Lehmer (1) is
the closest structural twin, while Ehrhart (2) and frustration-free (3) are the most directly buildable in
telperion.** conjecture1_proved = False.

## REDIRECT RESULT (`resonance_carrier.py`): the carrier is the 23-adic absolute value

Probes #1 and #2 both came back negative FOR THE SAME REASON, and both point to the same object. #1's
Lehmer `=1`-or-gap is absent archimedean-ly (`sup D = 1` is *approached*, no gap); #2's `23 | denominator`
is absent in the matching polytope (bipartite -> integral, Ehrhart period 1). The gap they both want lives
at **p = 23**: with `delta(T) = v_23(Phi^11) = 11 v_23(prod a_v) - n` (integer),
`|Phi^11|_23 = 23^(-delta)` is a discrete set with a **multiplicative gap of 23 around 1** -- the Lehmer
SHAPE (#1) realized by literal `23`-divisibility (#2), in one object. VERIFIED (`ResonanceCarrierCertificate`):
the adelic **product formula** `prod_v |Phi^11|_v = 1` ties the archimedean `Phi^11 <= 1` to the 23-adic
size; the tie `N(0,5)` is the unique `|.|_23 = 1` point while off-tie near-stars sit at `|.|_23 = 23^n` (gap
WIDENS); and this yields **categorical strictness** `Phi^11 != 1` on `11 ∤ n` (arithmetic, no size estimate).
Net: BG SEPARATES into (a) `11 ∤ n` -- closed 23-adically given the `<=` half, and (b) `11 | n` -- the
irreducible core (open sporadic-tie danger + the `<=`/collective-cancellation half). A reframing + verified
identities + a half-domain strictness lemma; NOT a proof. conjecture1_proved = False.
