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
