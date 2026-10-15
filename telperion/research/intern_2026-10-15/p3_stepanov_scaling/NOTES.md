# Pitch 3: Stepanov's auxiliary polynomial versus the scaling flow (2026-10-15)

Status: a literature and thinking note, not a result. Nothing here is progress on RH. `conjecture1_proved = False`.

AI work (Claude, intern session of 2026-10-15), not reviewed. Every literature claim is tagged CHECKED (with the
source actually read in this session) or FROM MEMORY.

## Verdict first

1. In Bombieri-Stepanov the work is done by one endomorphism with three roles. The q-th power map has the counted
   points as its fixed points, it is additive (so p^mu-th powers form a linear space and give multiplicity sqrt(q) for
   free), and it multiplies pole orders by q. Riemann-Roch, the linear algebra and "zeros <= degree" only support it,
   and each of those has a Spec Z analogue: Arakelov or Connes-Consani Riemann-Roch, Siegel's lemma, the product formula.
2. The fatal step is (a). Z has no global Frobenius. Its points have different residue characteristics, so an additive
   p-power map exists only mod p and only at p (Buium, Borger). The scaling flow's Frobenius is additive only in
   characteristic one (Connes-Consani). The failure already shows in genus 0: nothing over Z plays the role of `T^(q^n) - T`.
3. There is a second, independent wall: the genus is infinite (Connes-Consani: N(1) = -infinity). Bombieri's error
   term (2g+1)sqrt(q) is then empty. There is no extension of constants that raises q while holding g fixed. Pritsker
   gives a concrete form of this: a fixed auxiliary construction that is blind to the zeros cannot be sharp, by
   Littlewood's Omega theorem.
4. The archimedean degree bound, (c), is not the problem for integers. The product formula is an exact zero count.
5. I found one explicit attempt in the literature, van Frankenhuijsen 2008, and it stops exactly at (a). The real
   number-field "polynomial method for primes" is Chebyshev, Gelfond-Schnirelman, Nair and Pritsker, and it stops at
   Chebyshev-type constants. I found no toy problem with RH content.

## 1. Bombieri-Stepanov in one page

Source followed: van Frankenhuijsen's exposition of Bombieri's proof, arXiv:0806.0044, section 3 (CHECKED). Bombieri's
original is Sem. Bourbaki 430 (1973), and Stepanov's is Izv. 1969 (FROM MEMORY; the citations appear in
0806.0044). The formalized version used elsewhere follows Iwaniec-Kowalski chapter 11 (FROM MEMORY).

Setup: C is a smooth projective curve of genus g over F_q, with q = p^(2mu) an even power so that p^mu = sqrt(q). It has
a rational point infinity. L_k = L(k*infinity) has dimension l_k >= k + 1 - g (Riemann-Roch; only the lower bound is used).

Construction. Let s_1, s_2, ... be a basis of L_m ordered by pole order, and let b_i be in L_n. Define

  f(X, Y) = sum_i b_i(X)^(p^mu) s_i(Y),

a function on C x C. It has two restrictions:

- to the diagonal: `f|Delta = sum b_i^(p^mu) s_i`, which lies in L(p^mu n + m);
- to the graph of Frobenius: `f|Phi = sum b_i^(p^mu) s_i^q = (sum b_i s_i^(q/p^mu))^(p^mu)`, which lies in
  L(p^mu n + q m). It is a p^mu-th power because the p-power map is additive in characteristic p, and
  s_i(Frob x) = s_i(x)^q because s_i is defined over F_q.

The steps:

1. **Linear algebra (Riemann-Roch).** If (n+1-g)(m+1-g) > dim L(p^mu n + m), some f is not zero but has
   f|Delta = 0.
2. **Injectivity (pole orders).** If p^mu n < q, then f|Phi = 0 forces f = 0. The terms b_i^(p^mu) s_i^q have pole
   orders in distinct residue classes at scale q, so none can cancel. This is where "Frobenius multiplies degree by q"
   is used.
3. **Free multiplicity.** At an F_q-rational point x we have Frob(x) = x, so f|Phi(x) = f|Delta(x) = 0. Since f|Phi is
   a p^mu-th power, it vanishes there to order at least p^mu.
4. **Degree bound.** A nonzero function with a single pole of order D has at most D zeros. So
   p^mu (N - 1) <= p^mu n + q m. Taking n = sqrt(q) - 1 and m = sqrt(q) + 2g gives **N <= q + (2g+1) sqrt(q) for
   q > (g+1)^4** (0806.0044 Thm 3.6, CHECKED).
5. **Lower bound.** Take the Galois closure C' -> P^1 with group G. Then sum over sigma in G of N(1, sigma) equals
   |G|(q+1). Applying the upper bound to each twisted count gives N >= q - O_g(sqrt q) (Thm 3.7-3.8, CHECKED).
6. **Amplification.** Steps 4-5 hold for every F_(q^n) with g fixed. The bound |N_n - q^n - 1| <= B q^(n/2) for all
   large n, together with Dirichlet approximation on the arguments of the omega_nu, gives |omega_nu| = sqrt(q) (Lemma
   3.1, CHECKED).

Structural inputs, in order of how much they carry:

- (ii) **one Frobenius endomorphism** of the function ring that (ii-a) fixes exactly the points being counted, (ii-b) is
  additive on p-power parts, giving multiplicity for free, and (ii-c) multiplies degrees by q. **This carries the proof.**
  Without (ii-b) you only get trivial bounds such as N <= O(gq). Without (ii-a) the vanishing has to be imposed point
  by point, at a cost of one condition per point, and the method collapses into a tautology.
- (v) **a family of base extensions with the genus fixed**, so that q can be made larger than (g+1)^4 and step 6 can
  amplify. This is an Euler-product property: zeta of C over F_(q^n) is the product of the twists by n-th roots of unity.
- (i) finite-dimensional spaces L(D) with dim >= deg - g + 1, and linear algebra (unknowns > equations gives a nonzero
  solution);
- (iii) zeros <= degree, which is "principal divisors have degree 0";
- (iv) high-order vanishing. Stepanov used Hasse derivatives; Bombieri replaced them with p^mu-th powers.
  0806.0044 p. 4 records that the order-p derivatives turned into the Cartier operator, which is the p-th power (CHECKED).

## 2. Ingredient by ingredient

| ingredient | function field | Spec Z analogue | exists? | source |
|---|---|---|---|---|
| (i) Riemann-Roch spaces | L(D), dimension over F_q >= deg D - g + 1 | H^0(D) = {n in Z : \|n\| <= e^deg D}, a finite set. van der Geer-Schoof: h^0(D) = log sum_n exp(-pi n^2 e^(-2 deg D)), with RR as Poisson summation. Connes-Consani: integer dimension over S[+-1] = {0,+-1}, dim H^0 = ceil((deg D + log 2)/log 3) - 1_L, Serre duality with K = -2{2}. Gillet-Soule arithmetic RR in higher dimension | YES at curve level, but "dimension" is a log-size over a constant field {0,+-1}, not a vector-space dimension over a field | vdG-S math/9802121 Prop. 1 (CHECKED); CC arXiv:2205.01391 Thm 1.1, 3.4 (CHECKED); Gillet-Soule (FROM MEMORY) |
| (i') linear algebra: more unknowns than conditions | kernel of an F_q-linear map | Siegel's lemma with height control (Thue-Siegel, Bombieri-Vaaler 1983); the engine of transcendence proofs | YES | FROM MEMORY |
| (ii-a) Frobenius fixes exactly the counted points | x -> x^q; C(F_q) = Fix(Frob) = Gamma_Frob meets Delta | No endomorphism of Z other than the identity. Each prime p has its own Frobenius, and they live on different residue fields. CC: the counting distribution N(u) comes from the scaling action of R_+^* on the adele class space through the trace formula, with periodic orbits of length log p | NO as a single map. YES as a trace formula (the counts, not the map) | Borger 0906.3146 §2.1, "Z has a unique Lambda-structure, each psi_p is the identity" (CHECKED); CC arithmetic site 1405.4527 Thm 2.6-2.7 (CHECKED) |
| (ii-b) additive Frobenius, free multiplicity | (a+b)^(p^mu) = a^(p^mu) + b^(p^mu) at every point, since all points share the characteristic p | mod p only, separately for each p: Fermat (a^p = a mod p), Buium's p-derivation delta_p(m) = (m - m^p)/p, Borger's psi_p on Lambda-rings (Z[x] toric: psi_p(x) = x^p). Characteristic one: Fr_lambda(x) = x^lambda is an automorphism of R_max^+, additive for every real lambda > 0, but there is no subtraction | PARTIAL, local only: additive at p in char p, at infinity in char 1, never at all places at once | Manin 1312.5160 §2-3 (CHECKED); Borger 0906.3146 (CHECKED); CC 1405.4527 (CHECKED) |
| (ii-c) Frobenius multiplies degree by q | deg Frob^* D = q deg D (pole orders times q) | Scaling by lambda shifts an Arakelov divisor's degree by log lambda (additive, through the infinite component). In char 1, Fr_lambda multiplies tropical exponents by lambda (CC square: Psi(lambda) composition law) | PARTIAL: only in the tropical or characteristic-one model | CC 1405.4527 Thm 4.3 (CHECKED); the additive-shift remark is my own reading |
| (iii) zeros <= degree | principal divisors have degree 0 | product formula: for n != 0 in Z, sum_p v_p(n) log p = log\|n\|. Exact. Liouville's inequality for algebraic numbers | YES (exact) | standard |
| (iv) high-order vanishing | Hasse derivatives / p^mu-th powers | archimedean direction: d/dz on auxiliary functions (transcendence: Gelfond-Schneider, Baker). Arithmetic direction: divisibility by p^k; Buium's delta_p controls order 2 at p, one p at a time; no simultaneous Hasse derivative for all p | PARTIAL | Manin 1312.5160 (CHECKED); transcendence (FROM MEMORY) |
| (v) extensions with genus fixed; q >> g | F_(q^n), same g, zeta twisted by roots of unity | constants of Spec Z-bar are {0,+-1} ("F_(1^2)"). Adjoining mu_n gives Z[mu_n], a new curve whose genus grows with the discriminant, not an extension of constants. CC: the counting distribution has N(1) = -infinity, i.e. the "genus" is infinite | NO | Thas 1507.06480 §3, §4.2 summarizing CC Compositio 2010 (CHECKED) |
| (vi) lower bound via Galois covers | Thm 3.7-3.8 | Not needed. For Q the one-sided bound psi(x) <= x + O(x^(1/2+eps)) already implies RH (Landau's theorem on Dirichlet series with nonnegative coefficients, plus zeta(sigma) < 0 on (0,1), so there is no real singularity in (1/2,1)) | NOT NEEDED | one-sided equivalence stated in 0806.0044 Table 4.1 (CHECKED); the Landau argument FROM MEMORY |
| C x C with an "arithmetic" and a "geometric" coordinate | F_q(C) tensor F_q(C) | Z tensor Z = Z. Borger: Spec Z x_F1 Spec Z := W(Spec Z), big Witt space, infinite dimensional. Haran: F-rings with a genuine arithmetical surface. CC: square of the arithmetic site, Conv>=(N x N). Lorscheid: blueprint product, topologically 2-dimensional | YES in several versions; none carries functions with a degree bound in both coordinates | Borger 0906.3146 §1.2 (CHECKED); Haran 1508.04636 / Compositio 2007 (search abstract, CHECKED); Thas 1507.06480 §4.4 on Lorscheid (CHECKED) |

## 3. Literature findings

Searched (WebSearch and alphaXiv): Stepanov method plus number fields or Spec Z; Bombieri-Stepanov analogue; Buium plus
RH; Borger Lambda-rings plus RH; Connes-Consani Riemann-Roch; Haran F_1; Gelfond-Schnirelman; Diamond-Erdos; Connes'
essay.

1. **van Frankenhuijsen, arXiv:0806.0044 (2008): the one explicit attempt** (CHECKED). It presents Bombieri's proof
   and then, in section 4, tries to transcribe the upper-bound half to Spec Z. Its reasoning: by Table 4.1, the upper
   bound alone suffices for Q, so only the "Frobenius flow" half of Bombieri is needed, not the Galois-cover half. Its
   proposal is a function vanishing to high order at the primes up to x, with the derivative as the generator of the
   shift flow (following Connes and Deninger), framed in Nevanlinna theory. As a candidate it takes
   f(z) = prod_(p<=x) (1 - p z)^[log_p x], whose Nevanlinna counting function N_f(0,1) is exactly psi(x). It stops in
   three places, in its own words:
   - "We do not know what the analogue of the choice b_i = a_i^(p^mu) could be." This is ingredient (ii-b).
   - "There is no diagonal and we have to force the vanishing of f at the primes in an artificial manner." This is
     (ii-a).
   - "As a consequence, we do not know how to bound the Nevanlinna height (i.e., the degree) of this function." This is
     (c), but it arises only because of the first two.

   It also says (p. 4) that the original Bombieri "uses functions on C x C, again precluding a direct translation", and
   speculates that a function vanishing to high order at the first N primes with bounded degree "would already imply
   the Riemann hypothesis".
2. **Bombieri, by personal communication quoted in 0806.0044 p. 4** (CHECKED as a quotation). The derivative proof
   worked only over the prime field because of "the obstruction arising from iterating the connection p times". Order-p
   derivatives became the Cartier operator, which is the p-th power. So Hasse derivatives and the additive Frobenius are
   one ingredient in characteristic p. Over Z they come apart: the archimedean derivative exists, the additive power map
   does not.
3. **Connes, "An essay on the Riemann Hypothesis", arXiv:1509.05576** (CHECKED). It describes the Riemann-Roch strategy
   (Weil, Mattuck-Tate, Grothendieck) and the arithmetic and scaling sites. Stepanov or Bombieri does not appear in the
   pages returned. The CC program has always aimed at the intersection-theory route.
4. **Connes-Consani, Riemann-Roch for Spec Z-bar, arXiv:2205.01391** (CHECKED). Integer dimensions over S[+-1], with
   H^0(a{infinity}) = integers in [-e^a, e^a]. The only base is {0,+-1}: no Frobenius acts on it, and the dimension
   counts base-3 digits. This supplies ingredient (i) and nothing toward (ii).
5. **Borger, arXiv:0906.3146** (CHECKED). F_1 := Z with its unique Lambda-structure, all psi_p = id; RH and Weil's
   proof are named as motivation. Spec Z x_F1 Spec Z must be W*(Spec Z). Curves of genus >= 2 over Z[1/M] have no
   Lambda-structure (§2.9). Separated Lambda-schemes of finite type have polynomial point counts P(q) when
   q = 1 mod N (§6), so their zetas carry no RH content.
6. **Buium and Manin, "Numbers as functions", arXiv:1312.5160** (CHECKED). The p-derivation on Z is the Fermat quotient
   (m - m^p)/p, taken with respect to the identity lift; arithmetic jet spaces are one-prime objects. Section 3 asks
   whether a global version with delta_p for all p exists; Lambda-rings answer it on Z-algebras. Neither Manin nor the
   abstracts I saw attempt a zero-count or RH argument with these.
7. **Number-field polynomial method for primes** (CHECKED unless marked):
   - Gelfond-Schnirelman (1936). For P in Z[x] of degree n, lcm(1..n+1) * |int_0^1 P| >= 1, which gives
     psi(n+1) >= -log ||P||_[0,1]. The PNT would need integer Chebyshev constant t_Z([0,1]) = 1/e. Gorshkov (1956)
     showed this is impossible; 0.4213 < t_Z([0,1]) < 0.4232 (Pritsker, arXiv:1307.5361 §1).
   - Nair and Chudnovsky: multivariate weighted Vandermonde, int_1^x psi >= 0.99035 x^2/2.
   - Pritsker (Canad. J. Math. 57, 2005), Prop. 1.3: for any fixed polynomial weight w the constant satisfies B(w) < 1.
     **The reason is that the method's error term O(x log^2 x) is "too good"**, and would contradict Littlewood's
     int_1^x psi - x^2/2 = Omega_+-(x^(3/2)).
   - Chebyshev-Sylvester schemes (Gantumur arXiv:2512.02466 survey): the best classical constants are about 0.9576 and
     1.0435.
   - Diamond-Erdos (Enseign. Math. 26, 1980): constants arbitrarily close to 1, but the proof uses estimates equivalent
     to PNT (2512.02466 §8).

   This tradition is the honest number-field form of "auxiliary object, vanishing at all primes, degree bound". It uses
   the Euler product (Lambda = mu * log), so it passes the project's Davenport-Heilbronn test. It is quantitatively
   capped below PNT.
8. **Haran** (Compositio 2007, "Non-additive geometry"; arXiv:1508.04636). It builds an arithmetical surface over an F
   base aimed at Weil's intersection argument (CHECKED from search abstracts only; not read). Haran 1989 (LMS LN 153)
   frames the needed inequality as a two-dimensional Riemann-Roch (CHECKED as quoted in Thas 1507.06480 §1). Neither is
   a Stepanov approach.
9. **Smirnov, "Hurwitz inequalities for number fields"** (St. Petersburg Math. J. 4, 1993). It is cited in Thas as
   "perhaps the only work" on intersection theory in characteristic one, approximating Riemann-Hurwitz for maps
   Spec Z -> P^1/F_1 (CHECKED as a citation). Its target is abc, not RH (FROM MEMORY).
10. **Lean formalization**: github.com/math-inc/RiemannHypothesisCurves formalizes the Bombieri-Stepanov method (after
    Iwaniec-Kowalski ch. 11) for hyperelliptic curves (CHECKED from the repository page; whether it is sorry-free was
    not verified).
11. **Not found**: any paper that runs Stepanov or Bombieri with the scaling flow, with Buium's delta_p, with
    Lambda-structures, or in characteristic one, for zeta or for Dedekind zeta. Treat this as absent from a limited
    search, not as proved absent.

Toy cases asked about:

- Dirichlet L-functions over F_q(T): RH is the Weil bound for character sums. Stepanov's method proves it elementarily
  (W. M. Schmidt, LNM 536, 1976; cited in 0806.0044, content FROM MEMORY). This is still a function field.
- Selberg zeta of a compact hyperbolic surface: RH holds up to finitely many real exceptional zeros (small Laplace
  eigenvalues), by self-adjointness of the Laplacian. That is the Hilbert-Polya route, and I know of no auxiliary-polynomial
  proof (FROM MEMORY).

## 4. The fatal point

**(c), the archimedean degree bound, is not fatal.** For integers the zero count is exact: sum_p v_p(n) log p = log|n|.
All of transcendence theory runs on this together with Siegel's lemma. van Frankenhuijsen's failure to bound a
Nevanlinna height is downstream. It happens because the vanishing at primes had to be imposed by hand, as a product over
p, instead of coming out of the construction.

**(b) as posed, the lower bound through covers, is not needed for Q.** The one-sided bound psi <= x + O(x^(1/2+eps))
already implies RH (Table 4.1 of 0806.0044). But (b) has a deeper form that is fatal on its own: the
**genus is infinite**. Bombieri's error term is (2g+1) sqrt(q) and his regime is q > (g+1)^4. Both need g finite and
fixed while q grows, which in the function-field case is supplied by the constant-field extensions F_(q^n). Spec Z-bar
has constants {0,+-1} and no constant extensions. Its counting distribution N(u) = u - d/du(sum_rho u^(rho+1)/(rho+1))
+ 1 has N(1) = -infinity (CC, as summarized in Thas 1507.06480 Thm 3.1, CHECKED). Every zero contributes to
psi(x) - x at every scale.

Pritsker's Prop. 1.3 is the concrete form of this. Any auxiliary construction whose error is controlled without
reference to the zeros has an error term that is too small to be true, so its main-term constant must be strictly below
the truth. In Bombieri's construction, Riemann-Roch builds g in, so the auxiliary function "knows" the zeros. An
auxiliary object for Z would need a scale-dependent genus. The project's earlier work (`telperion/explorer/src/index.html`,
"The genus moves with the scale", an e9-session result, AI work, not reviewed) found that for zeta the degree and the
filtered genus grow at the same scale, so the regime "q beyond g" never arrives. This note agrees with that and adds the
literature behind it.

**(a) is the sharpest point, and it comes first.** Stepanov's free multiplicity requires one map that is additive at
every point being counted. That holds over F_q because all points of C have residue characteristic p. The points of
Spec Z have residue characteristics 2, 3, 5, ... and also characteristic one at infinity. So:

- The only endomorphism of Z is the identity. Borger turns this into a definition: F_1 = Z with every psi_p equal to id.
- Buium's delta_p and Borger's psi_p are additive only mod p, and give information only at p. Commuting lifts for all
  p exist on Z-algebras such as Z[x] (toric, psi_p(x) = x^p), not on the curve Spec Z itself.
- The scaling flow gives a Frobenius Fr_lambda(x) = x^lambda that is additive for all lambda > 0, but only on
  idempotent (characteristic-one) semirings. There is no subtraction there, so Bombieri's step 1 (a nonzero f whose
  restriction to the diagonal cancels to 0) has no direct meaning. On the adele class space the scaling acts by
  automorphisms of a group, not as a degree-multiplying endomorphism of a function ring with finitely many fixed points.

The failure already shows at genus 0, before Riemann-Roch or the genus comes in. For P^1 over F_q, Stepanov reduces to
the identity T^(q^n) - T = product of monic irreducibles of degree dividing n. Its degree, q^n, is known from the
Frobenius alone, so the prime polynomial theorem drops out with error 0 (Example 3.5 of 0806.0044 is the n = 1 case,
CHECKED). The Z analogue would be an integer whose size is computable without the primes and which is divisible by every
p <= x, a "Frobenius minus identity". The only exact candidate is lcm(1..x) = e^(psi(x)), which is a tautology. The best
real substitute is Chebyshev's binomial C(2n, n). By Kummer and Lucas, which is the Frobenius congruence
(1+x)^p = 1 + x^p mod p in the Lambda-ring Z[x], every p in (n, 2n] divides it, with multiplicity exactly 1, at height
2n log 2. That gives theta(2n) - theta(n) <= 2n log 2, a constant of 1.386 against the truth of 1. Without free
multiplicity there is no sqrt gain. Without the sqrt gain the method stays at Chebyshev constants, and Section 3 shows
that is where the whole tradition stays.

**Known partial substitutes**, none of which repairs (a):

- simultaneous Frobenius congruences in Lambda-rings (they give Chebyshev);
- p-derivations (they give order-2 information at one p);
- the characteristic-one Frobenius (additive, but with no cancellation);
- the CC trace formula (it gives the fixed-point counts, but as a distribution, not through a map on functions).

Is there a single fatal point? (a) breaks the mechanism and (b-deep) breaks the regime. If one had to be named, (a): it
blocks the construction before any counting starts, and it shows up even in genus 0.

## 5. Most promising toy problem

There is none with RH content. The candidates, from more to less useful:

1. **Genus-0 Stepanov over Z, i.e. the Gelfond-Schnirelman/Nair/Chebyshev framework read as an auxiliary-polynomial
   method.** The concrete question: do auxiliaries built only from Lambda-structure (products and integrals of
   polynomials in the toric Lambda-ring Z[x_1..x_r], with divisibility coming from the psi_p congruences, plus Buium
   delta_p for multiplicity 2) beat the known ceilings? The known ceilings are t_Z([0,1]) > 0.4213 in one variable,
   0.99035 for Nair-Chudnovsky, and B(w) < 1 for any fixed weight (Pritsker). This is exact-integer and certificate-shaped,
   which fits Telperion. The expected answer is no: factorial ratios and integer Chebyshev polynomials already use all
   the Kummer and Lucas structure, and Pritsker's argument rules out every fixed scheme. Its value would be confirming
   wall (a) numerically. It cannot prove anything about RH.
2. **Bombieri's argument in characteristic one.** Take a tropical curve with a Riemann-Roch theorem, such as CC's
   periodic orbits of the scaling site (FROM MEMORY: CC, "Geometry of the scaling site", proves RR there) or Baker-Norine
   graphs. Try to run steps 1-4 with Fr_lambda as the Frobenius and "maximum attained twice" as vanishing. It would test
   whether the cancellation step has a tropical substitute. These curves have no RH content, and I found no one who has
   tried this.
3. **F_1 objects whose zeta is known.** Deitmar and Borger finite-type schemes have polynomial point counts, so RH is
   automatic and Stepanov proves nothing new. Selberg zeta is settled spectrally, with no F_1 or Frobenius structure to
   test. F_q[T] Dirichlet L-functions are already done by Stepanov (Schmidt).

Recommendation: do not open a Stepanov line for zeta. If anything, run toy 1 once as a numerical certificate of wall (a).
Its predicted outcome is negative, so it only makes sense if the negative control is wanted.

## References

- E. Bombieri, Counting points on curves over finite fields (d'apres S. A. Stepanov), Sem. Bourbaki 430 (1973). FROM MEMORY (cited in 0806.0044).
- S. A. Stepanov, On the number of points of a hyperelliptic curve over a finite prime field, Izv. 33 (1969). Cited in 0806.0044.
- W. M. Schmidt, Equations over Finite Fields: An Elementary Approach, LNM 536 (1976). Cited in 0806.0044.
- M. van Frankenhuijsen, The Riemann hypothesis for function fields over a finite field, arXiv:0806.0044. CHECKED.
- A. Connes, An essay on the Riemann Hypothesis, arXiv:1509.05576. CHECKED.
- A. Connes, C. Consani, The Arithmetic Site, arXiv:1405.4527 (C. R. 2014). CHECKED.
- A. Connes, C. Consani, Riemann-Roch for Spec Z, arXiv:2205.01391. CHECKED.
- A. Connes, C. Consani, Schemes over F_1 and zeta functions, Compositio 146 (2010). Via Thas, CHECKED secondhand.
- G. van der Geer, R. Schoof, Effectivity of Arakelov divisors and the theta divisor of a number field, arXiv:math/9802121. CHECKED.
- A. Borisov, Convolution structures and arithmetic cohomology, arXiv:math/9807151. Cited in vdG-S, not read.
- H. Gillet, C. Soule, arithmetic Riemann-Roch / arithmetic intersection theory. FROM MEMORY.
- J. Borger, Lambda-rings and the field with one element, arXiv:0906.3146. CHECKED.
- A. Buium, Arithmetic Differential Equations, AMS Surveys 118 (2005). Via Manin and Borger, CHECKED as a citation.
- Yu. I. Manin, Numbers as functions, arXiv:1312.5160. CHECKED.
- S. Haran, Non-additive geometry, Compositio 143 (2007); New foundations for geometry, arXiv:1508.04636. Abstracts only.
- K. Thas, A taste of Weil theory in characteristic one, arXiv:1507.06480. CHECKED.
- A. L. Smirnov, Hurwitz inequalities for number fields, St. Petersburg Math. J. 4 (1993). Citation only.
- I. E. Pritsker, The Gelfond-Schnirelman method in prime number theory, arXiv:1307.5361 (Canad. J. Math. 57, 2005). CHECKED.
- T. Gantumur, An expository review of the Chebyshev-Sylvester method, arXiv:2512.02466. CHECKED.
- H. G. Diamond, P. Erdos, On sharp elementary prime number estimates, Enseign. Math. 26 (1980). CHECKED secondhand (2512.02466, search excerpts).
- E. Bombieri, J. Vaaler, On Siegel's lemma, Invent. Math. 73 (1983). FROM MEMORY.
- math-inc/RiemannHypothesisCurves (Lean 4, Bombieri-Stepanov for hyperelliptic curves). Repository page CHECKED.
- Project context: telperion/docs/RH_CLOSURE_SHAPE_2026-10-11.md; RH_F1_HODGE_INDEX_FRONTIER_2026-08-30.md;
  RH_F1_SURFACE_BLUEPRINT_2026-08-30.md; telperion/explorer/src/index.html ("The genus moves with the scale");
  telperion/research/rr_square/RR_SQUARE_STATEMENT_2026-10-12.md.
