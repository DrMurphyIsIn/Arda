# Where the order SIX comes from in the OpenAI QRH paper

Source: `qrh_paper1_paper.tex` (16,677 lines). Line numbers refer to that file.
"PAPER:" marks what the text states. "INFERENCE:" marks my own reading.

## Q1. Origin of the sextic order

### Where the sextic symbol is first introduced

- l.628-631 (Section 4.1): "the six roots of unity remain distinct in that
  field. Define the sextic symbol chi_p(a)=(a/p)_6 to be the unique sixth root
  of unity satisfying chi_p(a) = a^{(P-1)/6} (mod p)". The only structural
  justification given is that q_p = 1 (mod 6) for p outside S.
- l.637-638: "The square chi_c^2 is the cubic symbol." The cubic symbol of the
  theta function is recovered as chi^2, l.1903-1904: "for a good prime p, one
  has (x/p)_3 = chi_p(x)^2".
- l.4805-4808 (sextic sieve): "At each good prime the sextic residue character
  has exact order six, since the residue multiplicative group is cyclic."
- The probe twists the completed index A = c n^3 by the FIRST power of the
  sextic symbol, l.3353-3354: Psi_{m,s,eta}(a) = eta(a) Xi(a)^{-1} R(a,s) chi_a(m),
  and l.3387-3390 (T_{m,s,eta}). The auxiliary character xi at S is also chosen
  with "order divides six", l.3338-3343.

### Where the cubic part enters

PAPER: the theta input is cubic. l.1895-1900: "a smooth cubic theta function
theta on H^3 with theta(gw)=kappa(g)theta(w), kappa = (c/a)_3". Its Fourier
coefficients are cubic Gauss sums, l.1992-2001:
d_I(lambda^{-3} n b^3) = 3^{5/2}|b| g~_3(n), and the conversion
g~_3(n) = chi_n(lambda)^{-2} gamma_2(n), i.e. the theta coefficient is the
SQUARE of the sextic Gauss sum (gamma_2, cubic). The completed index is c n^3
(l.204-209, l.1706-1712): the cube is the Patterson/Kubota structure.

### Where the quadratic part is forced

PAPER, reflection: Proposition "Completed cubic reflection", l.1783-1789,
local column factor after reflecting a sextic twist of exponent j_p:
B_p(x) = chi_p(x)^{-j_p-2} (j_p != 0,4). A row prime entering with exponent 1
therefore reflects to chi_p^{-3}, a QUADRATIC character. The paper states this
explicitly, l.2848-2856: "The reason for the quadratic sieve is already visible
for squarefree rows. ... Every prime of R enters reflection with exponent one,
so for mu = u lambda^k n b^3 its column factor gives
chi_R(lambda^4 mu)^3 = chi_R(u lambda^{k+4})^3 chi_R(nb)^3."

PAPER, the quadratic large sieve is then the tool for the reflected energy:
l.2638-2652: "The next estimate bounds the quadratic character left by
reflection on a squarefree factor times a cube. ... the quadratic kernel
chi_a(b)^3 satisfies sum_a |sum_b c_b chi_a(b)^3|^2 << (UV)^eps (U+V) sum|c_b|^2.
This is Goldmakher-Louvel's quadratic large sieve." The family conditions are
checked with the square-class bicharacter R (l.2652-2671), itself computed from
the quadratic Gauss phase Gamma(c) (Lemma "Quadratic four-term formula",
l.838-870, and "Sextic reciprocity and the fixed Gauss phase", l.934-968, where
G(c) = conj(chi_c(4)) Gamma(c) and gamma_1 gamma_2 = mu alpha G).
l.2866-2871 gives the payoff: at equal lengths the reflected energy is
Z^{eps}(Z+UB)UB/(UB^2) << Z^{1+tau+eps}, the "Z^{1+eps} needed in the balanced
argument" (l.1653-1655).

### Mechanism in one paragraph

PAPER + INFERENCE. The order is 6 = lcm(2,3) and the two factors have distinct
sources. The 3 is the cubic theta function: the coefficient at the completed
index c n^3 is the cubic Gauss sum gamma_2(c) = (sextic Gauss sum)^2, and the
reflection formula composes the probe twist chi^j with this cubic coefficient
to give chi^{-j-2} on the dual side (l.1783-1789). The 2 is forced on the
REFLECTION side: with the probe twist taken as the sextic generator j = 1, the
reflected kernel is chi^{-3}, the quadratic symbol, and only for a quadratic
kernel is a large sieve with the clean bound (U+V) available (Goldmakher-Louvel,
l.2644-2650). This is what gives the reflected row energy Z^{1+eps} at balanced
lengths (l.2866-2871). INFERENCE: with a cubic twist j = 2 the reflected kernel
would be chi^{-4} = chi^2, cubic again, and the available cubic/sextic sieve
(Heath-Brown, BGL, Lemma l.4707-4716) carries the extra term (KD)^{2/3}; at
U B ~ Z that term gives Z^{4/3}/B, which exceeds Z^{1+eps} at B = 1 and would
destroy the balanced low estimate. Thus the sextic twist is exactly the twist
that the cubic Gauss-sum reflection turns into a quadratic character
(chi = chi^{-2} * chi^3: inverse cubic times quadratic). The paper never states
this reasoning as a design choice; it states only the consequence (l.2848).

## Q2. Remarks on other orders

Searches for "quartic", "biquadratic", "Kazhdan", "generaliz", "other fields",
"Q(i)", "sqrt(-1)", "n-fold", "metaplectic cover", "Gaussian integer",
"arbitrary order" return NOTHING relevant. "fourth" occurs only as "fourth
moment" / "fourth-power residue symbol" (the chi^4 label inside the sextic
machinery, e.g. l.9272, l.9979). "higher" occurs only in citations: "the
higher-order norm recursion of Blomer, Goldmakher, and Louvel" (l.134) and "for a
higher-order-character density application [BGL]" (l.156-157). "metaplectic"
occurs once, l.121: "Kubota's metaplectic theory and Patterson's cubic theta
series provide the automorphic setting." "Eisenstein" refers only to Eisenstein
integers/units (l.139, l.1796). There is no discussion of why cubic rather than
quadratic or quartic theta functions, and no discussion of other base fields.
The only field-specific facts used are: F = Q(sqrt(-3)) contains mu_6 (l.677-679,
l.5508-5510), every ideal is principal (l.577-580), and q_p = 1 (mod 6)
(l.627-628).

## Q3. Constants of the final exponent system (Section 20, l.15495+)

Format: constant -> origin (line) -> would change with k? (k = symbol order)

- z = 1/6 (contour/residue point) -> pole of zeta_F^S(6z) from the a-sum
  q_a^{-6z} over rows H = u a^6 (l.3758-3760, l.3806-3810, l.4045, l.6221-6243,
  "the residue of zeta_F^S(6z) at 1/6 is one sixth of the residue of zeta_F^S(v)",
  l.6270-6271). SEXTIC: becomes z = 1/k.
- q_p^{-5/6} and Z^{-ell/6} (principal normalizer S_i, A_T) -> the slot factor
  (q_p/P_i)^{z-1} evaluated at the residue point z = 1/6 (l.15562-15583,
  l.15599 "at w=1, z=1/6"). SEXTIC: would read q_p^{1/k-1}, Z^{-ell/k}.
- h/6 in C(s) = s + l_x/2 - 1 + h/6 (l.6140-6150, l.8641, l.8794) and 1/6 in
  "X^{1/3} Z^{s-5/6} Z^{ell/6} = Z^{C(s)}" (l.6299-6300) -> same pole at z = 1/6.
  SEXTIC.
- 2/3 in C_I(s) = s - 2/3 (l.190, l.5547) -> l_x/2 - 1 + h/6 at l_x = h = 1/2
  (l.6316 "Take l_x=l_y=h=1/2 and ell=0"): -2/3 = 1/4 - 1 + 1/12. SEXTIC via the
  1/12 = h/6.
- 11/16 in C_II(s) -> 17/96 - 1 + 13/96 (l.8794) with l_x = 17/48, h = 13/16.
  SEXTIC via h/6; l_x, h themselves come from the slot cap ell = 1/6 (see below).
- ell = 1/6 (total slot length) and 6 ell <= 1 -> row-energy algebra
  1 + 3 ell' - 2M' (l.8300-8320, ell' = ell - d, "At d = 1/6 one has ell' = 0").
  NOT the symbol order (the 3 is the cube n^3 in the completed index, the 2 is the
  mean square). Would NOT change with k, as the task context states; I confirm
  the paper's algebra has no sixth-root count here.
- Gram exponent P_a^{1/6}, i.e. b/12 in the low bound (l.8533-8560): exceptional
  frequencies have (k) = a_1^6 e because "Principal zero masks at valuations
  divisible by six remain present in the exceptional case" (l.8447-8449); the
  count is K_R^{1/6} (l.8541-8545). SEXTIC: would be K^{1/k}.
- 17/50 (Re z contour for nonprincipal rows, l.4054, l.5492, l.5811) -> a point in
  the first Euler-convergence region of the local correction (l.4053-4056:
  x_r >= 51/100, z_r >= 17/50, w_r >= -1/100). INFERENCE: 17/50 = 0.34 sits just
  above 1/3, so 6 z_0 > 2; the local series carries Q^{-6zm} (l.4003) and
  zeta_F^S(6z_0) is "absolutely bounded" (l.5884, l.6139). Probably SEXTIC-linked
  (the cost h(17/50 - 1/6) appears in E(d), l.15728), but I cannot certify the
  exact convergence constraint that fixes 17/50 rather than any other number
  above 1/3.
- 51/100 (floor bin a > 51/100, delta = 2a-1 > 1/50) -> the detector floor
  (l.4214 "assume beta_* > 51/100", l.4285-4289). Tied to the zero-detector
  geometry, NOT the symbol order.
- 1 - delta/2 and 4/3 - delta in the Stage I row envelope R(delta) (l.5192-5195)
  -> sextic large sieve bound K + D + (KD)^{2/3} (l.4712-4716), via the BGL
  recursion whose power decomposition a = a_1 a_2^2 ... a_6^6 is sextic
  (l.5077-5090). The 2/3 term is the Heath-Brown/BGL higher-order exponent;
  SEXTIC/CUBIC-linked (a quadratic sieve has no such term).
- 1 - 2 delta/3 (no-slot row count, l.15215, l.15443) -> combination of the
  sixth-power amplification e(r) = max{1, (1+5r)/6} (Lemma "Sixth-power
  amplification", l.12363-12395: P = (H/U)^{1/6}, H/P = U^{1/6} H^{5/6}) with
  the zero-slot plain moment. SEXTIC-linked through the 1/6, 5/6. alpha = 5/6
  is "the fixed slope from sixth-power amplification" (l.15103-15104).
- 76/75 -> pure bookkeeping: R = 76/75 - 2 delta/3 is "the slightly larger
  common exponent" chosen so that "At delta = 1/50 it equals one" (l.16148-16153).
  Changes with the 2/3 slope and the floor 1/50.
- 7/37 -> inverse capacity (1 - 23/37)/2 = 7/37 (l.15381-15382) from the marked
  inverse-moment width conditions 1 - r - 2z >= 0 and 3 - 2r - 8z > 0
  (l.15374-15379), compared with the available slot length ell/h = 8/39
  (l.15384-15386). The 8/39 depends on ell = 1/6 (slot cap, not symbol order)
  and h = 13/16. I did not trace the 23/37; I cannot tell whether it is
  sextic-linked.
- Capacity 1/(6 kappa), i.e. the condition n_1 + n_2 + 6 kappa z <= M in Lemma
  "Fourth moment with short prime factors" (l.12531-12562, l.15175-15180) ->
  the paper says the threshold A <= 5M/6 "comes from the transformed rows whose
  inducing characters lie in Theta: counting their sixth-power form" (l.12590-
  12595) and uses "0 <= 6 kappa - 1 <= 5" (l.14827). INFERENCE: the 6 is the
  sixth-power row count (rows inducing in Theta are sixth powers times fixed
  data); likely SEXTIC, but the derivation of 6 kappa itself was not traced.

## Q4. The 1/12 in 11/12

PAPER: the paper does NOT phrase Stage I as "only Y = H^{1/6} of the rows are
usable". Its mechanism is: Poisson in m produces frequencies H = u a^6 with u
sixth-power-free (l.3756-3760); each row u carries the Dirichlet series over a
with q_a^{-6z}, extracted as the scalar zeta_F^S(6z) (l.3806-3810, l.4045). The
principal row is u = 1 (l.5503-5513: a unit u != 1 is not a sixth power since
"every unit of F has sixth power one", Chebotarev makes chi(u) nonprincipal).
Its scalar factor zeta_F^S(6z) zeta_F^S(w) / L_F^S(s,eta) (l.6227) has poles at
w = 1 and z = 1/6; the double residue carries X^{1/2 - 1/6} Z^{s + 1/6 - 1} =
X^{1/3} Z^{s - 5/6} (l.6299-6300) and the constant c_S with the factor 1/6
(l.5519-5521, l.6327). With X = Z^{1/2} this is Z^{s - 2/3} = Z^{C_I(s)}
(l.5547). The low estimate is Z^{1/4} (l.3318-3319, l.6692-6693:
"Z^{1/4+omega} = Z^{C_I(11/12)+omega}"). Equating 1/4 = sigma_0 - 2/3 gives
sigma_0 = 11/12, i.e. sigma_0 = 1 - h/6 with h = 1/2.

INFERENCE: the h/6 is indeed the density of sixth powers: the principal signal
is the a-sum over a^6 up to Z^h, of size Z^{h/6}, which is the leader's
"H^{1/6} of the rows". It is the SAME sextic 1/6 as in Q3 (pole of
zeta_F^S(6z)), and it is sextic because the Poisson dual variable sees the
character chi_A(m) of order six in m (so only sixth-power frequencies are
invisible to it). With a k-th order twist the principal signal would be
Z^{h/k}, giving sigma_0 = 1 - h/k + b/(2k) in the leader's notation.

## Verdict

PAPER states nothing about removing the quadratic factor or changing the theta
order. INFERENCE: the general shape is: theta of order k with Gauss-sum
coefficients chi^{N/k}, twist of order N = lcm(2,k), reflection j -> -j - N/k;
the probe twist must be chosen so that the reflected kernel is QUADRATIC,
because the only character large sieve with the clean bound (U+V) is the
quadratic one (l.2644-2650), and that bound is what gives the reflected energy
Z^{1+eps} (l.2866-2871) and hence the low estimate.
(i) k = 3 with the quadratic factor removed: the symbol group has order 3, the
reflected kernel chi^{-j-1} is cubic for every j, and the reflected energy would
rest on the cubic large sieve (Heath-Brown 2000, BGL 2014) with its (KD)^{2/3}
term; at equal lengths that term is Z^{4/3}/B, which breaks Z^{1+eps} at B = 1.
The obstruction is not merely an unproved improvement: to my recollection
Dunn-Radziwill, "Bias in cubic Gauss sums: Patterson's conjecture" (cited by the
paper as [DR], l.16521), prove on GRH that Heath-Brown's cubic large sieve is
sharp, i.e. the (KD)^{2/3} term cannot be removed. So within THIS architecture
the quadratic factor is irremovable; a k = 3 version needs a different low-side
mechanism, not a better sieve.
(ii) k = 4 over Q(i): N = lcm(2,4) = 4, so the quartic symbol already contains
the quadratic one, reflection j -> -j-1 lands on chi^{-2} (quadratic) at j = 1,
the rows would be u a^4 and the signal Z^{h/4}; the leader's law
sigma_0 >= 1 - (1 + 3 ell)/(2k) would apply with k = 4 (13/16), with the caveat
that the completed index c n^3 would become c n^4, so the "3" in the slot-cap
algebra 1 + 3 ell' - 2M' (l.8300-8320) is the SAME 3 as the theta order and
would move too (I did not recompute the cap). The known obstruction is the theta
input: for n = 3 the Fourier coefficients of the Kubota-Patterson theta function
are exactly cubic Gauss sums (Patterson 1977, used at l.1895-2001 via [DR]);
for n >= 4 the coefficients of the n-th order theta function are NOT Gauss sums
and are not known in closed form (Kazhdan-Patterson, and Eckhardt-Patterson's
work on biquadratic theta series showing the quartic coefficients at primes are
not determined by quartic Gauss sums). Without an explicit reflection identity
with multiplicative local factors (Prop. l.1706-1800) there is no completed
reflection, no quadratic kernel, and no principal row extraction. So k = 4 is
blocked by the open problem of the Fourier coefficients of quartic theta
functions (the "Kazhdan-Patterson / Patterson quartic coefficient" problem),
and k = 3 by the sharpness of the cubic large sieve.
