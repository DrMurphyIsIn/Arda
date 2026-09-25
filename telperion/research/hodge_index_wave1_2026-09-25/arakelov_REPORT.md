# Hodge index for Spec Z, wave 1: angle `arakelov`

conjecture1_proved = False. Mechanism alive: False. Survived adversarial review: False.

# ANGLE arakelov: Hecke/Arakelov Hodge index as the source of W(x)

conjecture1_proved = False. **Verdict: the natural Arakelov/Hecke mechanism is REFUTED numerically as a route to W at scale. What it leaves is a barrier (a sharp statement of what fails), not a proof.**

## 1. The mechanism, stated precisely
**Function-field template.** On C x C, the Hodge index theorem is applied to the primitive part of the Frobenius graph Gamma_{F^n}, i.e. Gamma minus its components along the fibre classes. It gives Castelnuovo-Severi, which gives |alpha| = sqrt q, which gives W(x) for every x.

**Transport to Q, the best available version.**
- The arithmetic surface is X_0(N) x X_0(N) over Z, with Faltings-Hriljac or Yuan-Zhang Hodge index.
- The Hecke correspondences T_p act as the Frobenius graphs.
- Eichler-Shimura says T_p = F + V^t mod p. Castelnuovo-Severi on the fibre at p then gives purity |alpha_p| = |beta_p| = 1. Characteristic 0 alone does not: a symmetric bidegree (sigma(n), sigma(n)) gives only the trivial bound. The 11a table shows |a_p| <= 2 sqrt p from Frobenius, against only p+1 from characteristic 0.

So the entire output of "Hodge index on Hecke correspondences" is **local purity at every p, together with prime-power support (Euler product)**.

**Claim HH(x).** Take any Dirichlet series with the archimedean factor, conductor and pole of zeta_K, and with c(p^k) = log p (alpha_p^k + beta_p^k), |alpha|, |beta| in {0, 1}, and c = 0 off prime powers. Then Q_x >= 0 on the full window class.

If HH(x) held for all x, the Hecke-Hodge index would prove GRH-type positivity. **The test shows HH(x) fails for x > ~5.05.**

**The structural reason, as intersection numbers.** On X(1) x X(1), genus 0, the Lefschetz number of T_n is

Gamma_{T_n} . Delta = sum_t H(4n - t^2) = 2 sigma(n) - sum_{d|n} min(d, n/d).

This is the Hurwitz-Kronecker class-number relation, verified exactly for n <= 40 in hecke.py. Reading it term by term:
- the CM fixed points are the left side;
- H^0 and H^2 contribute 2 sigma(n), whose Dirichlet series is zeta(s)zeta(s-1);
- the cusp or boundary contributes lambda(n);
- the primitive H^1 contributes 0.

zeta lives entirely in the non-primitive and boundary classes, which Hodge index does not constrain; it treats them as the ample direction. Arakelov invariants of X_0(N) (omega^2 ~ 3g log N, Green's functions, Kudla-Rapoport-Yang arithmetic degrees) see zeta only through values such as zeta'/zeta(2) and zeta'(-1), or through resonances of the scattering matrix xi(2s-1)/xi(2s). They never see zeros as a spectrum carrying positivity. On the cusp-form side, Gross-Zagier heights and Waldspurger periods give L'(1/2) >= 0 and L(1/2) >= 0 for cusp forms. These are pointwise GRH consequences, and the degree-0 projection kills the Eisenstein/zeta component.

## 2. Where the Euler product enters
Nonlinearly, through Satake parametrization and prime-power support, so the linearity barrier is not the obstruction. The obstruction is that the input is *local*. The failing data are locally perfect: pure and Euler. They are globally incoherent: with a pole and conductor 20, the only realizable object is zeta*L(chi_-20) = zeta_K.

## 3. Counterfeit control
E leaves the class at n = 6 (c_E(6) = 3.584, not a prime power) and at n = 9 (c_E(9) = 3 log 3 > 2 log 3, violating purity). D leaves at n = 6. Up to x < 6, E is locally pure (c_E(2) = 0, c_E(4) = 2 log 2, c_E(5) = log 5) and Weil-positive. The mechanism's horizon, x_P ~ 5.05, lies **below 6**. It dies before E is even distinguishable, far short of x_E ~ 19.82 or x_D ~ 31.

## 4. Tests run (scratchpad/hodge/arakelov/)
The harness uses bcore pole + arch plus independent Gauss-Legendre prime matrices, and reconstructs bcore's comb to 1e-14. Galerkin bases are Neumann, N = 16 and 24. A negative Galerkin value is a genuine negative test vector.

| test | result |
|---|---|
| zeta_K data, strict purity (p = 2, 5 ramified) | x = 5.03: +9.1e-3 (N = 16), +8.4e-3 (N = 24); x = 5.1: -1.72e-2 / -1.77e-2; x = 6: -0.356 / -0.357. Witness: alpha_2 = -1, 3 with alpha = beta = -1, alpha_5 = -1. Bisection gives x_P in [5.047, 5.063]; onset as log 5 enters the window. |
| zeta_K data, unitary at every p | x_P in [4.19, 4.20] |
| zeta_K itself | +5.0e-3 (even) at x = 20, stable; agrees with the certified 3.44e-3 |
| zeta data (degree 1, pole) | fails as soon as p = 2 enters: alpha_2 = -1 at x = 3 gives -0.265 / -0.899; even the relaxed alpha_2 = 0.99 gives -1.8e-4 / -2.0e-3 at x = 3 |
| pole-free, conductor q | worst pure datum is always 'all +1' (zeta minus its pole); log Q_req(x) = 2.17, 3.33, 4.51, 5.85, 7.21, 8.66, 10.33 at x = 3, 5, 8, 13, 20, 30, 45, so Q_req ~ x^{2.0-2.7}: purity alone gives only the trivial small-support range |
| Hecke Lefschetz on X(1) | the identity holds exactly for n <= 40 |
| 11a | a_p within 2 sqrt p (the Frobenius-CS bound); the characteristic-0 Hecke-CS bound is only p+1 |

Optimizer caveat: the worst case was found by coordinate descent over a grid of Satake angles, so each reported worst value is an upper bound on the true minimum, and each x_P is an upper bound. Every negativity claim is backed by an explicit witness.

## 5. Literature (UNVERIFIED: the session's web-search budget was used up)
- Faltings 1984; Hriljac 1985; Yuan-Zhang, arithmetic Hodge index for adelic line bundles (~2017).
- Eichler 1954, Shimura, Ihara (congruence relation); Deligne 1974.
- Gross-Zagier 1986; Waldspurger 1981 and Kohnen-Zagier 1981 (nonnegativity of central values).
- Kudla-Rapoport-Yang 2006.
- Abbes-Ullmo 1997 and Michel-Ullmo 1998 (omega^2 on X_0(N)).
- Lax-Phillips 1976 (scattering and resonances).
- Haran (non-additive geometry, 2007); Manin 1995; Connes-Consani (~2020-21, Weil positivity at the archimedean place).

No known work builds a Hodge-index surface whose positivity restricts to W(x) for zeta. The purity-horizon computation appears new. It strengthens the project's W_{p,c} barrier: those examples violated purity, and these are pure.

## 6. Odds and deliverables
- Hecke/Arakelov Hodge index on existing arithmetic surfaces reaching W(x) for all x: < 0.2%.
- A new Spec Z x Spec Z with a proved Hodge index: < 1% within the horizon.

Deliverable, a barrier theorem: "Locality + purity + (Gamma, conductor, pole) does not imply W(x) for x > ~5 (zeta_K data) or x > 2 (zeta data)." It could be kernel-checked by exhibiting the witness datum and a negative vector at x = 6. The lesson for any future "Hodge index for Spec Z" is that its positive-definite complement must include the fibre/pole class that couples all primes. The pole is not a nuisance term. It is the ample class, and every local positivity is blind to it.

## Adversarial verdict

```json
{
 "angle": "arakelov (skeptic review): testing whether a Hecke-correspondence Castelnuovo-Severi / Arakelov Hodge index can serve as a Hodge index for Spec Z. The proposal itself returns alive=false and offers a barrier result.",
 "survives": false,
 "fatal_flaws": [
  "As a route to W(x), the mechanism is refuted by its own test, and I reproduced that refutation independently. For zeta_K data, the worst locally pure Euler datum (alpha_2=-1, alpha_3=beta_3=-1, alpha_5=-1) is Weil-negative from x ~ 5.05. That is far below x_E ~ 19.82, so the mechanism cannot separate zeta_K from E.",
  "The function-field analogy is wrong at the key step. Over F_q, Hodge index on C x C gives GLOBAL purity: |eigenvalues of Frobenius on H^1| = sqrt q, which is RH itself for the curve's zeta. On X_0(N) mod p, Eichler-Shimura plus Castelnuovo-Severi gives LOCAL Ramanujan (|a_p| <= 2 sqrt p, which is RH for the reduction's local zeta). That says nothing about zeros of L(f,s) or zeta. So HH ('local purity implies W') is not the analogue of Weil's argument. It is the statement 'Ramanujan + Euler product implies GRH', which is folklore-false once the functional equation is dropped (Beurling-type Euler products with off-line zeros). The test refutes a strawman.",
  "For zeta and zeta_K, the Satake data are roots of unity, so their purity is trivially true. The X_0(N), Eichler-Shimura and 11a machinery adds nothing about zeta. It is decoration.",
  "The 'barrier' is much weaker than advertised. The failing data keep the Gamma factor, conductor and pole but DROP the functional equation, which is exactly the global constraint. That the Weil form is non-monotone under sign flips of prime coefficients follows at once from zeta's near-null saturation. I checked zeta data at x=3: alpha_2 = 0.99 already gives lambda_min = -1.9e-4 / -2.0e-3. A barrier that any tiny perturbation beats says little that the near-null phenomenon did not already say.",
  "Factual errors in the counterfeit bookkeeping. c_E(9) = 6 log 3 (a_E(9) = 3, c_E(3) = 0), not 3 log 3. c_E(4) = 2 log 2 already violates the STRICT class (p=2 ramified, where |c(4)| <= log 2 is required). So 'E passes every local test for x < 6' holds only for the unitary-at-every-p class. The qualitative conclusion is unchanged."
 ],
 "linearity_or_classP_violation": "The proposal escapes the linearity barrier only formally. Satake parametrization is nonlinear, but the class it tests is defined by LOCAL constraints only, with the functional equation dropped, so it is a fooling family from the opposite side. The project's class-P / fooling lemma says functional equation + growth alone cannot separate zeta from counterfeits. This result says Euler product + Ramanujan + fixed Gamma/conductor/pole alone cannot either. Together they only restate that any proof must use the full Selberg-class conjunction: the functional equation and the Euler product coupled globally. That is the standing expectation (GRH for the Selberg class), not a new constraint. Nothing in the argument assumes W or an RH-equivalent, so there is no circularity; there is also no positive theorem.",
 "counterfeit_check": "Reproduced with independent code. It uses a smooth basis (1-(u/A)^2)^w T_k(u/A), archimedean term computed as a Fourier-side digamma integral (my own complex digamma), pole via F(+-i/2), and prime matrices by Gauss-Legendre; bcore is not imported. Every Rayleigh-Ritz value is an upper bound on lambda_min, so each negative value is a genuine negative test function.\n- zeta_K: +0.93 at x=6; +8.9e-3 (even) at x=20; +3.2e-3 at x=22.\n- E: positive through x = 20.5 (+1.3e-3 even, N=12, an upper bound that lags); negative at x=22 (-2.9e-4 even) and x=25 (-3.2e-4 even, -1.5e-2 odd). This is consistent with x_E ~ 19.82.\n- D: lambda_min is ~1e-13..1e-16 over x = 20..45, i.e. at double-precision noise. D's sign near 31 is NOT resolvable in float64 with this basis; that needs mpmath or certified arithmetic.\n- The mechanism's own failure point is x ~ 5.05, well before n=6 where E leaves the Euler class. So it never engages the counterfeits, as the proposer says.",
 "numerics_reproduced": "YES, to about 3 digits, with fully independent code (scratchpad/hodge/arakelov_skeptic/wf.py, cdig.py, t_main.py, t_h.py, t_z.py; float64 numpy).\n- Worst strict datum at x=5.1, odd sector: -1.71e-2 (N=26, w=1). Proposer: -1.77e-2.\n- At x=5.03: +8.9e-3. Proposer: +8.4e-3.\n- My horizon lies in (5.03, 5.06]. Proposer: [5.047, 5.063].\n- x=6: -0.29, an upper bound. Proposer: -0.357 with the Neumann basis.\n- An exhaustive grid search found the same witness, (alpha_2 = -1, theta_3 = pi, alpha_5 = -1).\n- Unitary at every p: horizon in (4.18, 4.22), witness theta_2 = theta_3 = pi. Proposer: 4.19-4.20.\n- zeta data at x=3: alpha_2 = 0.99 gives -1.87e-4 / -2.03e-3; alpha_2 = -1 gives -0.265 / -0.899. Both match exactly.\n- Coefficients: c_ZK matches Lambda(1+chi_-20) to 4e-15; c_E(6) = 3.5835 is confirmed; c_E(9) = 6.5917 = 6 log 3, which corrects the proposal.\n- Not rerun: the pole-free Q_req table and the Hurwitz-Kronecker check.",
 "novelty": "Low. Neither the classical inputs nor the qualitative conclusion is new:\n- The Kronecker-Hurwitz class-number relation is classical, and reading it as T_n . Delta is Hirzebruch-Zagier / Zagier.\n- 'Ramanujan + Euler product does not give RH without the functional equation' is folklore (Beurling generalized-prime zeta functions; Diamond-Montgomery-Vorhauer, recalled from memory).\n- Gross-Zagier and Waldspurger are the known arithmetic positivity results, at the central point for cusp forms.\nThe only possibly new item is the specific number x_P ~ 5.05 for zeta_K data (4.2 unitary). Given near-null saturation, that is a margin measurement, not a structural theorem. All citations are UNVERIFIED: this session's web-search budget was exhausted (200/200), for the proposer and for me alike.",
 "what_is_real": "1. A correct, independently reproduced quantitative fact: with Gamma_R(s)Gamma_R(s+1), conductor 20 and the pole fixed, locally pure Euler data are not all Weil-positive beyond x ~ 5.05 (strict class) or ~ 4.2 (unitary at every p). There is an explicit negative witness (alpha_2 = -1, alpha_3 = beta_3 = -1, alpha_5 = -1); at x=6 it gives lambda_min <= -0.29 even with C^2 test functions vanishing at the edges. It can be Lean-certified cheaply as a small rational Gram/Rayleigh check, as a documented negative control.\n2. A clarified lesson: any 'Hodge index for Spec Z' must constrain the Euler coefficients GLOBALLY, through the functional equation / pole direction. Local Castelnuovo-Severi on Hecke correspondences only gives Ramanujan-type local purity, which is trivial for zeta and insufficient even at x ~ 5.\n3. Minor corrections to the proposal: c_E(9) = 6 log 3, and E already violates strict ramified purity at n=4.",
 "next_step_if_survives": "It does not survive as a mechanism. The single most informative follow-up for the barrier line is to re-run the worst-case search restricted to data that ALSO satisfy the functional equation approximately. One way: impose the approximate-FE / Guinand-Weil constraints as linear conditions on (c(n))_{n <= x^2} via smoothed explicit-formula identities at test functions supported beyond the window, then check whether the minimal lambda_min over locally pure Euler data plus FE constraints is still negative at x ~ 6-20. If it goes negative, that is a genuinely informative barrier: FE + Euler + Ramanujan locally still does not force W at finite x, and would pin down exactly which global rigidity (class-P uniqueness) must be used. If it stays positive up to about 19.8 while E fails, that is the first mechanism that couples both halves. Separately, D's window sign near x ~ 31 should be recomputed in high precision: float64 cannot resolve it."
}
```
