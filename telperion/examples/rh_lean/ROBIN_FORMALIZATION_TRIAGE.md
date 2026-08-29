# Robin -> RH: Lean/Mathlib formalization triage (D2)

> Feasibility of kernel-formalizing each mapped result against Mathlib v4.32.0. Effort and target are the agent triage verdicts; none of these formalizations prove RH (see D1 wall).

| Result | Effort | Target | Missing |
|---|---|---|---|
| Colossally abundant (CA) definition and inclusion CA | low | telperion-emitter | Defs of SA and CA (short). The inclusion CA => SA is a one-line strengthening argument (global max of sigma(n) |
| Nicolas => Robin reduction (sigma(n)/n < n/phi(n)) | medium | mathlib-contribution | Only assembly work: express sigma(n)/n and n/phi(n) both as products over primeFactors of n (multiplicativity  |
| GA1 and GA2 numbers (definitions) | medium | telperion-emitter | The definitions are pure and formalizable now. The only nontrivial embedded claim -- '4 is the smallest extrao |
| SA reduction of least counterexample | medium | telperion-emitter | Definitions of 'superabundant' and 'the least counterexample' must be written (trivial defs). The proof is a p |
| Superabundant (SA) and Colossally Abundant (CA) defi | high | mathlib-contribution | The Alaoglu-Erdos structure theorem (non-increasing exponents k2>=k3>=...>=kp, kp=1 except {4,36}, P(N) ~ log  |
| robin-odd-n>9 | high | mathlib-contribution | The pre-PNT Mertens Lemma 1: sum_{p<=x} 1/p <= loglog x + gamma for x>=5 (an EXPLICIT effective bound, not the |
| robin-squarefree-n>30 | high | mathlib-contribution | Two pre-PNT Mertens estimates (Lemma 1 parts 1 and 2: sum_{p<=x}1/p <= gamma+loglog x, and a companion). A con |
| Akbary-Friggstad (2009): least counterexample is sup | high | mathlib-contribution | Definition of 'superabundant' (sigma(k)/k strictly maximal among k<=n) — must be defined, not in Mathlib. Mono |
| Gronwall maximal order | high | mathlib-contribution | The limsup = e^gamma requires Mertens' third theorem prod_{p<=x} p/(p-1) ~ e^gamma * log x, which is NOT in Ma |
| Consecutive-CA gap lemma (Robin's Proposition 1) | high | mathlib-contribution | The lemma chains: (1) CA extremal structure between consecutive CA numbers (depends on the CA generation theor |
| Sole-Planat Psi_t reduction to primorials | high | mathlib-contribution | Def of Psi_t and R_t; the 'champions are primorials' proposition (Sole-Planat Prop 1) — a maximization argumen |
| Robin unconditional weak bound | high | mathlib-contribution | The clean sigma(n)/n < e^gamma loglog n (1 + 0.6483/(loglog n)^2) needs a LOWER bound for Chebyshev theta stro |
| Robin's unconditional bound (G(n) <= e^gamma + 0.648 | high | telperion-emitter | The general-n effective bound still needs effective Mertens/Chebyshev estimates on prod(1-1/p)^{-1} over super |
| CA generation recipe (epsilon-sweep / x-parameter al | research-scale | mathlib-contribution | The whole constructive theory: the floor formula alpha_p(eps) = floor(log((p^{1+eps}-1)/(p^{eps}-1))/log p) -  |
| Gronwall (maximal order of sigma) | research-scale | not-formalizable-now | The load-bearing analytic core is entirely absent: Mertens' third theorem (prod_{p<=x}(1-1/p)^{-1} ~ e^gamma l |
| Ramanujan (conditional upper order) | research-scale | not-formalizable-now | Everything analytic: the RH-conditional refinement of the maximal order needs the explicit-formula / zero-free |
| Robin's criterion (RH iff sigma(n) < e^gamma n log l | research-scale | not-formalizable-now | Both directions of the iff are deep. Forward (RH => bound from n>5040) needs Ramanujan's sharpened bound (miss |
| Nicolas's criterion (totient/primorial form) | research-scale | not-formalizable-now | Same analytic core as Robin/Gronwall: limsup (n/phi(n))/loglog n = e^gamma needs Mertens' 3rd theorem; the iff |
| Lagarias's criterion (RH iff sigma(n) <= H_n + exp(H | research-scale | not-formalizable-now | The iff-with-RH is equivalent to Robin's criterion, so it inherits the SAME missing analytic core (Ramanujan b |
| CNS extraordinary-number reformulation of RH (RH iff | research-scale | not-formalizable-now | Direction (RH => 4 unique) needs Robin's unconditional bound (G(n)->e^gamma sup for n>5040, G(4)>e^gamma) -- p |
| GA2 numbers characterize RH failure quantitatively ( | research-scale | not-formalizable-now | Two separable parts. (a) The FINITE claim: the 19 explicit numbers 3,4,...,5040 are GA2, and every GA2 in that |
| Infinitely many CA numbers are GA1 | research-scale | not-formalizable-now | Depends entirely on the (unbuilt) SA/CA structure theory (exponent monotonicity, CA parameter function F(p,1), |
| gronwall-maximal-order | research-scale | not-formalizable-now | The entire analytic-number-theory core: Mertens' third theorem prod_{p<=x}(1-1/p)^{-1} ~ e^gamma log x is NOT  |
| robin-equivalence-RH | research-scale | not-formalizable-now | Robin's theorem is a deep equivalence resting on the explicit RH-conditional asymptotic (Ramanujan/Robin) sigm |
| robin-squarefull-exceptions | research-scale | not-formalizable-now | The Rosser-Schoenfeld explicit bound prod_{p<=x} p/(p-1) <= e^gamma(log x + 1/log x) and Chebyshev theta(x) >  |
| robin-5-free | research-scale | not-formalizable-now | Superabundant/colossally-abundant number theory (Alaoglu-Erdos exponent structure), Rosser-Schoenfeld, and the |
| robin-sum-two-squares-n>720 | research-scale | not-formalizable-now | The Banks-Hart-Moree-Nevans general density theorem, which uses explicit Ramare-Rumely prime-distribution boun |
| robin-7-free | research-scale | not-formalizable-now | Explicit Chebyshev theta(x) bounds and Mertens-type estimates at primorials (the R_t(N_k)<e^gamma verification |
| robin-11-free | research-scale | not-formalizable-now | Sharper explicit Chebyshev theta bounds (Broughan-Trudgian). Strictly stronger explicit prime-counting input t |
| robin-20-free | research-scale | not-formalizable-now | Explicit theta bounds PLUS Briggs' verified colossally-abundant range up to ~10^(10^13.11). The verified-range |
| robin-21-free | research-scale | not-formalizable-now | Recently-improved effective theta(x) and prod p/(p-1) estimates (Axler/Broadbent-Kadiri et al.) and the Morril |
| robin-padic-valuation-hertlein | research-scale | not-formalizable-now | Explicit theta bounds and the primorial-champion inequality N_k/phi(N_k) >= n/phi(n) closure. The per-prime Eu |
| robin-padic-valuation-axler-extension | research-scale | not-formalizable-now | Depends on Axler's refined absolute bound Theorem 1.3 (the axler-unconditional-upper-bound item below), which  |
| axler-unconditional-upper-bound | research-scale | not-formalizable-now | Effective Broadbent-Kadiri-Lumley-Ng-Wilk theta(x) estimates (loglog N_k = theta-based) and the Morrill-Platt  |
| Gronwall (1913): limsup of the normalized divisor su | research-scale | not-formalizable-now | The entire analytic core: Mertens' third theorem (the product-over-primes asymptotic), the construction of the |
| Robin (1984) equivalence | research-scale | not-formalizable-now | The equivalence proof requires Robin's explicit-formula analytic number theory: relating the excess of sigma(n |
| Robin's conditional lower bound if RH false (Robin 1 | research-scale | not-formalizable-now | Requires theta = sup Re(rho) > 1/2 machinery, the explicit-formula injection of an oscillating x^{theta-1} err |
| Broughan (2017): least counterexample can be taken C | research-scale | not-formalizable-now | Definitions of superabundant AND colossally abundant (CA: extremizers of sigma(k)/k^{1+eps} over a range of ep |
| Consecutive-CA quotient structure (Broughan Lemma 6. | research-scale | not-formalizable-now | Full CA-threshold theory: CA numbers arise from ordering the benefit thresholds log(1+1/(p^{a+1}...))/log p; t |
| Alaoglu-Erdos (1944): largest prime factor ~ log n | research-scale | not-formalizable-now | Asymptotic p ~ log n as n->infinity along superabundant n requires optimal-exponent-allocation analysis feedin |
| Morrill-Platt (2018): Robin verified in a large rang | research-scale | not-formalizable-now | The RANGE result (5040 < n <= 10^(10^13.099)) is NOT a per-n check — it is a mathematical reduction (to 25-fre |
| Zimov (2025) main theorem: least CA counterexample c | research-scale | not-formalizable-now | The proof CHAINS unbuilt prerequisites: Lemma 1 (loglog m/loglog n = 1+o(1)), Thm 5 (p ~ log n, Alaoglu-Erdos, |
| Robin criterion (RH equivalence) | research-scale | not-formalizable-now | The RH<=>Robin EQUIVALENCE is a research-frontier theorem, not a computation. Mathlib has NO statement of RH ( |
| t-free / t-full progress (Robin unconditional cases) | research-scale | not-formalizable-now | Depends entirely on the Sole-Planat reduction (above) plus the effective theta estimates of Broadbent-Kadiri-L |
| Computational frontier: Briggs and Morrill-Platt bou | research-scale | not-formalizable-now | Two things: (1) the CA generation recipe (to know WHICH numbers to check and that they are ALL the CA numbers  |
| Extremely abundant (XA) numbers and RH equivalence | research-scale | not-formalizable-now | Same class as the Robin criterion: the RH <=> (#XA = infinity) biconditional depends on Gronwall's limsup = e^ |

## Prioritized roadmap (from the triage)

**Now (low/medium, Telperion-emitter):** CA/SA definitions + CA subset SA (low); the SA-reduction of the least counterexample (medium) -- the load-bearing lemma for "Robin for all n <= X"; GA1/GA2 definitions.

**Mathlib-contribution candidates:** Nicolas => Robin bridge (sigma(n)/n < n/phi(n)); elementary unconditional families (odd n>9, squarefree n>30); Lagarias/Nicolas statements.

**Not now:** anything requiring the infinite CA tail (= RH), the interval-arithmetic computational sweeps (no verified interval library in scope), Robin Thm 7 / Zimov band (deep analytic).
