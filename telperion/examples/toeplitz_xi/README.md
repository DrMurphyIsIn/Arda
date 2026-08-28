# Total positivity (3×3 Toeplitz minors) for the Riemann ξ

A **different** RH-necessary lens from Jensen hyperbolicity (`turan_xi`,
`jensen_xi`): the Pólya-frequency / total-positivity criterion.

## The mathematics

RH ⟺ `G(u) = Σ_k a_k u^k` (with `a_k = [z^{2k}] ξ(1/2+z)`) has only real negative
zeros ⟺ `G` is a **Pólya-frequency function** ⟺ the one-sided Toeplitz matrix
`[a_{i−j}]` is **totally positive** — all minors ≥ 0 (Edrei–Thoma,
Aissen–Schoenberg–Whitney). The 2×2 minors are log-concavity (`turan_xi`); the
**3×3 minors** are new degree-3 conditions:

```
minor(m) = det [[a_m, a_{m-1}, a_{m-2}], [a_{m+1}, a_m, a_{m-1}], [a_{m+2}, a_{m+1}, a_m]]
         = a_m³ − 2 a_{m-1} a_m a_{m+1} + a_{m-1}² a_{m+2} + a_{m-2} a_{m+1}² − a_{m-2} a_m a_{m+2}  ≥ 0.
```

All `a_k > 0`, so a **worst-corner** exact-rational lower bound (positive monomials
at the enclosure floor, negatives at the ceiling) certifies the minor over the
whole box; the once-proved `toeplitz3_pos_of_enclosure` bridge (five `mul_le_mul`
monomial chains + `nlinarith`) discharges it in Lean. Certified for **m = 2, 3,
4, 5** (worst-corner margins `+1.5e-13`, `+2.2e-20`, `+1.4e-27`, `+4.4e-35`).

- `src/telperion/toeplitz.py` — `ToeplitzMinorCertificate` + `TOEPLITZ3_BRIDGE_LEMMA`.
- `compute_coeffs.py` / `a_coeffs.json` — the transcendental import (mpmath).
- `generate.py` — `certify → emit → freeze`. `frozen/ToeplitzXi.lean` — emitted.

## Honest scope

RH-**necessary**, not sufficient; finite (m = 2…5); enclosure-conditional; not
`lake`-built (bridge hand-verified, not machine-checked locally per the SoC
hazard). Higher minors (4×4, …) and the full total-positivity hierarchy are the
next rungs — the worst-corner method generalizes, with more monomials.

## Reproduce
```bash
python3 examples/toeplitz_xi/compute_coeffs.py       # regenerate a_coeffs.json (needs mpmath)
python3 examples/toeplitz_xi/generate.py             # certify -> emit -> freeze
python3 examples/toeplitz_xi/generate.py --check     # drift check
pytest tests/test_toeplitz.py -q
```
