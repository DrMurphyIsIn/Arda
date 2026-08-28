# Newton's inequalities for the Jensen sequence of ξ

The correctly-normalized log-concavity — sharper than `turan_xi`, and the pairwise
necessary condition for Jensen-polynomial hyperbolicity (hence for RH).

## The mathematics

For the Jensen polynomial `J^{d,n}(X) = Σ_j C(d,j) γ_{n+j} X^j` of `ξ` (with the
EGF sequence `γ_k = k!·a_k`, `a_k = [z^{2k}] ξ(1/2+z)`), real-rootedness implies
**Newton's inequalities** on the binomial-basis coefficients:

```
γ_k² ≥ γ_{k-1} γ_{k+1}      (log-concavity of the Jensen sequence).
```

This is *sharper* than the raw-coefficient Turán inequality `a_k² ≥ a_{k-1}a_{k+1}`
that `turan_xi` certifies: dividing through, it says `a_k² ≥ ((k+1)/k) a_{k-1}
a_{k+1}` — the extra factor `(k+1)/k > 1` is exactly the binomial normalization,
and it is the version tied to Jensen hyperbolicity. **Normalization was fixed
empirically** (see `jensen_xi`): `γ_k = k!·a_k` is right; `(2k)!·a_k` is not.

It is a product-vs-square inequality, so it **reuses the proven
`TuranEnclosureCertificate`** (`turan_from_enclosure` bridge) over the γ
enclosures — no new Lean. Certified for **k = 1…6**.

- `compute_gammas.py` / `gammas.json` — the transcendental import (mpmath).
- `generate.py` — instantiates `TuranEnclosureCertificate` on γ; `certify → emit
  → freeze`. `frozen/NewtonXi.lean` — emitted.

## Honest scope

RH-**necessary**, not sufficient; finite (k = 1…6); enclosure-conditional; not
`lake`-built. It is *implied by* the cubic hyperbolicity `jensen_xi` certifies
(Newton ⟸ hyperbolic), so it is a cleaner all-k companion rather than new
strength.

## Reproduce
```bash
python3 examples/newton_xi/compute_gammas.py         # regenerate gammas.json (needs mpmath)
python3 examples/newton_xi/generate.py               # certify -> emit -> freeze
python3 examples/newton_xi/generate.py --check       # drift check
```
