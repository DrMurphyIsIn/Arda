# Primality certificate emitter — status & Lean-emit design (2026-08-21)

First entry into a NEW domain for Telperion (number theory), from
[COVERAGE_GAPS_2026-08-21](COVERAGE_GAPS_2026-08-21.md) rank #1.

## Shipped (this PR) — the untrusted-generator core, fully tested

`telperion/pratt.py`:
- `find_pratt_certificate(n)` — deterministic search for a Lucas witness `a`
  (order n-1 mod n) + complete prime factorization of n-1 + recursive Pratt
  sub-certificate per prime factor (bottoms out at 2). Returns `None` if `n` is
  composite.
- `verify_pratt_certificate(cert)` — independent exact-integer re-check:
  factorization reconstructs n-1, witness has order exactly n-1, every claimed
  prime factor is itself certified.
- `PrattCertificate` dataclass (recursive).
- CLI `telperion prime <n>` — finds, verifies, and renders the recursive
  certificate; exit 1 on composite.

Tested (`tests/test_pratt.py`): certifies primes (incl. 32-bit+), rejects
composites, checks recursive structure, rejects a tampered witness. All local,
exact arithmetic — no Lean needed for this layer.

## Follow-up (CI-gated) — the Lean emitter

Target: emit, per certificate, a theorem discharged through Mathlib's
`lucas_primality` (verbatim signature, confirmed from mathlib4_docs):

```lean
theorem lucas_primality (p : ℕ) (a : ZMod p)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ (q : ℕ), Nat.Prime q → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) :
    Nat.Prime p
```

Emission shape for a prime `p` with witness `a` and prime factors `{q₁,…,qₖ}`
of `p-1` (each with its own emitted `isPrime_qᵢ`):

```lean
theorem isPrime_<p> : Nat.Prime <p> := by
  refine lucas_primality <p> (<a> : ZMod <p>) ?_ ?_
  · decide                              -- a^(p-1) = 1 in ZMod p
  · intro q hq hqd
    have hq_mem : q ∈ (<p> - 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqd, by norm_num⟩
    fin_cases hq_mem <;> decide          -- (p-1).primeFactors = {q₁,…,qₖ}; a^((p-1)/qᵢ) ≠ 1
```

Sub-certificates are emitted first (topological order, leaves→root) so each
`fin_cases` branch's factor primality is already in scope where Lucas needs it
(Mathlib's `lucas_primality` takes `Nat.Prime q` as a *hypothesis* `hq`, so the
factor primalities are actually consumed by the recursion assembling `hqd`, not
re-proved inside — the emitter threads the sub-theorems as needed).

### The open risk (why this is CI-gated, not shipped)
The two `decide` calls evaluate `ZMod p` exponentiations **in the kernel**.
Kernel `decide` on `a^(p-1)` for large `p` can blow `maxHeartbeats`/memory
(naive `Monoid.npow` = p-1 multiplications unless the kernel uses fast-pow).
This must be measured in CI (this machine cannot build Lean — see memory
"System crashes = SoC watchdog panics"). Mitigations to try in CI order:
1. `decide` as above (simplest; may be too slow past small p).
2. `Nat.ModEq` / `ZMod.natCast_pow` rewrites to keep exponentiation in ℕ with
   `Nat.pow_mod` (fast modular pow), then `norm_num`.
3. `by norm_num [ZMod.pow_eq_pow_iff_of_prime]`-style targeted lemmas.
Pick the first that compiles green within budget; shard large certs across files.

Until a CI-green emission is demonstrated, **no primality Lean is claimed to
compile** — the finder/verifier ship now; the emitter lands when CI proves it.
