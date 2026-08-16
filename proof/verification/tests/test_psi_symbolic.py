"""The exchange-lemma identity is GENERAL (all trees), not just N<=9."""
from verification.psi_symbolic import (
    prove_identities_symbolic,
    verify_expansion_formulas,
)


def test_expansion_formulas_reproduce_real_psi():
    # EXP_beta / EXP_betap match the actual Psi on every Kelmans step, all trees n<=9.
    res = verify_expansion_formulas(n_max=9)
    assert res["ok"] and res["steps"] > 4000


def test_identities_proven_symbolically():
    # topology-lemma identity + pi-level bilinear form hold as symbolic identities
    # in the free environment quantities -> valid for ALL trees at once.
    p = prove_identities_symbolic()
    assert p["topology_lemma_identity"]
    assert p["pi_bilinear_exact"]
