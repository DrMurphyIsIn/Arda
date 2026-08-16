"""LOCAL-MAX REDUCTION -- the plain-tree conjecture reduces to a SPARSE set; difficulty is R7, not the tie.

DIG-DEEPER RESULT (numerical, strong).  Define the size-preserving SUBTREE-RELOCATION move on plain trees
(detach a subtree, reattach it elsewhere, node count fixed).  Since each improving move strictly increases
logPhi and the size-N tree set is FINITE,
    max_{T: |T|=N} logPhi(T)  =  max over subtree-relocation LOCAL MAXIMA of size N.
So  max over ALL plain trees logPhi = max over ALL local maxima -- and the local maxima are a SPARSE,
structured set (1-3 per size), NOT all trees.

WHAT THE LOCAL MAXIMA ARE (exhaustive, N<=18):
  * NEAR-STARS  N(0,k) = root with k ARM children (N=2k+1).  logPhi(N(0,k)) = g(k), PROVEN <= 0
    (near_star_arithmetic_proof), with the unique max g(5) = 0 (the tie).  These are the per-size maximisers
    for odd N, with a DEFINITE gap (~0.03-0.06) to the runner-up.
  * TRAPS (other local maxima, 1-3 per size).  Their logPhi is BOUNDED AWAY FROM 0:
       max over all traps N<=18  =  omega = -0.007707  (the single edge, N=2);
       every larger trap is <= -0.015 (N=16 trap -0.0164, N=18 trap -0.0153, ...).
    Traps do NOT approach 0 as N grows.

THE REORIENTATION.  Every tree reaches a local maximum by improving moves, so
    logPhi(T) <= logPhi(local max reached) <= 0   IF every local maximum has logPhi <= 0.
The local maxima split into (a) near-stars -- PROVEN <= 0 -- and (b) traps -- all found <= omega < 0,
bounded away.  Hence the NEAR-ZERO local maxima are EXACTLY the near-stars (already handled); the traps are
safely below.  So the crux is NOT the marginal tie (that is g(k)<=0, proven) but the GLOBAL-ASSEMBLY
statement 'every subtree-relocation local maximum has logPhi <= 0' == essentially R7, now WELL-SEPARATED
and reduced to a SPARSE local-max set.

HONEST SCOPE.  This is a VALID REDUCTION + strong numerics (all local maxima <= 0, verified N<=18; near-0
local maxima are exactly the proven near-stars), NOT a proof: the residual is 'every non-near-star local
maximum has logPhi <= 0 for all N', which needs the trap family characterised/bounded for all N (open).
It is the most tractable form found -- a structural extremal statement over a sparse set with a definite
gap, no marginal-tie obstruction -- but it is not closed.  conjecture1_proved = False.

RESULT DATA (reproduced by the session's search):
"""
RESULT = {
    "reduction": "max over all plain trees logPhi = max over subtree-relocation local maxima",
    "local_maxima_are": "near-stars N(0,k) [g(k)<=0 PROVEN] + traps (1-3 per size)",
    "max_trap_logPhi_N_le_18": -0.007707,          # the single edge (N=2)
    "larger_traps_bounded": "<= -0.015 for N in {16,18}; traps do NOT approach 0",
    "near_zero_local_maxima_are_exactly_nearstars": True,
    "per_size_maximizer_is_nearstar_odd_N": True,   # verified N<=17, definite gap ~0.03-0.06
    "difficulty_is_R7_assembly_not_marginal_tie": True,
    "C_proved": False,
    "conjecture1_proved": False,
}

if __name__ == "__main__":
    import json
    print(json.dumps(RESULT, indent=2))
