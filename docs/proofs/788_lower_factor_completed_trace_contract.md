# Proof 788: Lower-factor-square completed trace contract

## Result

Proof 788 combines Proof 784 and Proof 787 into one Gate-facing contract.
It does not prove Gate 3U, but it removes a remaining ambiguity about where
the finite Euler lower factor can disappear.

For

    c_S = finiteEulerLowerFactor(S.visiblePrimes) > 0
    K_S = completed Hardy--prolate physical boundary pairing
    n_S = Re Tr(normalizedSourceBandGramResponse_S)

Lean proves the exact identity

    || c_S^2 * sum_i Re K_S(e_i,e_i) || = |n_S|.      (788.1)

For the canonical selected family, it also proves

    canonicalRealGate3UAt(owner, bound)

    iff

    || c_S^2 * sum_i Re K_S(e_i,e_i) || <= c_S^2 * bound. (788.2)

Thus the remaining source theorem is not a merely uniform normalized estimate
and not a branchwise Hardy/prolate estimate.  It is the lower-factor-square
decay of the same completed signed physical trace from Proof 784.

## What Changed

    Proof 784:
      Gate real scalar
        = || sum_i Re K_S(e_i,e_i) ||

    Proof 787:
      normalized real trace
        = c_S^2 * raw real source trace

    Proof 788:
      |normalized real trace|
        = || c_S^2 * sum_i Re K_S(e_i,e_i) ||

This makes the active target:

    complete outer + reflected second support + prolate pairing
            |
            | keep signed and coupled
            v
    one Hermitian real trace series
            |
            | prove lower-factor-square decay before abs value
            v
    canonical real Gate 3U

## Lean Owners

    ConnesWeilRH/Source/CCM25Concrete/
      CCM24FiniteSGatePhysicalLowerFactorCompletedTrace.lean

    ConnesWeilRH/Dev/
      CCM24FiniteSGatePhysicalLowerFactorCompletedTraceAudit.lean

The public declarations are:

    norm_lowerFactorSq_completePhysicalHermitianTrace_eq_abs_normalizedSourceBandRealTrace
    canonicalRealGate3UAt_iff_lowerFactorSq_completePhysicalHermitianTraceBound
    canonicalRealGate3UAt_of_lowerFactorSq_completePhysicalHermitianTraceBound

## Scope

    +--------------------------------------------------------------+----------------+
    | statement                                                    | status         |
    +--------------------------------------------------------------+----------------+
    | normalized trace equals lower-factor-scaled completed trace  | Lean proved    |
    | canonical Gate iff scaled completed trace has c_S^2 bound    | Lean proved    |
    | support-polynomial lower-factor-square physical decay        | open           |
    | Gate 3U / finite-S sign / Burnol / RH                        | open           |
    +--------------------------------------------------------------+----------------+

Proof 788 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
_root_.RiemannHypothesis.
