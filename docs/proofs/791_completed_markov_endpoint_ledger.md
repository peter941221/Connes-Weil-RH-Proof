# Proof 791: Completed Markov endpoint ledger

## Result

Let `B_S` be the actual source-band Gram endpoint, `C_(p,S)` the pulled-back
two-sided Markov coboundary, and `R_S` the actual nonlinear completed
remainder.  For visible-prime lists differing by `p :: S` and `S`, Lean proves

```text
B_(p::S) - B_S
  = C_(p,S) - (R_(p::S) - R_S).                         (791.1)
```

The same right-hand side is also the increment of the actual quadratic cycle
and of the completed relative response.

```text
Markov coboundary C_(p,S)
              |
              | subtract the matching completed remainder increment
              v
actual endpoint increment B_(p::S) - B_S
```

## Why It Matters

Equation `(791.1)` places the only possible extra-half-power cancellation on
one literal source Sonin carrier.  It is not legitimate to seek it inside the
Markov first jet, or in separately normed Hardy/prolate branches.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovCompletedFirstDifference.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovCompletedFirstDifferenceAudit.lean
```

Key declarations:

```text
sourceBandGramIncrement_eq_coboundary_sub_remainder
actualBandQuadraticCycledResponse_sub_eq_coboundary_sub_endpoint
actualBandCompletedRelativeResponse_sub_eq_coboundary_sub_endpoint
```

## Scope

This is an operator identity.  It asserts no trace legality, norm bound,
positivity, Gate 3U bound, finite-S sign, Burnol identity, or RH result.
