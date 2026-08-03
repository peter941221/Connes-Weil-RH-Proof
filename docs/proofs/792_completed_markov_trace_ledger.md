# Proof 792: Trace-legal completed Markov ledger

## Result

Under the existing actual Hardy--prolate pair-data hypotheses, all terms in
Proof 791 are trace class along one fixed source Hilbert basis.  Lean proves

```text
Tr(B_(p::S) - B_S)
  = Tr(C_(p,S)) - Tr(R_(p::S) - R_S).                   (792.1)
```

No new trace cycle is introduced: the coboundary is read back as a difference
of the two actual first jets, and the remainder increment as a difference of
the two actual completed remainders.

## Why It Matters

The cancellation candidate now exists at the scalar trace level where Gate
3U is evaluated.

```text
actual pair data
      |
      v
trace-class first jets and remainders
      |
      v
Tr(endpoint increment) = Tr(coboundary) - Tr(remainder increment)
```

The equation does not authorize taking absolute values of its two terms
separately.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovCompletedTraceDifference.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovCompletedTraceDifferenceAudit.lean
```

Key declarations:

```text
sourceBandGramIncrement_isTraceClassAlong
ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder
```

## Scope

This proves trace legality and an exact trace identity.  It supplies no
uniform trace estimate and does not close Gate 3U.
