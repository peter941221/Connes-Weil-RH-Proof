# Proof 458: Endpoint-only rectangular boundary collapse

## Result

Proof 458 performs an exact cancellation inside the Proof 457 ledger.  The
first-jet pair and its two rectangular defects cancel against the first-jet
part of the source quadratic cycle.  What remains is the endpoint-only ledger

```text
Tr M_global(endpoint)
  = Tr M_source(base^dagger*base - frame^dagger*dual)
    + boundary(base,base^dagger)
    - boundary(dual,frame^dagger).
```

The source endpoint cycle is identified with the existing `sourceBandGramResponse`.
At the same time, Proof 457's exact combined identity gives

```text
Tr M_source(sourceBandGramResponse)
  + endpointRectangularBoundary
  = 2 * integral_0^1 weightedBoundaryTrace(alpha) d alpha.
```

The weighted trace still contains Proof 455's detector core and root-cycle
defect.  The left side now has only two rectangular boundary defects rather
than the four terms in the quadratic ledger.

## Consumer

`canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_sourceGramBoundaryBound`
accepts one bound on the source Gram response plus the two endpoint boundary
defects, along an arbitrary source-prefix schedule.  It derives the existing
weighted-boundary consumer without estimating any component separately.

## Boundary

This is exact algebra and carrier bookkeeping, not the missing analytic bound.
The uniform source-Gram-plus-boundary estimate, finite-S sign, negative-owner
integration, Burnol's identity, and `_root_.RiemannHypothesis` remain open.
