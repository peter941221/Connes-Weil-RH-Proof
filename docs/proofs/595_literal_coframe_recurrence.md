# Proof 595: literal coframe recurrence

## Result

The literal-list metric coframe now has an exact polar readback:

```text
M_S
  = upperFactor(S) * AmbientProduct(S)^dagger
      * newSuffixFrame(S) * GramInvSqrt(S)
```

For an adjacent visible prime `p`, the same source file proves

```text
M_(p::S)
  = upperFactor(p::S) * AmbientProduct(S)^dagger
      * (newFrame(S) * transition(p,S)^dagger
         + boundaryDagger(p,S)) * GramInvSqrt(p::S).
```

The forward coframe has its own exact causal recurrence:

```text
F_(p::S)
  = sourceBandProjection * inverseList(S)
      * inversePrime(p) * sourceInclusion.
```

These are readbacks on the actual finite-S and source carriers.  They do not
provide a family-uniform bound or identify the metric coframe with the forward
coframe.

```text
 +------------------------+       +--------------------------+
 | terminal Gram polar M_S| ----> | adjacent Schur expansion |
 +------------------------+       +------------+-------------+
                                                 |
                         +-----------------------+-----------------------+
                         |                                               |
                         v                                               v
              +----------------------+                         +-------------------+
              | survivor coordinates |                         | boundary dagger   |
              | frame * transition   |                         | genuine leakage   |
              +----------------------+                         +-------------------+
```

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrenceAudit.lean
```

The audited declarations use only `[propext, Classical.choice, Quot.sound]`.

## Boundary

Bone 1 remains open at the source-specific uniform two-channel factorization
of the signed old-carrier telescope.  This proof adds no spectral gap, Gate
3U estimate, finite-S sign, Burnol identity, or RH conclusion.
