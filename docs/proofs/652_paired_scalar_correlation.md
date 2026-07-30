# Proof 652: paired scalar correlations

## Result

Proof 652 pairs adjacent terms of Proof 651's alternating prefix before any
absolute value. For even horizons it proves

```text
sum_(k<2N) term_k
  = sum_(j<N) (term_(2j) + term_(2j+1)),
```

and for odd horizons it adds exactly one terminal correlation. The adjacent
pair is the difference of correlations at translations `2j log p` and
`(2j+1) log p`.

A route-uniform bound on the paired prefix plus its one terminal term is
sufficient for the scalar target and hence for the existing Bone 1
consumers.

## Boundary

Pairing preserves cancellation but supplies no estimate. The paired envelope
is still an explicit premise at this stage.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorPairedScalarCorrelation.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorPairedScalarCorrelationAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
