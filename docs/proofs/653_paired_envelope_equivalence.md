# Proof 653: paired envelope equivalence

## Result

Proof 653 proves that Proof 652's pairing is an equivalent reformulation, not
a stronger analytic hypothesis. The paired prefix is the raw prefix at
horizon `2N`; the terminal term is the difference between horizons `2N+1`
and `2N`.

```text
paired envelope bound B -> raw prefix bound B,
raw prefix bound B       -> paired envelope bound 3B.
```

Thus the paired envelope, the scaled scalar correlation family, the weak
matrix-coefficient family, and Proof 649's pointwise family have the same
existence-level content.

## Boundary

The factor-three reverse estimate is algebraic. Neither side of the
equivalence is shown to have a route-uniform finite bound.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorPairedEnvelopeEquivalence.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorPairedEnvelopeEquivalenceAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
