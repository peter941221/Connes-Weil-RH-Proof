# Proof 597: old-carrier coframe orientation ledger

## Result

Proof 597 keeps the old-carrier signed telescope in the correct rectangular
orientation.  The exact decomposition is

```text
signed telescope
  = metric orientation row
    + metric residual row
    + metric inclusion row
    + forward-complete row.
```

The metric coframe recurrence is expressed with the adjoint of the actual
Schur transition.  Its orientation gap is read back as

```text
(survivor residual + boundary residual)^dagger
  * suffixEulerAmbientProduct(S).
```

The row carriers are explicit rectangular maps
`finiteSCarrier ->L frameCarrier`.  The detector leg is the actual
`detectorOperator * sourceInclusion` direction used by the existing leakage
owner; it is not replaced by a source-complement factor.

## Bone 1 boundary

This is an exact ledger, not the missing family-uniform Bone 1 factor.  The
orientation and survivor-residual rows still need a bounded readout through
the actual old-carrier physical analysis.  No spectral gap, injectivity, norm
bound, Gate 3U estimate, finite-S sign, Burnol identity, or RH theorem is
claimed here.

```text
signed telescope
        |
        +--> orientation row       [hard factor producer]
        +--> residual row          [hard factor producer]
        +--> inclusion/forward    [separate bounded bookkeeping]
```

The source owner remains the two-channel factor contract in Proof 594.  In
particular, a bounded row by itself cannot be promoted to a physical readout
without a source-specific quotient/factor theorem.

## Lean owners

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedgerAudit.lean
```

The focused source and import-facing audit are intended to use only
`[propext, Classical.choice, Quot.sound]`.
