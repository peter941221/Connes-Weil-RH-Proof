# Proof 575: raw physical old-carrier kernel

## Result

Proof 574 reduced the physical Douglas target to two operators on the same
finite-S carrier:

```text
W  = suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
R0 = suffixActualBandRawPhysicalReducedRow
```

The new source theorem proves that `W` is injective.  Therefore the exact
kernel condition required by Douglas is satisfied:

```text
W y = 0  ->  R0 y = 0.
```

The old-carrier map also has the exact two-channel energy ledger:

```text
||W y||²
  = ||primeEulerAmbientLossFactor(p)† y||²
    + ||(I - newFrame newFrame†) transport† y||².
```

After pulling back through the old isometric frame, the second coordinate is
the actual rectangular boundary adjoint:

```text
||W oldFrame x||²
  = ||primeEulerAmbientLossFactor(p)† oldFrame x||²
    + ||boundary† x||².
```

## Kernel diagram

```text
W y = 0
  |
  +--> ambient channel: factor† y = 0
  |
  +--> boundary channel: (I - P_new) T† y = 0
          |
          +--> T† y = newFrame(q)
  |
  +--> factor† y = 0
          |
          +--> (I - T T†) y = 0
                  |
                  +--> T T† y = y
  |
  +--> y = T(newFrame(q))
          |
          +--> y = oldFrame(transition(q))
  |
  +--> ambient-loss-column injectivity
          |
          +--> y = 0
```

The step `I - T T† = factor * factor†` is the existing exact ambient
co-defect identity.  The final injectivity is the existing radial-support
ambient-loss theorem; it is not a new axiom or a closed-range estimate.

## Lean owner

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction.lean` now contains:

```text
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_normSq_eq_channels
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_oldFrame_normSq_eq_actual_channels
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_eq_zero_iff_channels_eq_zero
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_injective
suffixActualBandRawPhysicalReducedRow_eq_zero_of_oldCarrierAnalysis_eq_zero
suffixRawOldCarrierDomination_iff_exists_bounded_oldCarrierReadout
```

The focused audit is:

```text
ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReductionAudit.lean
```

## Boundary

Injectivity is necessary but not sufficient.  The remaining producer is still
the uniform graph-norm estimate:

```text
exists C >= 0,  forall y,
  ||R0 y||^2 <= C^2 ||W y||^2.
```

Equivalently, the algebraic quotient `R0 / W` must extend to a bounded map on
the closure of `range W`.  The existing ambient-loss injectivity and the
operator-norm residual bounds do not prove this extension.  No Gate 3U,
finite-S sign, Burnol identity, or RH theorem is claimed here.

The source module now makes this equivalence explicit: the old-carrier
domination holds exactly when there is a bounded readout
`readout : suffixEulerFrameAmbientBoundaryCarrier ->L sourceSoninCarrier`
with `readout ∘ W = R0` and `||readout|| <= C`.  The coframe telescope gives
the signed row identity, but no theorem in the current source turns it into
this bounded quotient estimate.  In particular, `W` is injective on the
infinite-dimensional global-log `L²` carrier; injectivity alone is not a
closed-range or lower-bound theorem.

## Verification

The Windows source was copied to the Ubuntu-24.04 WSL2 ext4 mirror before
the following commands:

```text
lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
result: 3331 jobs, PASS
lake build \
  ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReductionAudit
result: 3332 jobs, PASS
lake build ConnesWeilRH.Source.CCM25Concrete
  3843 jobs, PASS
lake build
  3924 jobs, PASS
```

The focused audit reports exactly `[propext, Classical.choice, Quot.sound]`
for the new declarations.  The WSL localhost-proxy warning and existing
repository linter warnings are environmental or pre-existing.  No `sorry`,
`admit`, or user axiom was added.
