# Proof 604: Uniform Joint-Gap Gate 3U Handoff

## Result

The gap-facing coframe producer now has a family-uniform wrapper:

```text
∀ p S,
  readout_(p,S) * oldCarrierAnalysis_(p,S)
    = coframeBoundaryMomentGap_(p,S) * oldFrame_(p,S)^†
```

The new structure is
`SuffixRawOldCarrierCoframeUniformJointGapReadoutData` in
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout.lean`.

Its exact downstream conversion is:

```text
uniform gap readout, bound B
  -> uniform signed-telescope readout, bound B
  -> old-carrier domination, bound 2B
  -> raw physical domination, bound 2B
  -> non-polar Douglas producer, bound ||D|| + 2B
```

The factor `2` is only the norm cost of the two coordinate projections of a
joint physical readout.  It is not a source estimate.

## Verification

The Windows source and the Ubuntu-24.04 ext4 mirror have identical SHA-256 for
the changed source module.  Verification passed:

```text
focused source module: 3368 jobs, PASS
import-facing axiom audit: PASS
CCM25Concrete aggregate: 3871 jobs, PASS
```

The seven audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.

## Remaining source obligation

Proof 604 does not construct the uniform readout.  The remaining Bone 1
theorem is still the source-specific signed Douglas estimate for the complete
adjacent gap / reduced row.  In particular, it must preserve the transition
skew and the adjacent cancellation; separate operator-norm bounds for the
orientation, residual, and known rows are insufficient.
