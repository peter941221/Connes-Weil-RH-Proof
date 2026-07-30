# Proof 578: old-carrier block reduction

## Result

The old-carrier spectral-gap route is unnecessary for this target.  Let

```text
W  = suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
R0 = suffixActualBandRawPhysicalReducedRow
E  = oldFrame * oldFrame†
Q  = W† W = I - T * newFrame * newFrame† * T†.
```

The existing intertwining identity gives

```text
T * newFrame * newFrame† * T†
  = oldFrame * transition * transition† * oldFrame†.
```

Therefore `Q` commutes with the old-frame projection `E`.  The raw reduced
row satisfies `R0 * (I - E) = 0`, so its output depends only on the old-frame
component.  The old-carrier energy splits orthogonally into the old-frame
component and its complement.

```text
                    y
                    |
          +---------+---------+
          |                   |
       E y = oldFrame oldFrame† y    (I-E)y
          |                   |
          |                   +--> R0((I-E)y) = 0
          |
          +--> source vector oldFrame† y
                    |
                    v
             original signed raw row
```

## Lean owner

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction.lean` proves:

```text
suffixEulerFrameTransportNewProjection_eq_oldFrame_block
suffixEulerFrameOldCarrierGram_commutes_oldFrameProjection
oldCarrierAnalysis_normSq_eq_oldFrame_part_add_complement_part
suffixRawOldCarrierDomination_iff_rawDomination
```

The final equivalence has the same bound in both directions.  Its reverse
direction uses the existing packed physical energy identity, so it keeps the
two signed physical channels summed.

## Boundary

This closes the old-carrier extension mismatch.  It does not prove the common
source-side inequality itself.  The actual 3U bottom remains the uniform
signed raw Douglas estimate for `SuffixRawAmbientBoundaryDomination`; no
spectral gap, separate row norm, or triangle estimate is inferred.

No Gate 3U sign theorem, Burnol identity, or RH theorem is claimed.
