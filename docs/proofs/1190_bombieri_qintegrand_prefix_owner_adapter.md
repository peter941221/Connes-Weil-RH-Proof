# 1190 — Bombieri qIntegrand prefix-owner adapter

## Status

**FORMAL owner alignment; P2 remains open.**

The remaining split-prefix obligation can now be stated in Bombieri's native
finite owner.  `BombieriQuadraticCanonicalQIntegrandPrefixP2BridgeData` carries
the same finite eigen/reciprocal data and asks only for

```text
Re(finite spectral prefix at the canonical cutoff)
  = Re((∫ qIntegrand(expSum γ z, expSum γ (dcoef γ z)))
       − endpointCorrection(t, γ, z)).
```

The existing formal identities

```text
KstarGram = ∫ qIntegrand − endpointCorrection,
Re⟨w,Hw⟩ = Re(KstarGram)
```

convert this data to `BombieriQuadraticCanonicalPrefixP2BridgeData`.  The
conversion then feeds the already-existing additive spectral-tail contract,
the finite positivity consumer, the P2 aggregate, and the pinned healthy-B5
`SourceRH` exit.

This does not assert that the selected orbit detector satisfies the
finite-prefix/qIntegrand equality.  That equality is still the sole open
analytic producer field on this Bombieri branch.

## Acceptance

Focused batch `p2-qintegrand-prefix-r6.log` completed successfully (3779
jobs), with no `error:` or `sorryAx`; audit outputs use only
`[propext, Classical.choice, Quot.sound]`.
