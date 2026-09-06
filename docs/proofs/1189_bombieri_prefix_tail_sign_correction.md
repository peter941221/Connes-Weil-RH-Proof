# 1189 — Bombieri prefix/tail sign correction and split producer socket

## Status

**FORMAL interface correction; P2 remains open.**

The established shell partition is additive.  For every cutoff `N`, the
healthy same-owner spectral value satisfies

```text
qw(g) = Re(finite spectral prefix at N) + Re(high-shell tail at N).
```

Consequently the Bombieri spectral-tail owner must use the additive equation
`qw = Re⟨w,Hw⟩ + Re(tail)` once the finite-prefix identification is supplied.
The generic residual socket remains subtractive, so its adapter uses the
explicit residual `-Re(tail)`.  This preserves the already-proved estimate
`|tail| ≤ normTail ≤ Re⟨w,Hw⟩` without changing the positivity consumer.

The new formal `BombieriQuadraticCanonicalPrefixP2BridgeData` narrows the
remaining producer obligation to

```text
Re(finite spectral prefix at canonical cutoff) = Re⟨w,Hw⟩.
```

Its conversion to the canonical tail contract and the aggregate/pinned
healthy-B5 `SourceRH` exits are formal.  The prefix-to-Bombieri identification
is not present in the repository and remains the sole open analytic field for
this split Bombieri branch.

## Acceptance

Focused batch `p2-prefix-socket-r7.log` completed successfully (3779 jobs),
with no `error:` or `sorryAx`; audit outputs use only
`[propext, Classical.choice, Quot.sound]`.
