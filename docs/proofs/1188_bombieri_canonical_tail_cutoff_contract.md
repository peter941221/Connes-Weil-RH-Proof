# 1188 — Canonical Bombieri spectral-tail cutoff contract

## Status

**FORMAL interface tightening; P2 remains open.**

The new `bombieriSpectralTailCutoff` is chosen from the already-proved strict
finite Bombieri main-term margin and the same-owner shell-tail convergence.
Its specification proves that the norm tail at this cutoff is strictly below
`Re⟨w,Hw⟩`.

`BombieriQuadraticCanonicalSpectralTailP2BridgeData` packages the Bombieri
eigenvector, reciprocal relation, and one producer-facing equation:

```text
qw(g) = Re⟨w,Hw⟩ − Re(high-shell spectral tail at canonical cutoff).
```

The conversion to the residual socket, aggregate owner, and pinned healthy-B5
`SourceRH` exit is formal and axiom-clean. The remaining analytic task is now
exactly this same-owner decomposition; no independent tail-bound field is
required.

## Acceptance

Focused batch `p2-canonical-cutoff-r3.log` completed successfully (3779 jobs),
with no `error:` or `sorryAx`; audits report only
`[propext, Classical.choice, Quot.sound]`.
