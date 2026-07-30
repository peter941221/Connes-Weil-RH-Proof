# Proof 655: one-step target size

## Result

At horizon one the alternating polynomial is the identity. Proof 655 therefore
extracts the necessary Bone 1A size gate

```text
sup_(route-valid p,S) ||s_p^(-1) C_(p,S)|| < infinity.
```

It also proves that the canonical ambient extension has no norm loss:

```text
C_(p,S) = Interior_(p,S) newFrame_S^*,
||C_(p,S)|| = ||Interior_(p,S)||.
```

The existing paired scalar/coboundary target necessarily implies this
horizon-one bound.

## Boundary

Proof 645 controls `rho_(p::S) Interior_(p,S)`. The suffix scalar can collapse
on long lists, so that estimate does not control `s_p^(-1) C_(p,S)`. Proof
655 isolates the missing condition; it does not prove it.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorOneStepTargetSize.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorOneStepTargetSizeAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
