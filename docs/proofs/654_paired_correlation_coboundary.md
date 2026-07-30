# Proof 654: paired correlation coboundary

## Result

Proof 654 moves each adjacent correlation difference onto the complete
target adjoint. With `a = log p` and `C = C_(p,S)`, Lean proves

```text
<U_(2j a)u,C^*v> - <U_((2j+1)a)u,C^*v>
  = <U_(2j a)u,(I-U_(-a))C^*v>.
```

The target is also exactly the adjoint of the forward coboundary:

```text
(I-U_(-a)) C^* = [C(I-U_a)]^*.
```

The conjugate-linearity of the first inner-product coordinate fixes the
inverse-translation orientation. The paired-adjoint-coboundary envelope is
equivalent to Proof 649's pointwise target.

## Boundary

All four physical branches remain coupled inside `C`. Proof 654 licenses no
separate branch estimate and does not bound the coboundary correlations.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorPairedCorrelationCoboundary.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorPairedCorrelationCoboundaryAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
