# Proof 651: scalar correlation primitive

## Result

Proof 651 expands every weak matrix coefficient from Proof 650 as the exact
finite signed prime-log correlation sum

```text
star(s_p^(-1)) * sum_(k<N)
  <(-1)^k U_(k log p) u, C_(p,S)^* v>.
```

The complete coupled target `C_(p,S)` remains intact. Its outer, reflected,
second-support, and prolate components are not separated. Lean proves that a
route-uniform bound on these scalar sums is equivalent to the weak target and
therefore feeds the existing raw and renewed Bone 1 consumers.

## Boundary

The displayed correlation sum is an identity, not an estimate. Taking an
absolute value term by term would discard the alternating cancellation which
the reduction was built to preserve.

```text
+---------------------------------------------+----------+
| layer                                       | status   |
+---------------------------------------------+----------+
| readout coefficient = signed finite sum    | proved   |
| scalar-sum bound <-> weak target            | proved   |
| uniform bound for the actual signed sum     | open     |
+---------------------------------------------+----------+
```

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorScalarCorrelationPrimitive.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorScalarCorrelationPrimitiveAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
