# Proof 650: weak alternating primitives

## Result

Proof 650 converts Proof 649's pointwise vector bound into an equivalent
scalar matrix-coefficient bound. For the route-valid finite-horizon family
`H_i`, Lean proves

```text
forall u, exists M_u, forall i, ||H_i u|| <= M_u
  <->
forall u v, exists M_(u,v), forall i, |<H_i u,v>| <= M_(u,v).
```

The reverse direction applies Banach--Steinhaus on the target Hilbert space.
Consequently the weak premise is sufficient for the existing route-uniform
raw and renewed Bone 1 consumers.

## Boundary

No scalar matrix-coefficient bound is proved. The point of this reduction is
to expose a signed scalar quantity before any absolute value is taken.

```text
+-----------------------------------------------+----------+
| layer                                         | status   |
+-----------------------------------------------+----------+
| weak scalar bound <-> pointwise vector bound  | proved   |
| weak scalar bound -> raw/renewed consumers    | proved   |
| actual route-uniform scalar bound             | open     |
| Bone 1 / Gate 3U / sign / Burnol / RH         | open     |
+-----------------------------------------------+----------+
```

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorWeakAlternatingPrimitive.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorWeakAlternatingPrimitiveAudit.lean
```

The combined Proof 650--659 audit passed with `3454` jobs. Audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.
