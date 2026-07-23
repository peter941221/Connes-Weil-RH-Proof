# Proof 522: actual Schur graph-support defect

## Result

The canonical graph cosine is an ambient algebra element.  It cannot be
silently treated as an element of the projected carrier.  This module names
the missing component:

```text
graphSupportDefect(data, cosine)
  = (1 - data.projection) * cosine.
```

For an arbitrary cosine, the Euler graph action therefore has the exact form

```text
eulerGraphAction cosine (graphSine cosine)
  = (schurFrame cosine + graphSupportDefect data cosine, 0).
```

The defect is an equality ledger, not an estimate and not a support theorem.
In particular, no claim is made that the canonical graph cosine is fixed by
the projection.

## Projected graph-frame transport

The source-owned projected graph frame satisfies the actual carrier identity

```text
(1 - scalar * transport)
  * (projection * cosine + graphSine cosine)
  = schurFrame cosine.
```

This is proved from the four transport corners and the graph-sine lower row;
the proof keeps the complementary support equations explicit rather than
using an unsupported graph-cosine assumption.

If `inverse` is a left inverse of the Euler factor, the valid inverse readback
is consequently

```text
inverse * schurFrame cosine
  = projection * cosine + graphSine cosine
  = cosine + graphSine cosine - graphSupportDefect data cosine.
```

The defect is not multiplied by `inverse` in the final expression.  That
stronger-looking variant is false for a general noncommutative ring: after
the inverse cancels the Euler factor, the result is the projected cosine, and
`projection * cosine = cosine - (1 - projection) * cosine` is a purely
algebraic identity.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphSupportDefect.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphSupportDefectAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The source and audit contain no `sorry`, `admit`, or user axiom declaration.
The audited declarations are expected to use only
`[propext, Classical.choice, Quot.sound]`.

This proof exposes the graph-support defect for the later Gate 3U producer.
It does not control that defect, identify it with a physical post-Q
remainder, prove Gate 3U, prove the finite-S sign, supply Burnol's identity,
or prove `_root_.RiemannHypothesis`.
