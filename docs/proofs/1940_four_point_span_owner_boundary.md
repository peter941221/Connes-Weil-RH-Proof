# Record 1940: signed-remainder owner boundary

## Finding

The signed remainder theorem from record 1939 is formally valid for an
`OrbitG8Geometry rho g`, where `g` is the selected owner produced by the G8
orbit construction. It cannot by itself certify the four-point span

```text
h(lambda) = u - lambda * g.
```

The four-point consumer uses `h(lambda)` and its convolution square. No
`OrbitG8Geometry rho h(lambda)` construction is currently available, and
the existing healthy-owner sign theorem points in the opposite direction for
the original `g`.

## Route consequence

The 1939 signed decomposition is retained as an owner-preserving tool, but it
must not be fed into Cut 2 by silently replacing `h(lambda)` with `g`. The
next genuine producer brick is an exact physical-kernel expansion for the
same four-point span owner, followed by a strict signed budget for that owner.
The span's already-formal parabola and high-shell prefix wires remain the
consumers.

This is a scoped owner-mismatch correction, not a no-go for the four-point
route and not an RH claim.

## Evidence

Formal sources: `C1G8R0OrbitGeometry.lean`,
`C1FourPointSpanGateCertificate.lean`, and
`C1FourPointPrimePrefixReduction.lean`. The latter's new theorem is audited
in record 1939; its quantified owner is explicitly `OrbitG8Geometry rho g`.
