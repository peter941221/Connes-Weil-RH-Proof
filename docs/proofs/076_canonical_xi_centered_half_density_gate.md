# 076 Canonical Xi Centered Half-Density Gate

Date: 2026-07-12

Result: the Xi-quotient orbit symmetry is compatible with convolution-square
involution only after the exact half-density centering. The current raw log
pullback cannot be reused as the Plan 025 owner.

## Coordinate

Write

```text
u = s-1/2.
```

For the centered half-density `h`, use

```text
H(u) = integral_R exp(u*x) h(x) dx.
```

The additive involution `h*(x)=conj(h(-x))` gives

```text
H_star(u) = conjugate(H(-conjugate(u))).
```

Returning to the source variable, `u -> -conjugate(u)` is exactly

```text
s -> 1-conjugate(s).
```

Thus the convolution-square pairing and the completed-Xi functional/conjugate
orbit use the same points.

## Existing Owner Guard

`SelectedYoshidaBridge.logPullbackRaw` currently uses

```text
g(exp x)
```

without the half-density factor. Its `laplaceAt` therefore uses the uncentered
Mellin variable directly, and `laplaceAt_involution` pairs `s` with
`-conjugate(s)`. That concrete object must not be identified with the centered
Xi quotient by `rfl`, support equality, or symbolic transport.

The Plan 025 owner must instead expose the half-density conversion and the
equation `u=s-1/2` as data-bearing definitions.

## Decision

```text
Xi symmetry versus centered square: matched
reuse current raw log owner: rejected
new centered half-density owner: required after analytic gates
Plan 025: survives
```
