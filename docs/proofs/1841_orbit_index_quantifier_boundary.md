# 1841 - Orbit-index quantifier boundary after the geometric budget reduction

Date: 2026-09-22.

Status: Formal route audit; no new positivity or RH claim.

Record 1840 proves that a strict factor contraction eventually beats any
positive scalar budget for some natural index. The current raw geometry
producer, however, has the shape

```text
for each rho, exists g, exists geometry : OrbitG8Geometry rho g
```

and the constructor internally selects `geometry.orbitIndex`. It does not
provide

```text
for each rho and prescribed n, exists g, geometry with orbitIndex = n
```

Consequently the 1840 eventuality theorem cannot yet be composed with the
existing owner package. The missing theorem is a prescribed-index realization
result, or a monotone index-lifting theorem preserving the interpolation,
fourth-order tail, square-zero, support, visible-prime cutoff, and
Archimedean-margin fields.

Evidence: `C1G8R0OrbitGeometry.lean` exposes `orbitIndex` as a field of the
existential package, while
`exists_orbitG8Geometry_of_sourceNontrivialZero_right` constructs the package
after choosing the correction and index internally. No current declaration
quantifies over a caller-supplied index.

This finding narrows the next producer-side proof target. It does not refute
the route and does not claim RH.
