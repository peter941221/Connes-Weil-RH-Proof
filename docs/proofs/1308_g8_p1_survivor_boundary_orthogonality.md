# G8 P1 survivor--boundary orthogonality (2026-09-11)

The Schur--polar telescope now has a second exact same-owner consequence:

```text
newSuffixFrame(λ, [])† ∘ (suffixEulerBoundaryOutputMaps λ S).sum = 0.
```

The proof combines the ambient-product intertwining, its adjoint, the terminal
frame isometries, and the full boundary telescope. It therefore shows that the
aggregate metric boundary output is orthogonal to the terminal survivor before
the inverse-Gram square-root factor is applied. This is FORMAL P1 geometry;
the result does not identify the aggregate with radial prime-power crossings
or provide a positivity/sign estimate.

Build evidence: `1461_g8_p1_boundary_sum_orthogonality_audit.log` completed
successfully (3247 jobs), with zero `error:` and zero `sorryAx`; the paired
audit prints only `[propext, Classical.choice, Quot.sound]` for both local and
aggregate orthogonality declarations.

Metric-to-radial transport, finite metric trace equality, the P2 remainder and
sign, and the P3 producer remain open.
