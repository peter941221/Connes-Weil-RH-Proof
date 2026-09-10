# G8 P1 local boundary orthogonality (2026-09-11)

The import-facing leaf `C1G8P1BoundaryOrthogonality` proves the exact
same-owner Schur geometry

```text
newFrame† ∘ boundaryDagger = 0.
```

for every visible-prime step. The proof unfolds the rectangular boundary
dagger as `(I - newFrame newFrame†) ∘ transport† ∘ oldFrame` and uses the
new-frame isometry. Thus each local boundary output is orthogonal to its
corresponding new-frame range. This is FORMAL P1 structural transport
evidence, audited by `C1G8P1BoundaryOrthogonalityAudit`.

Build evidence: `1450_g8_p1_boundary_orthogonality.log` completed
successfully (3246 jobs), with zero `error:` and zero `sorryAx`; the audit
prints only `[propext, Classical.choice, Quot.sound]`.

This does not identify the metric boundary output with a radial prime-power
crossing, prove the finite metric trace equality, close the P2 remainder or
sign, or provide the P3 producer.
