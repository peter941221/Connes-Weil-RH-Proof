# 2597 analytic matrix interval interface

The generator imports all 900 rational rectangles from the 2351 analytic-matrix
witness and emits them as Lean `ComplexRect2427` data. The Lean theorem exposes
the exact soundness premise needed by the 2338 route: every rectangle must
contain the corresponding `ownerMomentMatrix2351` analytic integral.

This is intentionally conditional. JSON, Arb, and the witness hash are not
Lean proofs. The next certificate must prove the 900 containment claims from a
verified interval integrator; after that, the interval arithmetic layer can be
connected to the 2595 defect payload.
