# 2414 — repaired full-grid replay

Date: 2026-10-02.

After changing the public point-box hull margin to the named four-ULP value,
the 776611-node Linux replay was regenerated with 16 workers and span length
20001.  The artifact has matching current source/evaluator hashes.  Its
independent readback passes 39 finite nonnegative span witnesses with lengths
`38×20001+16573`.

This is a replay and provenance result, not a proof that the stored directed
floating-point witness dominates the mathematical span quantity.
