# 1854 - Indexed geometry consumer wiring

Date: 2026-09-23.

Status: Formally verified in Lean 4; consumer wiring only.

The existing `exists_orbitG8Geometry_of_sourceNontrivialZero_right` producer
now calls `orbitG8Geometry_of_indexed_raw_construction` for its final package
assembly. The selected orbit index and all same-owner raw fields therefore
flow through the explicit-index constructor before the geometry is exported.

This preserves the old producer behavior and does not add a budget or
positivity claim. The all-index healthy assembly remains the next source of
indexed raw data; strict base contraction and detector-specific signed
positivity are unchanged.

Verification: focused Audit log `1854_geometry_consumer.log`, successful
footer, zero `error:` lines and no `sorryAx`.
