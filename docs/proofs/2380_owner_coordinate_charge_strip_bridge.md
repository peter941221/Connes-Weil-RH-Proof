# 2380 — owner-level coordinate-charge strip bridge

Date: 2026-10-02.

The Lean theorem
`correctedPhysical_stripNorm_le_of_actual_coordinate_charge2359` now consumes
two explicit node hypotheses: an upper bound at the stored/actual coordinate
and a transfer inequality from the exact affine coordinate to that actual
coordinate.  It adds the uniform transfer charge through the audited finite
composite-node identity and then invokes the existing owner derivative and
curvature budget theorem.

The file's `#print axioms` audit passes.  This is an analytic interface
theorem only; it does not import the 2374/2378 numerical values or close the
directed numerical node certificate.
