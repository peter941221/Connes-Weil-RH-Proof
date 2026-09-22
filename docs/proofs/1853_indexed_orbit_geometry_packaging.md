# 1853 - Indexed OrbitG8 geometry packaging

Date: 2026-09-23.

Status: Formally verified in Lean 4; producer interface progress only.

The theorem `orbitG8Geometry_of_indexed_raw_construction` packages an already
verified raw selected-owner construction into `OrbitG8Geometry` with an
explicit caller-supplied `orbitIndex`. It preserves the base and correction,
support, interpolation, centered orbit sum, square-zero control, tail fields,
and derives the finite visible-prime cutoff from the same support owner.

This removes the old packaging boundary where `orbitIndex` existed only as a
field of an existentially returned geometry. The theorem does not manufacture
the raw construction, prove strict base contraction, or prove the signed
semi-local positivity needed for RH.

Verification: focused Audit log `1853_indexed_geometry_pack.log`, successful
footer, zero `error:` lines and no `sorryAx`.
