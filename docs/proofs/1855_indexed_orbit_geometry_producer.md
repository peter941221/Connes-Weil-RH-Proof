# 1855 - Indexed OrbitG8 geometry producer

Date: 2026-09-23.

Status: Formally verified in Lean 4; producer-side interface reduction.

The theorem
`exists_indexed_orbitG8Geometry_of_sourceNontrivialZero_right` starts from
the all-index healthy raw assembly. It fixes the base, threshold, correction,
and correction tail constant before exposing the orbit count. Every count
whose explicit quadratic tail is below one is then packaged as a complete
`OrbitG8Geometry` on the same selected owner.

This is the prescribed-index realization needed by the geometric budget
route. It still assumes neither the strict base seminorm contraction nor the
detector-specific semi-local signed positivity, so it is not an RH proof.

Verification: focused Audit log `1855_indexed_producer_final2.log`, successful
footer, zero `error:` lines and no `sorryAx`.
