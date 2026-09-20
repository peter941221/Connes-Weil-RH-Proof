# 053 - Orbit signed credit-deficit budget

Date: 2026-09-20.

Authority: supporting formal route screen under 003/004. Route selection is
unchanged.

Record 1745 formalizes the exact decomposition of the selected detector's
finite visible-prime profile aggregate into positive credit and negative
deficit. For the same `OrbitG8Geometry` owner, the semi-local gate is
equivalent to `archimedeanTerm + credit <= deficit`.

This closes an interface ambiguity, not the inequality itself. No pointwise
sign, frozen prime set, or new owner is introduced. The live producer must
prove the signed balance on the actual finite range supplied by the detector
support cutoff. Evidence is the paired Lean audit and
`shortest_route_20260920_signed_budget_v7.log`.
