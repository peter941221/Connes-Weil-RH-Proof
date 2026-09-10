# G8 P1 metric cutoff projection factorization

Date: 2026-09-11.

The import-facing leaf `C1G8P1MetricProjectionFactorization` proves the exact
same-owner identity
`g8PhysicalMetricCutoffOperator = K† G K`, where `G` is the ambient
`g8AdjointShearGram` and `K = sourceInclusion ∘ (sourceInclusion† ∘ rawCutoff)`
is the source-projected cutoff leg. The same leaf also proves the exact split
`rawCutoff = projectedCutoff + sourceCutoffComplementLeg`, so the unresolved
comparison is precisely the source-subspace projection defect: no equality
with the raw cutoff leg, and no finite-trace equality, is asserted.

This is FORMAL P1 owner alignment. It does not identify metric boundary maps
with radial crossings, prove the finite-prime readback, close the P2 remainder
or sign, or advance P3.

Evidence: `1490_g8_p1_metric_projection_factorization.log`, owning and audit
targets green, zero `error:`/`sorryAx`; both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Cross-import evidence: `1491_g8_p1_p2_p3_cross_import.log` rebuilt the two
projection declarations together with the diagonal P1, canonical P2, and
same-detector P3 leaves (3979 jobs), with zero `error:`/`sorryAx` and the same
three-axiom audit set.

RH is not claimed.
