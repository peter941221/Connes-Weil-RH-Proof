# 1765 — Annular two-wing majorant reaches the S3 square-sum consumer

Date: 2026-09-21. Classification: FORMAL assembly, same-owner readback. RH
is not claimed.

`C1G8R3AnnularMassConsumer.lean` adds
`sourceCompressedRoot_squareSum_of_annular_wing_majorant`.  It applies the
abstract two-sided cosine-rule assembly to the actual
`sourceRootAnnularOutputWindow` columns, then feeds the resulting uniform
annular bound into `sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound`.

The theorem leaves the analytic majorant, its pointwise kernel-diagonal bound,
and both wing integrals as explicit premises.  Thus it reconnects the paper
mass-face target without manufacturing an estimate, a sign, or an RH
conclusion.

Focused verification must include the paired Audit leaf and the standard
axiom/sorry checks.
