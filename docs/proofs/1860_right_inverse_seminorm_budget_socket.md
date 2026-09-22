# 1860 - Right-inverse coefficient budget socket

Date: 2026-09-23.

Status: Formally verified in Lean; consumer wiring.

The theorem
`affineResidualCorrection_seminorm_le_rightInverse_budget` connects the
actual `affineResidualCorrection` construction to the finite coefficient
budget from record 1857. Its right-hand side is the finite sum over the
support of `windowedMellinRightInverse`, weighted by the zero-order seminorm
of each window basis test.

This is not yet a budget certificate: the finite sum has not been bounded by
`1/2`. It is the exact producer-facing socket for that certificate and keeps
the Mellin right inverse and seminorm owner explicit.

Verification: WSL focused build `rightinverse-budget-1860.log`; successful
footer, zero `error:` lines, zero `sorryAx`, and standard three-axiom audit.
