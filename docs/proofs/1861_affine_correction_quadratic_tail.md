# 1861 - Affine correction quadratic-tail API

Date: 2026-09-23.

Status: Formally verified in Lean; explicit-family producer interface.

The theorem `affineResidualCorrection_with_quadratic_decay` proves that the
actual `affineResidualCorrection` built from
`windowedMellinRightInverse` has the same uniform quadratic vertical-tail
constant API as the older existential residual correction. Its proof applies
the existing compact-window tail estimate to the explicit finite combination.

This removes the tail API mismatch for an eventual explicit-coefficient base
producer. It does not prove the coefficient/basis seminorm budget, the
detector-specific signed positivity, or RH.

Verification: WSL focused build `affine-tail-1861.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and standard three-axiom audit output.
