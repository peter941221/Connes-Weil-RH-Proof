# 2437 — Route A family-factor interface

Date: 2026-10-02.

The family-term interface now exposes the exact three-factor decomposition
used by the evaluator: coefficient × bump/amplitude × complex phase.  Given
directed rectangles for those factors and an exact value-identification with
`externalFamilyValue2344`, Lean proves the resulting product rectangle contains
the family term.

This does not assert any factor endpoint bounds.  It converts the remaining
per-family obligation into independent certificates for the coefficient, bump
factor, and phase factor, followed by a value identity.
