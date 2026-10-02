# 2441 — Route A phase-factor bounds

Date: 2026-10-02.

Lean proves that every phase factor
`Complex.exp ((t : ℂ) * Complex.I)` lies in the explicit rectangle
`[-1,1] + i[-1,1]`, using the exact sine/cosine representation and their
global bounds.

This is an analytic fallback enclosure, not the narrow evaluator-specific
phase interval used for cancellation control.  The latter remains a separate
directed endpoint certificate.
