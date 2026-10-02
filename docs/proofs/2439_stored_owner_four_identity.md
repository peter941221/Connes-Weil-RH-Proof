# 2439 — Stored owner index-4 identity

Date: 2026-10-02.

An exact rational readback checks the index-4 base and correction coefficients
used by the existing Lean nonzero-owner lemmas against the binary64 hex values
in the audited 2275 owner capture.  All four real/imaginary rational values
match exactly.

This closes only the index-4 identity used by the owner guard.  It does not
import the full 30-coefficient table into Lean, and it is not a pointwise
`correctedPhysical` interval certificate.
