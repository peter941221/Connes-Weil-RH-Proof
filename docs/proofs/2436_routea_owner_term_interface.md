# 2436 — Route A corrected-owner term interface

Date: 2026-10-02.

The owner bridge now proves in Lean that a rectangle enclosing each of the 30
external family terms encloses their finite sum as the actual
`correctedPhysical` value.  It uses the existing theorem
`externalPhysical2344_eq_correctedPhysical`, so no parallel owner or alternate
normalization is introduced.

The theorem is still conditional on the per-family rectangle hypotheses.  It
does not import MPFR endpoints; those hypotheses are the remaining numerical
certificate input.
