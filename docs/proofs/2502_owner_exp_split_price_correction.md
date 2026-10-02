# Record 2502 — corrected-input exponential split price

The 2500 price was tied to the superseded 2499 endpoint direction.  Re-running
the same formal split price with the corrected 2501 inputs gives a maximum
finite binary64 split/direct-MPFR ratio of
`1.000000000000138` over 9,856 representable readings; 138 readings
underflowed binary64.  This is routing evidence only.  The Lean split theorem
remains the soundness anchor, and the hcell premise is still open.
