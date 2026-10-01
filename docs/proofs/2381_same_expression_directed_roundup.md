# 2381 — same-expression directed roundup

Date: 2026-10-02.

After the 2378 mismatch, the evaluator now performs a second MPFR directed
accumulation on the binary64 `RNDU` conversion of each already-directed term.
This is the same term expression followed by an explicit upward conversion;
it is not the old nearest-float `math.hypot * math.exp` path.

On the 1001-node control, all four channels satisfy
`directed_term_binary64_roundup_integrals >= directed_mpfr_term_accumulation_integrals`,
and the existing directed readings are unchanged.  A 300-second bounded
776611-node replay produced no artifact, so this remains a local control and
not a full-grid certificate.
