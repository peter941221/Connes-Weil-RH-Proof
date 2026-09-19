# 1717 — Shifted-Hardy summability does not yet transfer to S3

Date: 2026-09-20

## Verdict

The committed shifted-Hardy result is not the missing S3 estimate.  The
theorem `doubledShiftHardyInteriorCompression_summable` proves square-summable
columns for

```text
(I - P) K_b (I - P),   K_b = T_(2b) H,
```

after the exact doubled-shift transport.  The live S3 target is instead

```text
J† (E Q E) C J,
```

where `J` is the source-carrier inclusion, `E` the radial projection, `Q`
the Fourier-support projection, and `C` the selected root convolution.

The repository contains exact conjugation formulae for the first operator and
the exact decomposition of the second into a Hardy corner minus a square-
summable prolate correction, but no equality, factorisation, or bounded-ideal
estimate connecting the two.  In particular, the root convolution `C` and
the source inclusion `J` cannot be silently dropped from the shifted-Hardy
consumer.

## Exact remaining producer

By the committed records 1706, 1708, and 1711–1713, S3 is equivalent to a
uniform bound for the post-Tonelli pointwise kernel diagonal of the annular
root output.  A valid next theorem must therefore prove an estimate of the
form

```text
sup_x  sum_i |(C J e_i)(x)|^2  < infinity
```

in the appropriate representative/integrated formulation, or an equivalent
finite annular trace bound.  The shifted-Hardy theorem may be used only after
an independently proved factorisation of this diagonal through its operator.

## Status

This is a formal interface audit, not a no-go theorem for S3 and not a
numerical claim.  The healthy CompactLog B5 route remains active; the
consumer is unchanged and the analytic kernel-diagonal estimate remains
OPEN.
