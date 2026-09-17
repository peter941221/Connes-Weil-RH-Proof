# 1609: Wide Hardy support/Fourier support bridge

Date: 2026-09-18

## Result

`wideHardySupport_iff_wideFourierSupport` proves, for every bounded ambient
operator `A` and every nonnegative widened scale, the exact equivalence

`E_w H A = H A` iff `Q_w A = A`.

Here `H` is the Hardy--Titchmarsh involution, `E_w` is the widened radial
projection, and `Q_w` is the Fourier-support projection at that same scale.

## Role in S3/B4

The B4 wide-Hardy premise can now be supplied in the shorter Fourier-support
form.  This does not prove the premise for the actual Schur boundary dagger;
it identifies the remaining analytic producer as the Fourier defect of that
operator.  No RH, positivity, or Hilbert--Schmidt conclusion is asserted.

## Acceptance

Focused log:
`/home/peter/rh/build-logs/1609_wide_hardy_fourier_bridge_fix.log`.
It reports `Build completed successfully (4071 jobs)`, zero `error:` lines,
zero `sorryAx`, and one standard-axiom audit print.
