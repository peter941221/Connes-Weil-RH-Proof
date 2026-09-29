# 2203 — Matrix-level cancellation preflight

Date: 2026-09-29

This probe continues the active actual-owner consumer:

```text
actual source owner -> same-owner qw >= 0 -> SourceRH -> Mathlib RH.
```

Record 2202 showed that a componentwise endpoint-split bound is unusable for
the ill-conditioned interpolation solve. Record 2203 instead applies the
measured `m=3200` to `m=6400` matrix difference to the actual right-hand-side
solution vectors before taking the norm.

## Result

```text
matrix dimension                         30
||E||inf                                  9.183896645769796e-25
condition(A0)                             2.653731999607843e5

base   ||E c||inf                         3.328361160515191e-12
base   ||A0^-1 E c||inf                   4.473957160716424e3
base   direct solve difference            4.913431141035535e3

corr   ||E c||inf                         4.122398135445892e-9
corr   ||A0^-1 E c||inf                   4.909988267250998e6
corr   direct solve difference            5.478351481373936e6
corr   relative correction movement       about 9.6e-12
```

The action is much smaller than the coefficientwise worst-case radius from
2201. This is the expected cancellation structure and keeps the solve-side
perturbation far below the already screened `1e-6` relative coefficient error.

## Status

Status: `MATRIX-CANCELLATION-GO-CANDIDATE / UNPRICED`.

The difference matrix is still a stored floating quadrature comparison, so
this is not an outward certificate. It does, however, reject the inference
that the 2202 entrywise no-go closes the direct-product branch. The next
certificate target is an analytic bound on the matrix action `E c` (or an
interval residual assembled before taking entrywise moduli), followed by the
same owner transfer. No producer theorem or RH claim follows.

