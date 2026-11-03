# 3297 Route A rational endpoint tail diagnostic

Record 3297 mirrors the audited 3289 rational endpoint with high-precision
`Decimal` arithmetic.  It is a diagnostic magnitude probe only: Decimal
arithmetic is not directed rounding, the output is not imported into Lean, and
the rows are not endpoint-dominance theorems.

The probe was run at 80 decimal digits on representative cells, including the
negative minimum region around index 16923 and cells near support transitions.
The central negative cells are close: at index 16923 the diagnostic gap
`rational upper - Arb value upper` is about `5.06e-31`.  That observation does
not close the proof because the endpoint still has to be computed and compared
in Lean with exact rational arithmetic.

The same construction fails badly away from the central negative region:

```text
index   rational endpoint probe       Arb value upper       probe - Arb
12000   +34.4019310106600              -0.1426155917566      +34.5445466024166
15000   +39.0068862100701              -4.4187427343754      +43.4256289444456
16000   +21.6713805589606              -7.3143942710979      +28.9857748300585
16500   +6.4587116090025               -8.5776872026484      +15.0363988116510
30000   +1.3712762484847               -0.0010148974436651   +1.3722911459284
40959   +0.0000226819815154             0                    +0.0000226819815154
```

The failure mechanism is the tail branch inherited from 3285.  For an active
cell with `t <= -8`, `ratTailBumpInterval3285` replaces the actual factor
`exp(-30 + t)` by the uniform upper `exp(-38)`.  The owner coefficients are
roughly `10^14` in magnitude, so this turns a genuinely negligible support
edge into an interval contribution of order one.  At index 12000, the summed
family rectangle is approximately

```text
real in [-8.36556, 8.85863]
imag in [-5.14965, 5.82601]
```

before multiplication by the positive weight near `3.88343`; its upper endpoint
is therefore positive even though the signed Arb value is negative.

```text
3289 endpoint
      |
      +--> 3287 bump interval
              |
              +--> central branch: local Taylor bound
              |
              +--> tail branch: uniform exp(-38)  <-- named obstruction
```

This is a diagnostic no-go for consuming the 3294 block manifest through the
current 3289 endpoint function.  It does not reject the owner or the 3273
Taylor-6 replay.  A viable next proof object needs a tail interval that depends
on the actual rational `t` (or an equivalent support-edge partition) while
preserving signed cancellation.

The exact Fraction mirror in `scripts/routea_rational_endpoint_probe_3296.py`
was also corrected to the repository's `C1RouteARationalCellBump3287.lean`
filename.  A one-cell exact run exceeded five minutes without producing a
value, so it is retained as a performance diagnostic rather than a production
evaluator.

Nonclaims:

- no Lean endpoint-dominance theorem;
- no imported JSON or Decimal conclusion;
- no full-line tail proof;
- no producer_go, SourceRH, or RH claim.
