# Record 2528 — signed pointwise cancellation feasibility

Date: 2026-10-03.

The 2525 wide-rectangle representation priced the 640-cell node term at
about 89 and could not fit the existing endpoint budget. This record tests a
named replacement before any Lean generation:

```text
wide family rectangles -> midpoint family sum + coefficient error
                           -> norm after the 30-family sum
```

The weighted second derivative is treated with the same order of operations.
For a family with coefficient c, radius r, modulation m, and bump

```text
b(x) = exp(-30 / (1 - (x/r)^2))
```

inside its support, the diagnostic uses the exact interior identity

```text
b'(x)  = b(x) * (-60 u / (r (1-u^2)^2))
b''(x) = b(x) * (-60 (1+3u^2)/(r^2 (1-u^2)^3) + (b'(x)/b(x))^2)
```

and evaluates the complex family sum before taking its modulus. The
coefficient box is represented by its midpoint plus a Euclidean error radius;
that error is charged additively after the center sum.

Results:

```text
+--------+----------+----------------------+----------------------+----------------------+
| cells  | sigma    | node sum             | sampled remainder    | sampled total        |
+--------+----------+----------------------+----------------------+----------------------+
| 640    | -1/2     | 2.675979660886877    | 0.348130782506138    | 3.024110443393015    |
| 640    | +1/2     | 2.663843813683129    | 0.343649647406399    | 3.007493461089528    |
| 1280   | -1/2     | 2.688816070888075    | 0.081974600319111    | 2.770790671207186    |
| 1280   | +1/2     | 2.677064065852956    | 0.080916396067128    | 2.757980461920084    |
| 2560   | -1/2     | 2.686887376406491    | 0.019653549551288    | 2.706540925957779    |
| 2560   | +1/2    | 2.675211462945179    | 0.019387894566168    | 2.694599357511347    |
+--------+----------+----------------------+----------------------+----------------------+
```

Against `baseNormUpper2343 = 2.7790943782`, the 2560-cell sampled margins
are about `0.07255345` and `0.08449502`. The 1280-cell margin is only about
`0.00830371` on the negative endpoint, so 2560 is selected for the next
certificate attempt.

The curvature maximum was found on a 32-subnode binary64 grid. That is a
feasibility probe, not an integral certificate: a sampled maximum does not
bound the unsampled interior. No Lean numeric payload was imported, and this
record makes no producer-GO, SourceRH, or RH claim.

Decision: `REOPEN WITH NAMED REPRESENTATION CHANGE`. The old 640-cell
wide-box branch remains scoped-blocked. The new 2560-cell signed-cancellation
branch is viable diagnostically and becomes the active terminal subtask.

Evidence:

- `scripts/routea_owner_signed_cancellation_2528.py`
- `results/2528_signed_pointwise_cancellation_probe.json`
- `ConnesWeilRH/Dev/C1RouteAOwnerPanelNormBridge2467.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerPanelNodeUpper2471.lean`
- `ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean`
