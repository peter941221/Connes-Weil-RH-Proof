# Record 2669 - repaired-owner point-box control

**Verdict: SAMPLED-CONTROL-PASS; continuum enclosure remains open.**

This control checks whether the 2242 interval evaluator's returned box contains
high-precision evaluations of the repaired-owner formulas at selected points.
An interval box is a rectangle containing all possible real and imaginary
values; the point checks test that contract at samples, not at every real
input. Directed rounding (rounding each operation outward) is required when a
computed number is used as a proof upper bound.

## Readback

```text
+-----------------------------------------------+------------------+
| quantity                                      | value            |
+-----------------------------------------------+------------------+
| uniform grid points                           | 5001             |
| distinct points incl. support boundaries      | 5047             |
| point/channel comparisons                      | 20188            |
| high-precision reference                       | 90 decimal digits|
| containment failures                           | 0                |
| nearest hypot below a box-corner norm          | 10023            |
| max box-corner norm shortfall                  | 6.31e-12         |
| nearest weighted input below box-corner target | 9945             |
| nearest weighted input below sampled value    | 0                |
| family radii rounded below exact width^2       | 24               |
| rounded global support covers exact max         | yes              |
+-----------------------------------------------+------------------+
```

The sampled formulas use the 2338 exact-interpolation coefficient-ball
midpoints cast to binary64. Their MD5 values match the repaired treatment in
2665 and differ from the captured owner. No sampled reference value fell
outside the evaluator hull.

The `hypot` result is rounded to nearest, so it can sit below the norm of the
rectangle's far corner. That did not create a sampled point-containment failure
here, but it is not a valid general upper-bound operation. Record 2670 prices
the rectangle norm using MPFR square, addition, and square root with upward
rounding instead.

There is a separate radius issue: 24 individual binary64 `width * width`
values are below the exact square of their stored binary64 width. The maximum
rounded radius still covers the exact maximum support radius, but that global
fact does not cover each family on its own edge sliver. The sampled run therefore
does not close the exact `storedWidth^2` owner transfer.

## Nonclaims

The finite sample does not establish containment for every point of an
interval. It does not prove the evaluator's Lean soundness, identify the
repaired coefficients with the live producer owner, close the signed
infinite-xi tail, establish `chargeRest`, or imply producer GO, `SourceRH`, or
RH.

## Evidence

- `scripts/routea_repaired_owner_pointbox_control_2669.py`
- `results/2669_repaired_owner_pointbox_control.json`
- `scripts/routea_weighted_zero_zero_count_certificate_2242.py`
- `results/2338_exact_interpolation_repair.json`
- `results/2665_l1_margin_repair.json`
