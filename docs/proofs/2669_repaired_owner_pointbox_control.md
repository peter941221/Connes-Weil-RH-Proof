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
| nearest family products below exact width^2     | 24               |
| evaluator radii equal exact width^2             | 30 / 30           |
| MPFR radius precision                           | 256 bits          |
| outward global support covers exact max         | yes              |
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
values are below the exact square of their stored binary64 width. This control
now loads each width exactly into 256-bit MPFR and squares it there. A binary64
significand has at most 53 bits, so its square has at most 106 bits and is exact
at this precision. The endpoint of the global partition is separately rounded
outward. The sampled evaluator and reference therefore use the same exact
`storedWidth^2` parameter, including each family edge.

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
