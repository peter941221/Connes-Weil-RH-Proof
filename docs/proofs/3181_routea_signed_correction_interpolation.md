3181 Route-A Signed Correction Interpolation
=============================================

Status
------

SIGNED_CORRECTION_INTERPOLATION_DIAGNOSTIC

This diagnostic compares the two existing coefficient-box sources in record
2338: the base coefficient and the correction coefficient. It interpolates
their box midpoints and radii using alpha from 0 to 1. Alpha 0 and alpha 1
correspond to existing endpoints; intermediate alpha values are not claimed
to be proved owners.

The scan preserves the current bump functions, frequency support, signed real
part, and owner geometry. It uses composite trapezoid integration at both
sigma signs and adds the coefficient uncertainty charge. No curvature or
quadrature enclosure is supplied.

Reproduction
------------

```text
python scripts/routea_signed_correction_interpolation_3181.py
```

Machine-readable output:

```text
results/3181_signed_correction_interpolation.json
```

Interpretation
--------------

A negative midpoint would identify a candidate endpoint or interpolation
parameter for separate proof work. A nonnegative scan only says that this
coefficient path did not produce a candidate; it is not a global no-go.

Observed result
---------------

The corrected endpoint alpha 1 is a candidate at sigma -0.5:

    signed midpoint integral ~= -1.4151672441702890888e-8
    uncertainty charge       ~=  8.0477090647930695e-42
    signed upper diagnostic  ~= -1.4151672441702890888e-8

At sigma +0.5, the midpoint remains positive but is very close to zero.
The negative sigma -0.5 value is stable when the composite-trapezoid grid is
refined from 640 to 2560 cells. This makes alpha 1, sigma -0.5 the next
admissible numerical target for a rigorous signed finite-window enclosure.
The current result still has no curvature enclosure, no full-line tail
certificate, and no Lean producer import.
