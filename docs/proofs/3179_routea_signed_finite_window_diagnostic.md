3179 Route-A Signed Finite-Window Diagnostic
============================================

Status
------

SIGNED_FINITE_WINDOW_DIAGNOSTIC

This is a diagnostic replay for the current same-owner coefficient geometry.
It is not a certified quadrature result, a Lean certificate, a producer-go
result, a SourceRH result, or an RH proof.

Question tested
---------------

The earlier modulus-majorant diagnostic could hide signed cancellation. This
run keeps the real part of the complex midpoint contribution signed and adds
only the coefficient uncertainty charge. In plain language, it asks whether
the current owner becomes negative when cancellation is preserved before
rigorous numerical error is added.

The pointwise diagnostic is:

```text
signed contribution = exp(sigma * x) * Re(center(x))
uncertainty charge  = exp(sigma * x) * coefficient_error(x)
upper diagnostic    = signed integral + uncertainty charge
```

The finite window uses the existing owner/family inputs from records 2338 and
2528, with 2560 composite-trapezoid cells and 100 decimal-digit arithmetic.
The code does not provide a curvature enclosure, so the trapezoid result is
not an interval proof.

Observed result
---------------

```text
sigma = -0.5
signed midpoint integral ~= 1.0000000013672649325349954508763240384
uncertainty charge       ~= 4.2213581396113383e-45
signed upper diagnostic  ~= 1.0000000013672649325349954508763240384

sigma = +0.5
signed midpoint integral ~= 1.0000000000000000000000000000000000000
uncertainty charge       ~= 4.2213581396113383e-45
signed upper diagnostic  ~= 1.0000000000000000000000000000000000000
```

Both signed midpoint values and both diagnostic upper values are positive.
Thus, for this captured owner and finite window, closing numerical error alone
cannot turn the current midpoint into the required negative aggregate.

Boundary of the conclusion
---------------------------

This is a current-owner quantitative obstruction, not a global Route-A no-go.
It does not rule out a repaired owner, a different correction, or a different
closed geometry. It does show that the next useful work is owner/correction
design or a parameterized scan with a stated margin stop condition, rather
than merely tightening the same quadrature error estimate.

Reproduction
------------

```text
python scripts/routea_signed_finite_window_diagnostic_3179.py
```

Machine-readable output:

```text
results/3179_signed_finite_window_diagnostic.json
```
