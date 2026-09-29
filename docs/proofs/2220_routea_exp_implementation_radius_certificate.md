# 2220 — Exponential implementation-radius certificate

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, with the actual
`sourceNontrivialZeroSet` owner and same-owner `qw >= 0` target.

Record 2219 showed that a rounding-cell-only proof cannot assume that NumPy's
complex `exp` is correctly rounded. Record 2220 replaces that assumption. For
the same binding node, three representative families (0, 15, 29) and the
central GL point were evaluated with exact `Fraction` brackets for `exp`,
`sin`, and `cos`. The distance from the returned binary64 value is charged as
an explicit implementation remainder.

```text
samples                         3 atoms, 6 real/imag components
largest radius / ULP-cell       0.7352658427507756
largest radius / returned value 1.6001640668480035e-16
binding component               family 0, imaginary
all radii                       finite
```

The family-0 imaginary component is exactly the component that failed the
2219 correct-rounding cell. It is now covered by a positive explicit radius;
therefore the 2219 assumption is removed rather than silently retained.

The corresponding absolute radius is `3.540176259097088e-35`; the largest
relative radius among the six components is `1.6001640668480035e-16`.

This is a quantitative interface brick, not the complete producer proof. The
input exponent construction, finite summation, all quadrature terms, complete
owner transfer, and signed `C3'` margin remain open. The next gate is to lift
this radius through the full term/sum chain and compare its charge with the
actual selected-detector margin.

Artifacts:

- `results/2220_exp_implementation_radius.json`
- `results/20260929_2220_exp_implementation_radius_pass3.log`
- script: `scripts/routea_weighted_zero_exp_implementation_radius_2220.py`

Status: `EXP-IMPLEMENTATION-RADIUS-CERTIFICATE`; no RH claim.
