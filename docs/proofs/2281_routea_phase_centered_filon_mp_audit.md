# 2281: high-precision audit of the phase-centred Filon path

Date: 2026-09-30

Decision: the 2280 instability is primarily arithmetic at the current floating implementation; the mathematical Filon idea is not yet rejected.

## Question

Does the 2280 profile instability persist when the same stored owner, panel partition, interpolation degree, and oscillatory moments are recomputed with 100-digit arithmetic?

## Method

The audit keeps the 2275 stored coefficients and corrected width-a^2 owner. It recomputes selected transform values at xi = 40, 80, 120, 160, 200 using 100-digit mpmath arithmetic. The local Chebyshev interpolation is converted to a power polynomial at high precision, and the oscillatory moments are evaluated with high-precision recurrence. The result is compared with the binary64 implementation used by 2280.

## Result

The binary64 transform is not a reliable numerical reference in this regime:

```text
quantity                         maximum relative binary64 error
base transform                   1.9540717342
corr transform                   1.2310386006
```

The largest base error occurs at xi = 120 for the 12-panel, degree-12 profile. The largest correction error occurs at xi = 160 for the same profile. Several rows have relative error near one, meaning the floating result is comparable to the high-precision value in the wrong direction or phase.

## Interpretation

Record 2280 correctly rejected the floating profile as untrusted, but it should not be read as a no-go for every phase-centred Filon construction. The next implementation must change the arithmetic path first: stable Chebyshev-basis moment evaluation plus directed coefficient/error bounds. Only after that path agrees with the high-precision audit may a finite-window enclosure be attempted.

## Nonclaims

- Selected-point high precision is not an infinite-tail certificate.
- `mpmath` high precision is not a directed interval proof.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_phase_centered_filon_mp_audit_2281.py
python -m unittest discover -s scripts -p 'routea_phase_centered_filon_mp_audit_selftest_2281.py' -v
```
