# 2337 - Certified marked sign and exact-target exclusion

Date: 2026-10-01

Status: CAPTURED-MARKED-SIGN-CERTIFIED-ONLY.

## Result

The actual captured source at n=0 has a strictly negative marked square:
Re(square(rho-1/2)) < -99/100, and the real four-point sum is < -19/10.
This is certified by Arb integrals, not inferred from sampled agreement.
Independent exact-rational postprocessing derives both signs directly from
the exported base and correction rectangles.

At the same time, all eight mandatory source target values are excluded by
their enclosures. In particular the raw moment at 1/2, which must vanish for
the centered zero moment, has real part approximately 1.2708730094e-9 and
imaginary part approximately 5.8737193146e-9. These are nonzero residuals,
not uncertainty radii. The fixed captured coefficients therefore cannot be
used as an exact finite-node realization. A tolerance-only interpolation test
would miss this failure.

## Exact object and endpoint proof

The input coefficients, widths, modulations, and node coordinates are lifted
from their exact binary64 ratios, not shortest decimal strings. The physical
radius is the exact square of each lifted width. No P-only multiplier is
inserted and no coefficient is re-solved. The transform is
H(z) = B(z) C(z) at n=0, as identified in 2335.

For one family of radius R, put x = R*u and delta = 1/64. The interior
integral is evaluated on -1+delta <= u <= 1-delta by acb.integral, using
256-bit arithmetic. The callback rejects any complex domain whose
1-u^2 denominator contains zero; no endpoint singularity is presented as
an analytic interior point.

On either omitted real edge slice, 0 < 1-u^2 <= delta*(2-delta), and the
modulation has modulus one. Consequently the combined edge charge is

```text
E_edge <= 2 delta R exp(-30/(delta*(2-delta)) + |Re(z)| R).
```

This bound is added to both components of the complex rectangle. Coefficients
are multiplied before accumulation with their own interval uncertainty. Tiny
edge bounds remain Arb values, never float-underflowed zeros. Exact rational
lower/upper endpoints are exported; display decimals are not proof pins.

## Readings and scope

The certified four-point real sum is approximately
-1.9999999997375341868354998214. All eight node integrations pass the
registered width gate. No source zero or completeness of the finite zero list
is proved. The positive-real residual at each of the three raw moment nodes
excludes zero. The captured root is not a healthy exact-moment witness.

The arithmetic certificate is external to Lean. Its integration guarantee
comes from python-flint 0.9.0, and the elementary edge bound is given above.
The rational checker rechecks postprocessing and provenance, not the
integration engine. No full spectral sum, physical-kernel sign, producer GO,
or RH claim follows from this marked prefix.

Validation: 10 Arb adversarial tests and 6 rational mutation tests pass. The
smoke integral overlaps its two-times-finer partition enclosure. Source and
capture hashes match. Negative tests cover poles, inflated error that must
refuse a sign, exact binary64 versus decimal lifting, changed node order,
forged hashes, zeroed factors, and unsupported producer claims.

## Evidence and primary documentation

- scripts/routea_marked_sign_arb_certificate_2337.py and paired Arb selftest.
- scripts/routea_marked_sign_rational_check_2337.py and paired rational selftest.
- results/2337_marked_sign_certificate.json and results/2337_rational_postprocess.json.
- build-logs/2337_marked_sign_certificate.log and build-logs/2337_marked_sign_selftest.log.
- Official python-flint 0.9.0 acb.integral documentation: analytic callback and
  certified integration options, retrieved 2026-10-01:
  https://python-flint.readthedocs.io/en/latest/acb.html

The next action is exact analytic interpolation repair, not relaxing the
zero-moment condition. Record 2338 prices such a finite-node repair separately.
