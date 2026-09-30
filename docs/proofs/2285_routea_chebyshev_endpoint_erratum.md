# 2285: Chebyshev endpoint-coefficient erratum

Date: 2026-09-30

## Error

The discrete Chebyshev coefficient conversion used in records 2281 and 2282 halved the constant endpoint coefficient `c_0` but failed to halve the degree endpoint coefficient `c_n`. This is a factor-of-two bug. A unit test with samples of `T_2` at `[-1, 0, 1]` returned `[0, 0, 2]` instead of `[0, 0, 1]`.

## Correction

The coefficient rule is now:

```text
c_k = total / n       when k = 0 or k = n
c_k = 2 * total / n   otherwise
```

After correction, 2281's binary64-vs-100-digit audit reads maximum relative errors `1.8425785913e-8` for base and `2.0121396395e-7` for corr. The previous order-one arithmetic-failure claim is withdrawn.

The corrected 2282 Chebyshev profile remains untrusted for a different reason: pointwise profile changes remain `17.5547x / 39.4779x` and `1.8828x / 484.0690x` across the tested refinements. Therefore the current approximation/residual route remains open only behind a real residual theorem; the old arithmetic diagnosis is not valid.

## Scope

This erratum supersedes the affected numeric interpretation, not the entire tail route. No hgap supplier, directed interval certificate, producer GO, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_phase_centered_filon_mp_audit_2281.py
python scripts/routea_chebyshev_basis_filon_screen_2282.py
python -m unittest discover -s scripts -p 'routea_chebyshev_endpoint_erratum_selftest_2285.py' -v
```
