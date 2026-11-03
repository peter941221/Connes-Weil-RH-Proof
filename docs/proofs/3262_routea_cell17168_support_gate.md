# Record 3262: Cell-17168 Support Gate

## Result

The formal candidate cell `17168` is physically active for every stored
family:

```text
for every family:
  |center(17168)| < storedWidth(family)^2
                  |
                  v
             bump > 0
```

The record also proves strict positivity for the family-8 bump, which is the
shared width used by the later owner-preserving cancellation records.

## Boundary

This is only a support gate. It does not prove a negative weighted-original
integrand value, the finite aggregate, the full-line tail, the C3' signed
budget, B5 readback, `producer_go`, `SourceRH`, or RH.
