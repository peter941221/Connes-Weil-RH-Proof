# G8 P3 same-detector contradiction (2026-09-11)

The import-facing leaf `C1G8P3Contradiction` composes the supplied
same-owner G8 readback data with the existing healthy detector sign.  For the
identical selected owner it proves

```text
G8SameOwnerReadbackData ∧ HealthyYoshidaDetectorData
  ⟹  False,
```

because the readback consumer gives `0 ≤ qw(g)` while the detector's positive
spectral square gives `qw(g) < 0`.  The theorem is only the P3 logical
capstone; it constructs neither the readback data nor the missing P2
analytic inequality.

Acceptance: `/home/peter/rh/build-logs/1328_g8_p3_contradiction.log`,
3959 jobs, zero `error:`/`sorryAx`, standard audit axioms only.
