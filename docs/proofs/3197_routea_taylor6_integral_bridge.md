# 3197 Route A Taylor-6 Integral Bridge

Status: the global Taylor-to-symmetric-cell integral bridge is verified in
Lean.

The theorem `intervalIntegral_taylor6_upper_from_global3197` combines the
preceding records:

```text
global ContDiff 6 + global sixth-derivative bound
        |
        v
full-cell Taylor-5 upper with sixth remainder / 720
        |
        v
odd powers integrate to zero on the centered cell
        |
        v
h^3/24, h^5/1920, h^7/322560
```

The remaining coefficients are represented by the fixed-cell second and
fourth `iteratedDerivWithin` values at the owner center. This is the exact
analytic shape needed by the Route A cell panel. It still requires actual
owner-specific numerical or interval inputs and does not establish a producer
certificate.

Evidence:

- `build-logs/3197_wsl_build.log`
- `build-logs/3197_wsl_audit.log`

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.
