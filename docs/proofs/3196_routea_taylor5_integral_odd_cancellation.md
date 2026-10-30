# 3196 Route A Taylor-5 Integral Odd Cancellation

Status: symmetric-cell integral cancellation is verified in Lean.

The theorem `intervalIntegral_taylor5_upper_cancel_odd3196` accepts a full
cell pointwise upper bound containing Taylor terms of degrees zero through
five and a sixth-order remainder bound:

```text
value + first * u + second * u^2 / 2 + third * u^3 / 6
      + fourth * u^4 / 24 + fifth * u^5 / 120 + sixth * u^6 / 720
```

For a cell centered at `center`, the odd powers integrate to zero. The
remaining coefficients are exactly:

```text
h^3 / 24, h^5 / 1920, h^7 / 322560
```

This theorem is the integral-side companion to 3195. Together they establish
the analytic Taylor-6 bridge before numerical cell data are supplied.

Evidence:

- `build-logs/3196_wsl_build.log`
- `build-logs/3196_wsl_audit.log`

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.
