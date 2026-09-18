# 1644 — S3 complement-corner normal form

Date: 2026-09-18.

The selected-root leakage leg now has the exact form

```text
U_b C [R_b (I - Q_0) R_b] U_{-b},
```

where `R_b` is the doubled-shift radial projection, `Q_0` is the unit
Fourier-support projection, `C` is the selected root convolution, and `U_b`
is the logarithmic translation by `b = log(lambda)`.

This is an algebraic rewrite of the existing translated-defect theorem.  It
does not assert Hilbert--Schmidt summability.  In particular, it records why
the existing shifted-Hardy interior-compression estimate cannot be substituted
without an additional block identity: that estimate controls the opposite
interior block, while S3 asks for the displayed radial complement corner.

No RH conclusion is claimed.
