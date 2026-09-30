# 2284: panelwise mpmath instrument audit

Date: 2026-09-30

Decision: the current bare `mp.quad` path is an instrument failure, not a mathematical tail result.

## Question

Can the suspicious 2284 global `mp.quad` result be validated by integrating each y-panel separately and comparing 35, 50, and 70 decimal precision?

## Result

At xi = 40 with eight panels, individual panel contributions are not small. The largest panel magnitude is about `4.87e-2` for base and `1.44e-1` for corr. However, the reported total changes across precision as follows:

```text
quantity       35 digits       50 digits       70 digits
base total     1.946e-38       2.684e-53       1.692e-54
corr total     1.135e-37       6.742e-52       6.252e-52
```

The precision movement is approximately `1.15e16` for base and `1.81e14` for corr. This means the apparent global cancellation is controlled by the quadrature residual, not by a stable mathematical value.

## Interpretation

This record rejects the current `mp.quad` evaluator as a truth oracle for the oscillatory owner transform. It does not reject the owner, the global cancellation mechanism, or Filon mathematics. Any reopening must use an independently certified evaluator, such as Arb/ball arithmetic with a validated oscillatory rule, or a proven panel remainder bound.

## Nonclaims

- Panelwise mpmath is not a directed interval certificate.
- The finite xi sample is not the infinite tail.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_panelwise_mpmath_audit_2284.py
python -m unittest discover -s scripts -p 'routea_panelwise_mpmath_selftest_2284.py' -v
```
