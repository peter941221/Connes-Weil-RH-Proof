# 2221 — Full-owner black-box exponential bound no-go

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

This probe tests whether the missing exponential implementation certificate can
be avoided by using only the unconditional triangle inequality

```text
|exp(q) - v| <= |exp(q)| + |v| = exp(Re q) + |v|.
```

It uses the complete 2211 finite candidate rule: 30 nodes, 30 families,
`NSEG=1100`, and 12 Simpson panels.

```text
full-owner black-box price       2.659471411358396e+05
2211 combined-correction target  6.2550323e-05
ratio                            4.251730900507734e+09
```

Therefore a black-box triangle inequality is quantitatively unusable. This is
a scoped no-go for that fallback only; it does not reject the 2220
implementation-radius approach. The remaining admissible move is to certify
the implementation remainder (or replace the evaluator by a certified
interval/Taylor evaluator) and propagate it through every quadrature term and
finite sum.

Artifacts:

- `results/2221_exp_blackbox_no_go.json`
- `results/20260929_2221_exp_blackbox_no_go.log`
- script: `scripts/routea_weighted_zero_exp_blackbox_no_go_2221.py`

Status: `BLACKBOX-EXP-TRIANGLE-SCOPED-NO-GO`; no RH claim.
