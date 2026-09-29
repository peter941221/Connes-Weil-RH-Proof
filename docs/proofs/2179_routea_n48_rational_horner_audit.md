# 2179 — Route A exact-rational order-48 audit

Date: 2026-09-29.

## Consumer and premise

The consumer is the high-height tail in the same-owner signed C3' budget,
then `SourceRH`.  The named premise removed here is that the order-48 total
variation `N48` is supported only by an mpmath interval candidate.

The audit keeps the one-copy G8-H numerical owner and the 2066 rational root
intervals.  It reconstructs the exact numerator polynomials `P47` and `P48`
with `Fraction` coefficients and evaluates them with exact rational Horner
intervals.  No termwise absolute expansion is used.  The exponential factor
is bounded safely by `exp(-30/(1-u^2)) <= 1`, so this is intentionally much
coarser than the 2135 candidate.

## Result

The exact rational sign-free variation enclosure gives

```text
log10 N48_upper = 146.2702132174163
max local error log10 = 87.02642803037088
```

Repricing the 2178 algebraic tail with this coarse independent upper bound
scales the two-sided tail to

```text
log10(two-sided tail)        = -681.5220860929089
log10(two-sided / L2 charge) = -692.1667428154246
```

Thus the tail margin survives even after discarding the exponential decay and
replacing the mpmath value by an exact-rational coarse enclosure.

Evidence:

- `scripts/routea_n48_rational_horner_audit_2179.py`
- `results/2179_routea_n48_rational_horner_audit.json`
- `results/20260929_routea_n48_2179.log`

## Boundary

This is an independent tail-margin audit, not the final sharp `N48` proof.
Root completeness was audited separately in record 2180.  The one-copy owner,
finite-window signed margin, coefficient/Gram enclosure, and selected-detector
transfer remain open.

Classification: **RATIONAL-HORNER-TAIL-MARGIN-PASS**.
