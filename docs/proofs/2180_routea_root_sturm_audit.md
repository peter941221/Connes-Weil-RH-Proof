# 2180 — Route A exact-rational root completeness

Date: 2026-09-29.

## Consumer and premise

The consumer is the order-48 sign-partition enclosure used by the high-height
same-owner C3' tail.  The premise removed is that the 2066 list of 64 root
intervals is complete and has no hidden roots in the gaps.

The numerator polynomial `P48` is rebuilt over `Fraction` coefficients.  A
143-term exact rational Sturm chain is evaluated at every interval endpoint,
at `-1`, and at `1`.

## Result

```text
degree(P48)                   = 142
Sturm chain length             = 143
roots in (-1,1)               = 64
input intervals                = 64
each listed interval           = exactly 1 root
each of 65 exterior gaps       = 0 roots
```

The run completed under the WSL resource-aware wrapper with exit code 0.

Evidence:

- `scripts/routea_root_sturm_audit_2180.py`
- `results/2180_routea_root_sturm_audit.json`
- `results/20260929_routea_sturm_2180.log`

## Boundary

This closes root completeness only.  It does not prove the selected detector's
finite-window signed C3' inequality, transfer the one-copy numerical owner to
the complete closed-ball owner, or establish RH.

Classification: **STURM-ROOT-COMPLETENESS-PASS**.
