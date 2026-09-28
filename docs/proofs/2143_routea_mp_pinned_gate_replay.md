# 2143 - High-precision pin correction and gate replay

Date: 2026-09-28.

Status: NUMERICAL STABILITY PASS; producer gate OPEN.

Trial 162 from record 2141 was reconstructed using the 320-point-per-panel
high-precision target matrix. The double-precision coefficients had maximum
high-precision pin residuals `2.43e-10` and `1.21e-10` for base and correction.
Minimum-norm high-matrix corrections of L2 size `0.433` and `0.191` reduced
both pin residuals below `1.5e-14`.

The correction does not destroy the finite gate. At 20001 xi nodes:

```text
             C           D             det
before   0.0885167074  -8.277039e16  -8.874235e15
 after   0.0885167074  -8.277039e16  -8.874235e15
```

The `Ap/B` spreads are unchanged to the displayed precision. This is strong
numerical evidence that the signed gate is not caused by the small target-pin
residual, but it remains a sampled floating-point result. The high matrix is
not interval enclosed and the 21 known zeros are not the complete owner.

Next hard gate: transfer this coefficient path to the complete formal owner
and certify the full-line integral and tail.

Evidence: `scripts/routea_mp_pinned_gate_replay_2143.py` and
`results/2143_routea_mp_pinned_gate.json`.
