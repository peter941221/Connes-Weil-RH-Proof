# Proof-717 / Gate-3U: 884 - outer channel is Sonin-scale-ROBUST (negative extends 824)

Date: 2026-08-08
Status: case-bound negative for the outer channel over the WHOLE physical scale line.

## 1. Question

824 established the outer leak `||(I-R) o D||` on the transported-Sonin frame
PLATEAUS ~0.62 (floor >=0.369) at logla=0 and does not vanish with resolution.
It was measured at ONE Sonin scale.  Does the physical scale `lambda` (Lean
`lambda : CCM24SoninScale`, band edge at t=logla) move the leak -- i.e. is the
negative a property of the model or an accident of one scale?

## 2. Result - the outer leak is FLAT across the physical scale line

Regression anchor matches 824 (n=600, L=8: 0.6242 vs 824's 0.6245).

```
 logla  outer(max over 6 transported-Slepian cols)
 -2.00   0.6090
 -1.50   0.6118
 -0.60   0.6161
  0.00   0.6192  (regression anchor region)
 +0.60   0.6190
 +1.20   0.6194
 +2.00   0.6199
```

The leak is pinned ~0.61-0.62 across logla in [-2, +2], drifting only ~+1%
upward with scale, never approaching 0.

## 3. Reading (honest, scope per 8c)

- Only the OUTER channel is trusted (it avoids the numerically-unreachable
  Sonin intersection R0).  The result is a case-bound NEGATIVE: over the whole
  sampled physical scale line the outer part of the metric coframe leakage stays
  bounded below by ~ 0.61 on the transported-Sonin frame, so no lambda makes
  `||leakage|| <= 1` (which needs degenerate leakage = 0) via this channel.
- It is NOT a proof (finite-grid, model-specific), and NOT a RH refutation: the
  inner/source-band channel and the off-Sonin forward cancellation remain the
  open analytic question (docs/872: `D_S = F + D == J`).
- It STRENGTHENS 824: the negative survives the definition of the model as the
  physical scale varies.  If a future closure is found it must be in the exact
  cancellation `F == -D + J`, not in a scale choice.

PROBE: docs/proofs/884_outer_sonin_scale_sweep_probe.py
