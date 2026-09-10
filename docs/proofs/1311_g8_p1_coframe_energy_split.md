# G8 P1 pointwise coframe energy split

Date: 2026-09-11.

The import-facing leaf `C1G8P1CoframeEnergySplit` specializes the survivor--
boundary orthogonality to every source vector and proves

```text
‖finiteEulerMetricCoframe(λ,family) x‖²
  = ‖survivor(λ,family) x‖² + ‖visibleBoundary(λ,family) x‖².
```

This is a FORMAL same-owner P1 energy identity obtained from the literal
metric coframe split and the exact orthogonality theorem. It supplies no
metric-to-radial transport, finite metric trace equality, P2 remainder/sign,
or P3 positivity producer.

Evidence: `1482_g8_p1_coframe_energy_split.log`, owning and audit targets
green (3928 jobs), zero `error:`/`sorryAx`; the audited declaration uses
exactly `[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
