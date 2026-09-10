# G8 P1 survivor--boundary coframe Pythagorean identity

Date: 2026-09-11.

The import-facing leaf `C1G8P1CoframePythagorean` proves two exact
same-owner identities. First, the survivor coframe is orthogonal to the
aggregate visible-boundary coframe:

```text
g8MetricSurvivorCoframe(λ,family)† ∘
  g8MetricVisibleBoundaryCoframe(λ,family) = 0.
```

Taking the adjoint gives the reverse cross term, and expanding the existing
metric coframe split yields the exact unweighted Gram decomposition

```text
finiteEulerMetricCoframe† ∘ finiteEulerMetricCoframe
  = survivor† ∘ survivor + boundary† ∘ boundary.
```

This is a FORMAL P1 energy/Gram consumer on the literal `CompactLog` owner.
It does not cancel detector-weighted channels, identify the boundary term with
a radial crossing, prove a finite metric trace equality, or advance P2/P3
signs.

Evidence: `1475_g8_p1_coframe_pythagorean.log`, owning and audit targets green,
3927 jobs, zero `error:`/`sorryAx`; both audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
