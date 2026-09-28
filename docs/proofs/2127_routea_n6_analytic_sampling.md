# 2127 — Route-A n=6 analytic eighth-order sampling chain

Date: 2026-09-28.

Status: ANALYTIC-DERIVATIVE-SAMPLING-CANDIDATE. This is a numerical
sampling-bound candidate, not an interval certificate, producer theorem, or
RH proof.

## Scope

Record 2126 used finite differences to estimate the eighth derivative of the
three prime-channel integrands. Record 2127 replaces that estimate with an
analytic truncated-Taylor jet chain for the stored 300-node Gauss-Legendre
seed quadrature:

```text
seed derivatives
  -> cardinal products at s - z
  -> P polynomial
  -> modulus-square jets
  -> W = |base|^(2(N+1)) |correction|^2
  -> W, P W, P^2 W eighth derivatives
```

The interpolation product excludes the active node, and the seed is shifted
by the active node. These two controls are necessary; the first implementation
omitted both and produced a false zero derivative chain.

## Result

The registered owner is the 40-node known-zero under-approximation at
`rho = 0.55 + 30.424876125859513 i`, `N = 4`, with `n = 6`, support radius
16, and 595877 visible prime powers. At `dxi = 0.01` and `|xi| <= 75`:

```text
C       =  1.170419316890047e6
b       =  1.2160140244088554e10
D       =  8.280575869996369e13
det     = -5.095155122372849e19
```

The absolute eighth-derivative integrals and resulting sampling charges are:

```text
channel       integral |f^(8)|       sampling charge
C             7.712967565927477e20    2.2799700324876965e4
b             4.915787756521575e24    1.453117580897202e8
D             3.216362645994263e28    9.507638122160236e11
```

Propagating these one-sided moment charges through `det = C*D - b^2` gives
`6.577554167160422e18`, leaving a determinant margin of `7.746x`.

The jet value channel agrees with the original cardinal evaluator to maximum
relative error `9.937876670622347e-10` over the grid. Prime coverage remains
complete: all 595877 entries satisfy the FFT Nyquist bound.

## Interpretation

This retires the finite-difference-only objection for the sampling term and
shows that `dxi = 0.01` is numerically viable for the sampling component. It
does not close the Route-A certificate. The stored seed quadrature is not yet
interval-enclosed, DFT forward rounding is not charged, the finite-window tail
is not charged, and the owner is still a known-zero under-approximation.

At `dxi = 0.02`, the same analytic chain gives only `0.0116x` determinant
margin, so the step-size choice is part of the registered certificate budget,
not a cosmetic refinement.

## Reproducibility

```text
ROUTEA_DXI=0.01 python3 scripts/fourpoint_n6_routea_analytic_sampling_2127.py
```

Artifact: `results/2127_routea_n6_analytic_sampling.json`.