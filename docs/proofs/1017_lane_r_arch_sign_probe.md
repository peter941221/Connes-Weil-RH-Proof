# 1017 — Lane R arch-sign numeric probe (prime-free subfamily CONFIRMED)

Date: 2026-08-18.
Probe: `docs/proofs/1017_lane_r_arch_sign_probe.py` (numpy 2.5.2, WSL2).

## Verdict (good news)

The prime-free subfamily of Lane R is numerically CONFIRMED with a solid
margin: for every sampled triple-vanishing prime-free compact-log test `g`
(unit `L2` norm), `archimedeanTerm (g.convolutionSquare) < 0` strictly,
hence `qw g = -arch(g^2) > 0`.  The quadratic form appears negative
DEFINITE on the constraint subspace, not merely semidefinite.

## Setup (exact Lean definitions mirrored)

```text
laplaceAt g s   = INT g(t) e^{s t} dt              (bilateral Laplace)
square          = g* * g  (Hermitian, F(0) = ||g||^2)
archimedeanTerm F = (log(4pi)+gamma) F(0)
                  + INT_{y>0} (e^{y/2}(F(y)+F(-y)) - 2F(0)) / (2 sinh y) dy
```

Sampled family: `g = sum_k c_k phi(t) e^{kt}`, `phi` a smooth bump on
`(log(1-w), log(1+w))`, coefficients in the null space of the three
vanishing moments `laplaceAt g s = 0` at `s = 0, 1/2, 1`.  The square
support lands inside `(-log 2, log 2)`, so `finitePrimeSum = 0` exactly,
and the `s = 1/2` vanishing kills the pole term (`|pole| <= 4.4e-16`
measured).  Null space sampled with 12 random unit directions per window.

## Results (unit-norm roots, random null-space directions)

```text
window               arch min      arch max     |pole| max   verdict
(-0.1625,+0.1398)    -1.238605     -1.233092    2.4e-16      arch < 0
(-0.2231,+0.1823)    -1.050321     -1.040102    2.3e-16      arch < 0
(-0.2877,+0.2231)    -0.906689     -0.889758    4.4e-16      arch < 0
(-0.3567,+0.2624)    -0.792516     -0.766241    3.5e-16      arch < 0
```

Margins are 0.77..1.24 with sample spread under 0.02: the sign is not
borderline.

Detector-oriented roots (extra `laplaceAt g rho = -1` at a FAKE off-line
point `rho`, i.e. not an actual xi zero) keep `arch < 0`
(`-22.3`, `-2.7`, `-22.1` with correctly positive `F0 = ||g||^2`).  This is
consistent with the Lean theory: the constructed sign flip
(`spectralWeilValue < 0` iff `arch > 0` by the closed Gate 2 chain) requires
detection at a REAL off-line xi zero — a RH-false-world object, unreachable
numerically while RH holds on the sampled regime.

Probe bug fixed en route: the autocorrelation grid must start at
`a - b` (reflection about 0), not `2a`; asymmetric windows
(`log(1+-w)`) shift by `a + b != 0`.  A negative `F0` is the tell
(`F(0) = ||g||^2 >= 0` always).

## What this buys the route

- The prime-free Lane R instance carries NO prime arithmetic (support kills
  every prime-power term).  It is a pure archimedean quadratic-form
  inequality: `arch(g* * g) <= 0` on the 3-codimensional vanishing subspace
  of `L2(log(3/4), log(5/4))`.  Numerics says negative definite.
- Two Lean attack shapes, both inside existing house templates:
  1. Concrete-root leaf (plateau template, `Dev/C1HealthyNarrowPlateau.lean`
     style): construct ONE root explicitly, prove `arch(root^2) <= 0` by
     the near/mid/tail quantitative split.  First true Lane-R-direction
     positivity leaf.
  2. General subspace statement via the Gamma_R diagonalization already
     built in `Dev/C1XiCenterTwoGamma.lean` (the arch profile / digamma
     kernel machinery) — reduce the quadratic form to the paired profile
     series and prove negativity on the moment-constraint subspace.
- Full Lane R (supports beyond `log 2`, prime terms present) remains
  RH-equivalent and open.  RH NOT claimed.
