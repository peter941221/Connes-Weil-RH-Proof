# 2296: Carrier-separated interpolation survives the finite-window diagnostic

Date: 2026-09-30.

Result: the captured owner's carrier-separated 192:6 interpolant passes both
signed and absolute sampled functional-difference diagnostics on all six
combinations of grid step and reference order. This is a finite-window
numerical candidate, not hgap, a quadrature certificate, or a producer result.

## Named change from 2295

A carrier is a known oscillating factor exp(i theta y). The old interpolant
fitted it together with the envelope. This one integrates it through the
analytic polynomial moments and fits only the envelope. The change concerns
the representation of the same captured function, not a new owner or new
coefficient solve.

Let y be the physical coordinate and xi the Fourier frequency. Each family
has stored width a, physical radius R=a^2, stored phase theta, and complex
coefficient c. Define phi_R(y)=exp(-30/(1-y^2/R^2)) inside |y|<R, zero outside.
Group indices having identical theta and define

`A_theta(y) = exp(y/2) sum_(j with phase theta) c_j phi_(R_j)(y)`.

The owner transform is exactly the sum over theta of

`integral A_theta(y) exp(-i (2 pi xi - theta) y) dy`.

There are 30 families and 25 phase groups. Both coefficient-vector hashes
remain identical to capture 2275. On each panel, interpolate A_theta at
Chebyshev-Lobatto nodes, then integrate the polynomial against the shifted
phase. Combine all complex carrier contributions before any modulus. The
finite-window functional retains its signed kernel and full complex polynomial
modulus. The support-derived visible kernel has 41136 prime powers.

```text
old: phi * exp(y/2) * exp(i theta y) -> polynomial fit -> Fourier moments

new: phi * exp(y/2)                  -> polynomial fit
     exp(i theta y)                 -> shifted Fourier moments
                          |
              sum complex carrier contributions
                          |
                signed functional difference
```

The pointwise regrouping control reconstructs the old stored owner at 257
physical coordinates. Maximum absolute deviation is 2.9489341e-11; the worst
ratio to a 256-epsilon absolute-term allowance is 0.7847814. This is a floating
transcription control, not a certified forward-error calculus. The calculation
reproduces the old 2295 24:4 signed discrepancy bitwise at steps 0.02 and 0.01
in the same run. The step-0.005 old-profile control is new, not a historical
anchor.

## Interpolation remainder target

For degree six, reference Lobatto nodes are
`-1,-sqrt(3)/2,-1/2,0,1/2,sqrt(3)/2,1`. Their monic product is

`omega(t)=t(t^2-1)(t^2-1/4)(t^2-3/4)`.

Let u=t^2. A primitive of omega is
`u^4/8-u^3/3+19u^2/64-3u/32`. Split its integral at u=0,1/4,3/4,1;
the exact rational integral of |omega| on [-1,1] is 1/32.
For panel half-length r and a seventh-derivative bound M, the standard complex
vector-valued divided-difference integral gives interpolation L1 remainder
`M r^8/(32*7!)`. The shifted oscillatory phase has modulus one.
This supplies a named analytic target for the 96-to-192 panel probe; it does
not price the functional automatically. Halving panel length gives a factor
128 in the aggregate constant-M transform bound. The observed functional
improvement must be measured separately.

## Same-functional readings

Full window [-40,40], same captured vectors, same signed 41136-term kernel.
Composite GL reference uses 24 physical panels, 256/512 nodes per panel.
Grid steps are 0.02,0.01,0.005, with exact central zero frequency.

The table below uses the finer grid and the 512-node reference. The diagnostic
budget is 1e7, applied here to the actual sampled functional difference rather
than a transform-only proxy.

```text
+-----------+---------------------+-----------------------+-------------------+
| profile   | signed difference   | absolute difference   | absolute / budget |
+-----------+---------------------+-----------------------+-------------------+
| 24:4      |  2.79138194e16      | 2.73590941e17         | 2.73590941e10     |
| 24:6      |  6.41633664e13      | 9.57140427e14         | 9.57140427e7      |
| 48:4      |  3.62427324e14      | 3.08452980e15         | 3.08452980e8      |
| 48:6      |  2.30370755e9       | 6.06928257e11         | 6.06928257e4      |
| 96:6      |  8.98852547e6       | 5.02489912e8          | 5.02489912e1      |
| 192:6     |  4.40608991e2       | 3.28105767e5          | 3.28105767e-2     |
+-----------+---------------------+-----------------------+-------------------+
```

The 96:6 profile passes only the signed diagnostic. Its absolute difference
still exceeds budget by about fifty times. The 192:6 profile passes both
throughout all six controls; its worst absolute difference is 3.33863911e5,
or 0.0333864 times budget. Maximum observed transform deviations are roughly
1.435e-10 for base and 2.933e-7 for correction.

The 256/512 reference movement reaches 5.38e-14 in base and 1.37e-11 in
correction. The small signed 192:6 difference ranges from negative to positive
across controls; it does not establish the sign of the true error. Its absolute
sampled difference, not that unstable sign, licenses the next enclosure probe.
The two GL reference orders share an evaluator class. Their agreement is not
independent analytic validation. None of the three grids supplies an integral
error theorem.

## Instrument controls

The moment evaluator uses the power series for |alpha|<=2 and the recurrence
outside it, where alpha=(2 pi xi-theta)r. Tests cover positive/negative phases,
zero shifted frequency, and both sides of that branch against smooth
high-precision polynomial moment integrals. Chebyshev-to-power conversion
trims zero polynomial coefficients; the matrix implementation pads those
coefficients to degree+1 slots. This fixes the first-run shape failure without
changing any mathematics.

Twelve tests cover the complete carrier grouping, pointwise owner identity,
exterior zero, length rejection, shifted-phase sign, exact same-carrier and
cross-carrier cancellation, zero channels/panels, analytic moments, exact
Lobatto product integral, old-profile controls, and summaries gating every
reference/grid reading.

Run:
`python3 scripts/routea_carrier_separated_functional_screen_2296.py`

Tests:
`python3 scripts/routea_carrier_separated_functional_selftest_2296.py`

Evidence:
`scripts/routea_carrier_separated_functional_screen_2296.py`,
`scripts/routea_carrier_separated_functional_selftest_2296.py`,
`results/2296_carrier_separated_functional_screen.json`.

## What remains

Next price the uniform seventh-derivative remainder for this representation,
including whether a triangle sum over carrier errors loses too much of the
observed cancellation. The rounded shape radii, nodes, polynomial coefficients,
phase and moment arithmetic need their own allowances. The numerical GL
reference has no certified quadrature remainder. A complete finite-window
functional certificate is still missing, as are infinite-tail control and
actual selected-owner readback. The interpolant is not an infinite-line tail
surrogate. No hgap supplier, producer GO, or RH claim follows.
