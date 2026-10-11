# Record 2673 - interval geometry bridge for the bump quotient

Verdict: MATHEMATICAL-INTERVAL-GEOMETRY-BRIDGE-PASS; evaluator certificate remains open.

The 2242 bump evaluator first needs an enclosure for
`q = 1 - (x / radius)^2`.  This record adds the exact-real interval bridge
in `ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`:

- `RealInterval2429.endpointAbsMax` bounds the absolute value of every point
  in an interval by the larger endpoint absolute value;
- `RealInterval2429.endpointAbsMinOrZero` records the correct lower absolute
  value, using zero when the interval crosses zero;
- `RealInterval2429.endpointAbsMinOrZero_le_abs` proves that lower bound;
- `RealInterval2429.mem_oneSubSqDiv` proves that positive radius intervals
  enclose `1 - (x / radius)^2` using monotonicity of reciprocal and square;
- `RealInterval2429.mem_bumpFromBoxes` composes that enclosure with the
  existing positive-`q` reciprocal and exponential bridge, so the box output
  encloses `exp(-30 / (1 - (x / radius)^2))` whenever its lower `q` endpoint
  is positive.

The audit also checks concrete crossing-zero, positive-only, and negative-only
`x` intervals, plus one full bump composition example.

The source compiles in the active Linux Mathlib v4.30 environment with exit
code 0. The audit declarations use only the project standard axiom trio
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced.

This closes one mathematical interval-composition sub-obligation. It does not
prove MPFR directed-rounding soundness, binary64 endpoint transfer, the full
2242 evaluator contract, the live-owner identity, `chargeRest`, the signed
infinite-xi tail, Producer GO, SourceRH, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`
- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebraAudit.lean`
- `results/2670_repaired_owner_continuous_box_price.json`
