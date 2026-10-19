# Row-B D4/D7 arithmetic does not yet certify the Lean integrals (record 3067)

Date: 2026-10-19.

Status: source-level gate audit for the reopened row-B campaign. The stored
finite sums clear their numerical thresholds, but the chain has no proved link
from those rational rows to the actual Lean derivative integrals. This is a
scoped transfer gap, not a no-go for Route B or a producer result.

## What the current artifacts prove

For derivative order `k` (the number of derivatives), the target quantity is
`D_k = 4*integral_(0,1/2) |T^(k)(x)| dx`, where `T` is
`Real.smoothTransition`. An interval enclosure means a proved interval that
contains the actual derivative value at every point of a cell.

The current chain is:

```text
Real.smoothTransition derivatives
       |
       +--> Lean cell-membership theorem 2809
       |
       `--> separate Python interval replay 3040
                    |
                    +--> exact rational lists 3041
                    `--> exact aggregate thresholds 3042
```

The two lower branches have not been connected.

- `scripts/generate_seed_d4d7_cell_upper_3040.py` evaluates the 8192 cells
  through the imported `p3_certified_strip_constants_2720.py` mpmath interval
  evaluator. Each exported row is `4*cellWidth*derivativeIntervalRadius`
  plus an endpoint-majorant share. The artifact itself says evaluator-to-Lean
  soundness remains open.
- `scripts/generate_seed_d4d7_arithmetic_3041.py` copies the 3040 rational
  row strings into Lean lists and proves their lengths and sums with
  `norm_num`. This proves exact arithmetic about the stored rationals.
- `C1RouteBSeedD4D7Aggregate3042.lean` proves the aggregate constants are
  below 1500 and 2,000,000,000. The bounds are useful only after the row
  enclosures are connected to the actual derivatives.
- `C1RouteBSeedCellGeometry2809.lean` proves each actual fourth and seventh
  derivative lies in the corresponding `seedTransitionJetInterval2734` cell
  interval. It does not show those Lean interval endpoints are enclosed by
  the rational numbers exported in 3040.
- `C1RouteBSeedLedgerSoundnessContract3025.lean` and
  `C1RouteBSeedLedgerAllowanceContract3031.lean` correctly expose the missing
  pointwise comparison as a hypothesis. They do not prove it.

## Exact next theorem

For every `i < 8192` and `k` in `{4,7}`, prove that four times the cell width
times the absolute upper bound of the Lean interval jet is no larger than the
corresponding 3040 row minus its apportioned endpoint share, plus the allowed
rounding allowance. The factor four and the cell width turn a pointwise
derivative bound into an upper bound for that cell's contribution to `D_k`;
comparing the derivative magnitude directly to an integral charge would have
the wrong units. The 3040 generator already adds `endpoint[k]/8192` to every
row, so summing the rows includes the endpoint charge; it must not be added a
second time. The certificate must use the same cell endpoints, derivative
order, absolute-value convention, and endpoint allowance as the row data.

```text
Lean jet membership 2809
        |
        v
proved rational containment for each cell and order
        |
        v
4 * cellWidth * jetAbsUpper <= 3040 row - endpointShare + allowance
        |
        v
8192-cell sum + allowance sum < D4/D7 threshold
```

The first arrow is the blocking proof obligation. Re-running the Python
evaluator or proving another sum of its output would not close it. The
workable proof route is to preserve interval dependencies through the
2734/2736-2738 recurrences, certify the rational exponential bounds used by
the cell inputs, and instantiate the actual 2809 cells. A representative-cell
proof is a smoke test only; completion requires all 8192 cells or one uniform
theorem covering them.

## Scope

This gate advances only the row-B seed derivative pins. It does not establish
the poweredSeed carrier transfer, the rho-quantified detector duties, Route-A
selected-owner `qw >= 0`, `SourceRH`, or RH. Route A remains the binding
producer lane under the project rules.

Evidence: `results/3040_seed_d4d7_cell_upper.json`,
`scripts/generate_seed_d4d7_cell_upper_3040.py`,
`scripts/generate_seed_d4d7_arithmetic_3041.py`,
`ConnesWeilRH/Dev/C1RouteBSeedCellGeometry2809.lean`,
`ConnesWeilRH/Dev/C1RouteBSeedD4D7Arithmetic3041.lean`,
`ConnesWeilRH/Dev/C1RouteBSeedD4D7Aggregate3042.lean`, and
`ConnesWeilRH/Dev/C1RouteBSeedLedgerSoundnessContract3025.lean`.
