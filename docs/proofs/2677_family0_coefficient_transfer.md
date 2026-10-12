# Record 2677 family 0 cell bridge

Verdict: FAMILY 0 BASE-M0 CELL BRIDGE GREEN. The other 119 family/channel
memberships, the binary64 repaired-owner identity, and integral consumption
remain open.

`C1RouteACellContainment2677Family0.lean` instantiates the record-2676
mid-factor and complex-product lemmas for family 0 using the exact record-2338
base coefficient rectangle and the exact rational phi, cosine, and sine
intervals used by the record-2677 screen. Under membership of the coefficient
and the three continuous factors in those intervals, Lean proves that the
external family value belongs to the coefficient-aware complex product
rectangle. This establishes the algebraic propagation step for an arbitrary
position; no cell-position assumption is needed for that implication.

The new theorem `record2677Family0BaseM0CenterMem` specializes the coefficient
membership to the actual Lean owner `baseCoefficientCenter2540 0`. Its premise
is therefore reduced to the three factor memberships; the coefficient premise
is discharged by the existing exact theorem
`baseCoefficientCenter_mem2540`.

The same module now proves the three factor pins on the full cell. For the
bump, it applies the order-30 Taylor remainder at -1/2, raises the positive
lower/upper pins to the 60th power to enclose exp(-30), and uses an order-5
lower pin for the cell-end exponential addend. For sine and cosine, it uses
the order-26 complex exponential remainder at the cell endpoint and the
second-derivative chord error across the angle interval. These are exact-real
Lean inequalities; the JSON supplies rational endpoint literals only.

`record2677Family0BaseM0CellMem` composes the cell-wide factors for the exact
Lean center `baseCoefficientCenter2540 0`. The theorem
`record2677Family0BaseM0Subset` proves that this product rectangle is inside
the outward-rounded 160-bit dyadic box consumed by the aggregate bridge.
`record2677Family0BaseM0CellRectMem` therefore establishes an unconditional
cell-wide membership for family 0, base M0, at that exact Lean center.

The new `record2677BaseM0AggregateSubset` and
`record2677BaseM0CellContained` theorems connect this family-0 result to the
30-family finite-sum consumer. The latter discharges index 0 when the owner
coefficient and modulation equal the exact Lean center, while retaining the
other 29 family memberships as explicit hypotheses. Both declarations compile
in the Linux-native Mathlib v4.30 workspace and audit to exactly
`[propext, Classical.choice, Quot.sound]`.

This does not establish the binary64 repaired-owner identity used by the
numeric replay. Nor does it cover the remaining 29 families or the other
three channels. Consequently it does not yet discharge the full 2675 rectangle
premise, the 8192-cell `chargeRest` obligation, the signed infinite-xi tail,
or the Producer inputs.

Validation: the source passes under Linux Mathlib v4.30; the companion audit
prints exactly `[propext, Classical.choice, Quot.sound]` for the new theorems,
with no `sorryAx`. The generator
`scripts/generate_routea_family0_bridge_2677.py` reproduces the proof source
from `results/2677_cell4096_coefficient_enclosure_screen.json`.
