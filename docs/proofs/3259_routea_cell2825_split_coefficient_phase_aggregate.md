# Record 3259: Cell-2825 Split Coefficient-Phase Aggregate

## What is proved

For the selected Route A owner at cell `2825`, the 22 family-specific
coefficient-phase rectangles have a strictly negative aggregate real upper
endpoint:

```text
record2680Cell2825CoeffPhaseAggregateRectSplit3258.reHi < 0
```

Here `reHi` is the upper endpoint of the rectangle's real-coordinate interval.
The rectangle is an interval enclosure: it contains every value allowed by
the previously verified family phase boxes and the exact owner correction
coefficient. The theorem is therefore a formal sign bound for this enclosed
aggregate, not a floating-point sample.

## Proof decomposition

```text
22 corrected family phase boxes
          |
          v
22 independent coefficient-phase upper lemmas
          |
          v
Finset.sum_le_sum over Fin 22
          |
          v
explicit finite rational sum = -508128000000000000
          |
          v
aggregate reHi < 0
```

The independent modules are named
`C1RouteAConcreteOwnerPhaseCell2825Family8CoeffPhaseUpper3258.lean` through
the corresponding family-29 module. The aggregation module is
`C1RouteAConcreteOwnerPhaseCell2825CoeffPhaseAggregateSplit3258.lean`.

The important implementation boundary is that the aggregation layer imports
already compiled family lemmas. It does not unfold the Taylor evaluator,
repeated-squaring phase propagation, binary64 decoding, or interval products
again. This keeps the proof auditable and avoids the simplifier blow-up seen
when all 22 endpoint calculations were placed in one theorem.

## Verification evidence

The WSL2 build gate used:

```text
lean-toolchain: leanprover/lean4:v4.30.0
Lean: 4.30.0
target: ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseCell2825CoeffPhaseAggregateSplit3258
```

The audit file
`C1RouteAConcreteOwnerPhaseCell2825CoeffPhaseAggregateSplit3258Audit.lean`
prints:

```text
'ConnesWeilRH.Dev.record2680_cell2825_coeff_phase_aggregate_re_upper_split3258'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Boundary

This record proves only the coefficient-phase aggregate sign at cell `2825`.
It does not prove that the shared bump is positive, does not pay the signed
physical-kernel or C3' budget, and does not establish the full-line tail,
B5-shaped semi-local positivity, `producer_go`, `SourceRH`, or the Riemann
Hypothesis.
