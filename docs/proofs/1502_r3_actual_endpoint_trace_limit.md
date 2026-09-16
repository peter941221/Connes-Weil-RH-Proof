# 1502 — the actual endpoint channel trace limit (R2 remainder ρ4)

**Status: FORMAL.** New leaf
[`C1G8R3ActualEndpointTraceLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualEndpointTraceLimit.lean)
(+ paired audit). The ρ4 remainder of the record-1500 readback identity is
now discharged *conditionally on one named square-sum*: the endpoint trace
`t_n` converges to a named limit `B` whenever the root-convolution column
energy of the source inclusion is finite. RH is not claimed; the gate is
NOT proved.

## What is proved

The readback consumer takes the source-basis trace of
`(g8SourceCutoffPairData … n).traceProduct`, which this file identifies
exactly (`g8EndpointSourceCutoffPairData_traceProduct_eq`) as the endpoint
channel operator

```text
A_n = J† ∘L Wₙ† ∘L G ∘L Wₙ ∘L J ,
Wₙ = fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n),
G = g8AdjointShearGram owner lambda family ,  J = sourceInclusion lambda .
```

The middle `G` is FIXED; only the expanding window moves. This is a
different slot structure from the cross channel of record 1479 (there the
cutoff sits outside a source-side middle; here it sits inside, between the
ambient Gram and the inclusion), so record 1476's fixed-leg transfer does
not apply. Instead the proof cycles the diagonal to the source basis:

```text
⟪e_i, A_n e_i⟫ = ⟪Wₙ(J e_i), G(Wₙ(J e_i))⟫  →  ⟪C(J e_i), G(C(J e_i))⟫
```

by the record-1478 strong limit, and dominates

```text
|⟪e_i, A_n e_i⟫| ≤ ‖G‖ · ‖Wₙ(J e_i)‖² ≤ ‖G‖ · ‖C(J e_i)‖² ,
```

using the committed window factorization `Wₙ = (norm-one output projection)
∘L C` (`fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution`,
record 1478). Since `C = rootConvolution owner` *by definition*
(`CCM24FiniteSBandTrace.lean:36-39`), the summable majorant is exactly the
gate

```text
(★)   Summable i, ‖C (J e_i)‖² .
```

`tendsto_ordinaryTraceAlong_of_dominated_diagonal` then exchanges limit and
sum and yields, unconditionally *given* (★):

```text
t_n → B := ordinaryTraceAlong sourceBasis (J† ∘L C† ∘L G ∘L C ∘L J).
```

## The gate is the survivor core

`g8EndpointGate_iff_survivorCore` proves the equivalence of (★) with the
in-Sonin core `Summable ‖(J† ∘L C ∘L J)(e_i)‖²`: by the exact Sonin split
(`g8BridgeSoninCarrier_normSq_split`, record 1498) the ambient column
energy is IN-core plus leakage band, and the leakage band is
unconditionally square-summable (record 1497). Consequently
`tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore` states ρ4 in
its final conditional form: **the in-Sonin survivor core alone discharges
the endpoint remainder.**

## Position in the program

Record 1500's ledger updates:

```text
ρ1  ≡ 0            FORMAL
ρ2  → 0            FORMAL (1479/1481)
ρ3  → 0            FORMAL (1480)
ρ4  → 0            FORMAL GIVEN (★)   ← this record
ρ5  = 0 required   OPEN  (the substantive gate)
```

One named square-sum now gates BOTH the survivor diagonal energy (records
1485/1486 via record 1498) and the endpoint channel limit (this record).
The attack program for (★) is preregistered in record 1503.
