# 1323 — G8 P1 signed cross term: one primitive-energy bound

Date: 2026-09-11.

Status: FORMAL Lean brick. It combines the existing same-owner
Cauchy--Schwarz bound with records 1321 and 1322. It proves no sign, cutoff
limit, metric-to-radial transport, endpoint, P2/P3, or RH statement.

## Statement

For the unique signed projected--complement ordinary trace `X_n`, with raw
cutoff-leg energy `E_A(n)` and fixed Gram operator `G`, Lean proves

```text
|Re X_n| <= sqrt(E_A(n)) * sqrt(4 ||G||^2 E_A(n)).
```

This eliminates the two derived Hilbert--Schmidt energies and the complement
energy from the public analytic interface. The square-root form is retained
deliberately: it records exactly what finite-cutoff Cauchy--Schwarz supplies.
In particular, this bound contains no factor tending to zero and cannot by
itself settle the sign of the projection-defect ledger.

## Lean owner

`C1G8P1ProjectionDefectEnergyReduction.lean`, paired audit declaration:

```text
abs_re_ordinaryTraceAlong_g8ProjectionDefectCross_le_primitiveEnergy
```

## Verification

Batch `1537_g8_p1_primitive_cross_batch_retry1.log`: 3983 jobs, zero
`error:` and `sorryAx`; the audit prints only
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
