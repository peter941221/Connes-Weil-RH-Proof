# 1322 — G8 P1 complement-energy cutoff comparison

Date: 2026-09-11.

Status: FORMAL Lean brick. It compares the literal source-complement cutoff
leg with the raw cutoff leg on the same healthy owner. It proves neither a
cutoff bound nor a vanishing statement, and makes no metric-to-radial,
endpoint, P2/P3, or RH claim.

## Statement

Let `A_n` be the literal left cutoff leg and let `J` be the source Sonin
inclusion.  With

```text
D_n = A_n - J J† A_n,
E_A(n) = sum_i ||A_n e_i||^2,
E_D(n) = sum_i ||D_n e_i||^2,
```

Lean proves

```text
E_D(n) <= 4 E_A(n).
```

It uses `||J|| <= 1`, hence `||J J†|| <= 1` and
`||1 - J J†|| <= 2`, followed by the existing postcomposition
Hilbert--Schmidt energy estimate.  The factor four is intentionally a safe
finite-cutoff estimate; no Pythagorean or asymptotic conclusion is encoded.

Together with record 1321, both factors in the record-1320 Cauchy--Schwarz
bound are now controlled by the raw cutoff-leg energy up to fixed finite-owner
constants.  This is only a boundedness reduction: it has no mechanism that
makes the signed cross trace small or zero.

## Lean owners

`C1G8P1ProjectionDefectEnergyReduction.lean` and paired audit. New audited
declaration:

```text
g8SourceCutoffComplementEnergy_le_four_mul_sourceCutoffLegEnergy
```

## Verification

Batch `1536_g8_p1_complement_energy_batch_retry2.log`: 3983 jobs, zero
`error:` and `sorryAx`; the complete audit prints only
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
