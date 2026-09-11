# 1321 — G8 P1 projection-defect primitive-energy reduction

Date: 2026-09-11.

Status: FORMAL Lean brick. It reduces the two derived energies in the signed projection-defect Cauchy--Schwarz bound to literal same-owner cutoff energies. It proves no cutoff bound, vanishing statement, metric-to-radial transport, P2/P3 conclusion, or RH claim.

## Statement

For Hilbert--Schmidt input `A` and bounded postcomposition `B`, Lean proves
`sum_i ||B A e_i||^2 <= ||B||^2 sum_i ||A e_i||^2`.

For the unique signed G8 projection defect,

```text
E_left(n)  <= sum_i ||A_n e_i||^2,
E_right(n) <= ||G||^2 sum_i ||D_n e_i||^2,
```

where `D_n = A_n - J J† A_n`. Thus the remaining analytic input is a uniform raw cutoff-leg energy bound plus useful cutoff control of the complement energy. No claim that `D_n` tends to zero is made.

## Lean owners

`C1G8P1ProjectionDefectEnergyReduction.lean` and paired audit. Audited:

```text
tsum_normSq_postcomp_le
g8ProjectionDefectCrossLeftEnergy_le_sourceCutoffLegEnergy
g8ProjectionDefectCrossRightEnergy_le_gram_norm_sq_mul_complementEnergy
```

## Verification

Batch `1535_g8_p1_energy_reduction_retry6.log`: 3983 jobs, zero `error:` and `sorryAx`; each audit prints `[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
