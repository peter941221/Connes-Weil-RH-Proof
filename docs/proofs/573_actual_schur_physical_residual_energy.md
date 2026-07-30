# Proof 573: Actual Schur / Physical Residual Hilbert--Schmidt Energy

## Result

Let `R_S` be the actual physical-versus-Schur residual, `M` a bounded physical
right leg, and `A` a Hilbert--Schmidt source input.  If

```text
||R_S|| <= 2,
```

then, for any Hilbert basis of the source carrier,

```text
sum_i ||M R_S A e_i||^2
  <= 4 ||M||^2 sum_i ||A e_i||^2.
```

The actual finite-S specialization uses Proof 572's family-uniform residual
bound, so its constant is independent of the visible finite prime list.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurPhysicalResidualEnergy.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurPhysicalResidualEnergyAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The generic theorem is
`tsum_normSq_postcomp_residual_le`.  The actual residual theorem is
`sourceActualBandForwardTransportResidual_tsum_normSq_postcomp_le`.

## What This Closes

This adds an absolute Hilbert--Schmidt energy ledger for the actual physical
residual.  The proof applies bounded postcomposition to a summable source
energy and uses the operator-norm bound `||R_S|| <= 2` pointwise before taking
the nonnegative `tsum`.

## Boundary

This is not a Douglas factorization through the actual two-channel physical
analysis column.  In particular, it does not construct a family-uniform

```text
rawRow = readout * physicalAnalysis
```

with a bounded readout.  The residual is not proved zero, signed, or
trace-canceling.  Gate 3U, the finite-S sign, Burnol's identity, and RH remain
open.

The primary external boundary source is
[Connes--Consani--Moscovici, arXiv:2310.18423v2](https://arxiv.org/abs/2310.18423).
It supplies Sonin-space stability and Hilbert-space relations, but not this
missing signed Douglas producer.

## Verification

The source was built in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing
from the Windows source of truth:

```text
focused source module: lake build
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurPhysicalResidualEnergy
  3337 jobs, PASS

focused audit: lake build
  ConnesWeilRH.Dev.CCM24FiniteSActualSchurPhysicalResidualEnergyAudit
  3338 jobs, PASS
  both declarations: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3843 jobs, PASS
full repository: 3923 jobs, PASS
git diff --check: PASS
```

No `sorry`, `admit`, or user axiom is used by this batch.  The WSL localhost
proxy warning and pre-existing repository linter warnings are environmental or
unrelated to this module.
