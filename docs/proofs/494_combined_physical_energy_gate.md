# Proof 494: Combined physical energy gate

Date: 2026-07-22

## Result

Proof 494 closes the three auxiliary Hilbert--Schmidt columns around the
Proof 492 common physical pair and isolates the only remaining estimate in
the complete column

```text
M (V_S + C_S).
```

The exact objects are:

```text
J   = sourceInclusion
V_S = sourceActualBandForwardCoframe
C_S = finiteEulerMetricCoframe
M   = the complete three-branch physical right leg
```

The source module proves the following chain:

```text
readout : packed rectangular Schur histories -> common boundary carrier
norm(readout) <= 1
        |
        v
energy(M(V_S+C_S)) <= energy(sourceInput)
        |
        v
raw completed response trace norm <= 2 * fixedPhysicalEnergyMajorant.
```

The readout equation is an explicit premise.  It is not inferred from
biorthogonality, and the Julia co-defect contraction is applied only before
the carrier-correct bounded readout.

## Lean owner

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCombinedPhysicalEnergyGate.lean
```

Audit:

```text
ConnesWeilRH/Dev/CCM24FiniteSCombinedPhysicalEnergyGateAudit.lean
```

The five audited declarations are:

```text
rectangularBoundaryReadout_tsum_normSq_le
norm_sourceActualBandForwardCoframe_le_one
sourceActualBandCombinedPhysicalRightEnergy
sourceActualBandCombinedPhysicalRightEnergy_le_of_actualSchurReadout
lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_combinedEnergy
```

All five use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The source and audit contain no `sorry`, `admit`, or user axiom declaration.

## Verification

Commands were run in the Ubuntu 24.04 ext4 verification mirror with the
repository Lake build lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Dev.CCM24FiniteSCombinedPhysicalEnergyGateAudit
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CCM25Concrete
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
```

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 494 focused axiom audit        |  3296 | PASS   |
| CCM25Concrete aggregate              |  3768 | PASS   |
| full repository                       |  3849 | PASS   |
+--------------------------------------+-------+--------+
```

## Boundary

Proof 494 does not construct the bounded physical readout.  Therefore it does
not close Gate 3U.  The finite-S sign, negative-owner integration, Burnol's
identity, and unconditional RH remain open.

The unique next producer is a source-specific theorem identifying
`M(V_S+C_S)` with a bounded readout of the complete packed rectangular Schur
history.  Splitting the column into `MV_S` and `MC_S` would discard the raw
endpoint cancellation and recreate the family-dependent inverse lower-factor
loss.
