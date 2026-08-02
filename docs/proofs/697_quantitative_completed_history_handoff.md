# Proof 697: Quantitative completed-history handoff

Date: 2026-07-31

Status: exact consumer extension. This proof does not close Gate 3U.

## Result

The completed physical-history consumer now accepts a readout with an
arbitrary explicit operator-norm bound named `bound`. The source theorem is:

```text
sourceActualBandCombinedPhysicalRightEnergy_le_of_completedActualSchurReadout_of_norm_le
```

It proves:

```text
combined physical right energy
  <= bound^2 * sum_i ||sourceInput (e_i)||^2
```

The Gate-facing handoff is:

```text
lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_completedHistory_of_norm_le
```

It keeps the existing fixed majorant unchanged when the producer supplies:

```text
bound^2 * input energy <= fixedPhysicalEnergyMajorant
```

The physical factorization remains an explicit premise. No metric coframe is
reinterpreted as the full physical endpoint.

## Why this matters

The old consumer required `||readout|| <= 1`, although a genuine physical
producer may naturally have a fixed constant larger than one. Proof 697
removes that interface restriction without weakening the signed owner or
introducing a branchwise estimate.

This is only a handoff. It does not construct the actual completed-history
readout, prove the required family-uniform bound, or establish the finite-S
sign, Burnol's identity, or `_root_.RiemannHypothesis`.

## Verification

The Windows repository was copied one way into an Ubuntu-24.04 WSL2 ext4
verification mirror. The following batch passed under the shared Lake lock:

```text
lake env lean ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedPhysicalHistory.lean
lake build ConnesWeilRH.Dev.CCM24FiniteSCompletedPhysicalHistoryAudit
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
```

The new declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, heartbeat increase, or recursion-limit
increase was added.
