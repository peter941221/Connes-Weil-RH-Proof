# Proof 517: quantitative completed-history readout

## Result

The completed Julia history now has a quantitative readout theorem. If a
readout has operator norm at most `C >= 0`, its output Hilbert--Schmidt energy
is bounded by `C^2` times the input energy:

```text
sum_i ||readout (history (input e_i))||^2
  <= C^2 * sum_i ||input e_i||^2.
```

The old contractive theorem is unchanged and is the specialization `C = 1`.
The new theorem is
`completedRectangularBoundaryReadout_tsum_normSq_le_of_norm_le`.

Proof 517 also records the unconditional terminal-survivor readout

```text
readout = sourceThreeBranchPairData.right * frameSourceInclusion,
```

with the honest bound

```text
||readout|| <= ||sourceThreeBranchPairData.right * frameSourceInclusion||.
```

This is not a norm-one result. The existing Hilbert--Schmidt basis-energy
bound does not imply an operator contraction, and the noncommuting survivor
cannot be moved across the fixed Gram input. The norm-one terminal theorem
therefore remains conditional on the exact pointwise Douglas domination.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedPhysicalHistory.lean
  CCM24FiniteSCompletedPhysicalTerminalReadout.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedPhysicalTerminalReadoutAudit.lean
```

## Remaining obligation

The raw boundary-dagger readout and the joint norm are still source-specific
producer obligations. Proof 517 does not prove Gate 3U, the finite-S sign,
Burnol's identity, or `_root_.RiemannHypothesis`.

## Verification

Ubuntu 24.04 WSL2, isolated ext4 mirror:

```text
owning module build: PASS
focused axiom audit: PASS
CCM25Concrete aggregate: PASS, 3791 jobs
full repository: PASS, 3872 jobs
axioms: [propext, Classical.choice, Quot.sound]
```
