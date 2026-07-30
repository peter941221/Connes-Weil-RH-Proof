# Proof 600: old-carrier coframe commutator guard

## Result

The orientation ledger now records the exact source-compression identity

```text
J^dagger [P_0, D] J = 0,
```

where `J` is the source inclusion, `P_0` is the fixed source Sonin
projection, and `[P_0,D]` is the `cc20Commutator` of that projection with the
selected detector.  The Lean owner is
`suffixActualBandRawCoframeBoundaryDetectorLeg_commutator_sourceCompression_eq_zero`.

This is only a commutator cancellation.  The actual raw detector leg in the
old-carrier telescope is

```text
D J,
```

so its source compression is `J^dagger D J`, not the commutator compression
above.  The projection identities `J^dagger P_0 = J^dagger` and `P_0 J = J`
cannot turn `J^dagger D J` into zero.  In particular, taking `D = I` is an
immediate abstract counterexample to that substitution.

The actual signed telescope remains

```text
signed telescope
  = orientation row
    + survivor/boundary residual row
    + metric inclusion row
    + forward-complete row.
```

Therefore the conditional divide-and-conquer owner still requires all three
readout contracts through the same old-carrier analysis.  Bone 1, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.

## Next source target

Keep the real `D J` channel explicit.  The next producer must either rewrite
the hard row into a legitimate commutator plus a separately controlled source
compression, or construct one joint bounded readout for the complete signed
telescope.  A separate operator-norm or Hilbert--Schmidt estimate is not a
replacement for that old-carrier factorization.

## Verification

The Ubuntu-24.04 WSL2 ext4 verification batch passed:

```text
owning source build: 3357 jobs
import-facing orientation audit: 3347 jobs
CCM25Concrete aggregate: 3865 jobs
```

The new audited declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, or user axiom
was added.
