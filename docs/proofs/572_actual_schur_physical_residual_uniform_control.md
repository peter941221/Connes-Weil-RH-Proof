# Proof 572: Actual Schur / Physical Residual Uniform Control

## Result

The normalized physical inverse and the source-forward actual Schur product are
both contractions under the same Euler lower normalization:

```text
||normalizedFiniteEulerInverseList S|| <= 1
||suffixActualSchurForwardAmbientProduct lambda stepData S|| <= 1
```

Their actual variation-of-constants residual is therefore uniformly bounded by

```text
||suffixActualSchurForwardPhysicalTransportResidual lambda stepData S|| <= 2.
```

The source-carrier residual has the same bound.  Proof 565's endpoint alignment
residual and Proof 564's physical/Schur endpoint residual are not set to zero;
their signed sum is exactly the source transport residual and is also bounded
by `2`.

## Exact Row Owner

The module defines the signed four-term row
`rawPhysicalTransportResidualRow`.  For arbitrary coframe decompositions, the
existing raw coframe residual row is exactly this row:

```text
rawPhysicalCoframeResidualRow = rawPhysicalTransportResidualRow.
```

Specializing to the actual finite-S suffix gives the exact owner

```text
suffixActualBandNamedSchurCoframeResidualRow
  = rawPhysicalTransportResidualRow residual_S residual_(p::S).
```

For residual component norms at most `2`, the coarse operator-norm estimate is

```text
||rawPhysicalTransportResidualRow||
  <= 8 * ||cc20ThreeBranchCommutator||.
```

The specialized named row satisfies the same bound.  The constant is
independent of the visible prime list and the adjacent suffix index; the
commutator on the right is the existing owner-dependent operator.

## What This Closes

This closes the actual residual's uniform operator-norm ledger and gives the
residual a signed physical row owner.  The proof uses only contraction bounds,
the exact coframe additivity identities, Hilbert adjoint norm preservation, and
the ordinary four-term triangle inequality.

## Boundary

An operator-norm bound is not a Douglas estimate.  This batch does not construct

```text
residualRow = residualAmbientRow * ambientLossColumn
            + residualBoundaryRow * boundary†
```

with a family-uniform lower-bound/readout constant.  It therefore does not yet
prove Gate 3U, the finite-S sign, Burnol's identity, or RH.  The residual is
also not proved zero, nonpositive, or trace-canceling.

The primary source checked for the external boundary is
[Connes--Consani--Moscovici, arXiv:2310.18423v2](https://arxiv.org/abs/2310.18423).
It describes semilocal Sonin-space stability and Hilbert-space relations; the
missing semilocal signed residual/Douglas producer is not supplied by the
source result used here.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurPhysicalResidualUniformControl.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurPhysicalResidualUniformControlAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

## Verification

All commands ran in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing from
the Windows source of truth:

```text
focused module build: 3336 jobs, PASS
focused axiom audit: PASS; all ten declarations use exactly
  [propext, Classical.choice, Quot.sound]
CCM25Concrete aggregate: 3841 jobs, PASS
full repository: 3922 jobs, PASS
git diff --check: PASS
```

The WSL localhost-proxy warning and existing repository linter warnings are
environmental or pre-existing. No `sorry`, `admit`, or user axiom is used by
the new source or audit.
