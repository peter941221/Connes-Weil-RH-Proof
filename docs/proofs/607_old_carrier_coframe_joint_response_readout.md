# Proof 607: Old-Carrier Coframe Joint Response/Readout Equivalence

## Result

The old-carrier coframe now has an exact response-facing presentation of the
existing gap-facing source-factor contract.  The new contract is
`SuffixRawOldCarrierCoframeJointGapResponseReadoutData` in
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout.lean`.

For a visible prime `p` and suffix `S`, its factor is a bounded map

```text
K_(p,S) : sourceSoninCarrier(lambda) -> suffixEulerFrameAmbientBoundaryCarrier
```

and its response equation is

```text
oldFrame_(p,S) * L_(p,S) * transition_(p,S)
  = -rho_p * oldCarrierAnalysis_(p,S)^dagger * K_(p,S).
```

The map `K_(p,S)` is therefore the response-coordinate version of the
gap-facing readout.  Its adjoint is the actual old-carrier readout:

```text
K_(p,S)^dagger * oldCarrierAnalysis_(p,S)
  = gap_(p,S) * oldFrame_(p,S)^dagger.
```

The second identity is obtained by taking the adjoint of the response
factorization and cancelling the nonzero scalar `rho_p`.  The scalar is
nonzero because `primeSchurMarkovScalar_pos p` supplies its strict positivity.

## What Changed

The source module provides both directions:

```text
response factorization  --adjoint-->  gap readout
gap readout              --adjoint--> response factorization
```

The two one-suffix contracts are equivalent at the same bound, and the two
family-uniform contracts are also equivalent at the same bound.  No estimate
is lost in either conversion because the operator norm is preserved by the
continuous-linear-map adjoint.

The exact implementation uses the existing response identity from Proof 605
and the existing gap-readout shape.  It keeps the order
`oldFrame * response * transition`; it does not identify a transition with its
adjoint and does not discard the signed transition-skew channel.

## Bone 1 Boundary

This is a coordinate equivalence, not the missing Bone 1 producer.  The new
uniform response structure contains a family of bounded factors as a premise;
the module does not construct those factors or prove a bound independent of
`p` and `S`.  Consequently the active bottom remains:

```text
construct a genuine family-uniform old-carrier source factor
  -> obtain the Douglas/readout bound
  -> control the signed response in Gate 3U
  -> prove the finite-S sign and the remaining route identities
```

The range-annihilation guard from Proof 606 remains active.  In particular,
boundedness of the response does not imply annihilation of the complete signed
telescope, and no gap-zero covariance theorem is claimed here.  Gate 3U, the
finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadoutAudit.lean

ConnesWeilRH/Source/CCM25Concrete.lean
```

The audited declarations are:

```text
SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toJointGapReadoutData
SuffixRawOldCarrierCoframeJointGapReadoutData.toResponseReadoutData
exists_jointGapResponseReadout_iff_exists_jointGapReadout
SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformGapReadoutData
SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformResponseReadoutData
exists_uniform_jointGapResponseReadout_iff_exists_uniform_jointGapReadout
```

Every audited declaration reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Verification

The Windows source was synchronized file-by-file to the cached Ubuntu-24.04
WSL2 ext4 verification mirror.  The verification batch passed:

```text
focused source module: 3370 jobs, PASS
focused axiom audit:   PASS
CCM25Concrete aggregate: 3875 jobs, PASS
full repository:          3956 jobs, PASS
```

The build emitted only the repository's existing linter warnings plus long-line
warnings in this new source file.  No `sorry`, `admit`, or user axiom was
added.
