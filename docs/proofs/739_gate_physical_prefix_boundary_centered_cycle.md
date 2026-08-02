# Proof 739: Gate Physical Prefix Boundary Centered Cycle

## Result

Proof 739 removes the family-independent source block from every finite
boundary prefix constructed by Proof 738.

Write

```text
P_N = source Hilbert-basis prefix projection,
J   = sourceInclusion,
U_S = sourceEndpointCancellationResidual,
F_S = sourceActualBandForwardCoframe.
```

Since the endpoint coframe is `D_S = J + U_S`, Proof 738's middle operator has
the exact decomposition

```text
D_S P_N J^dagger - J P_N F_S^dagger
  = J P_N J^dagger
    + [U_S P_N J^dagger - J P_N F_S^dagger].
```

Lean names the bracketed term the centered prefix coframe.  Both of its
diagonal corners vanish:

```text
R C_(S,N)^0 R = 0,
(I-R) C_(S,N)^0 (I-R) = 0,

R = J J^dagger.
```

The cutoff remains on the source carrier throughout these identities.

## Fixed-Block Cancellation

Let `K` be the genuine three-branch detector commutator and let `left/right`
be its common-boundary Hilbert--Schmidt factors.  Proof 731 already proves

```text
J^dagger K J = 0.
```

Proof 739 strengthens the legal rectangular cycle to include any bounded
source cutoff `P`:

```text
Tr_boundary(right J P J^dagger left^dagger)
  = Tr_source(J^dagger K J P)
  = 0.
```

No cyclicity of an unrestricted operator product is used.  The cutoff is
inserted by `BasisHilbertSchmidtPairData.boundedPrecomp`, so both sides have
explicit trace-legality witnesses.

Consequently,

```text
GatePrefixCompressionTrace_(S,N)
  = GatePrefixRootPairing_(S,N)
  = Tr_boundary(
      right [U_S P_N J^dagger - J P_N F_S^dagger] left^dagger).
```

The Proof 735 consumer now needs only a common bound on these centered finite
boundary traces.

## Structure

```text
Proof 738 boundary prefix
        |
        | D_S = J + U_S
        v
fixed J P_N J^dagger  +  centered off-diagonal pair
        |                            |
        | legal cutoff cycle         | retained whole
        v                            v
Tr(J^dagger K J P_N)=0       active Gate 3U prefix owner
```

## Guard

The surviving operator is exactly

```text
U_S P_N J^dagger - J P_N F_S^dagger.
```

Do not estimate its two corners separately, and do not move `P_N` through
`U_S`, `F_S`, or `J`.  The fixed block vanishes because the compressed
commutator `J^dagger K J` is zero, not because `P_N` commutes with the physical
operators.

Proof 739 proves no bound uniform in `S` or `N`.  Gate 3U, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror.  The Proof 739 source, import-facing audit, and `CCM25Concrete`
aggregate batch passed with `4008/4008` jobs.  The full repository passed with
`4088/4088` jobs.

All twelve audited Proof 739 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source has no `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, overlong
line, or new linter warning.
