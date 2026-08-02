# Proof 731: Gate Physical Boundary Centered Cycle

## Result

Proof 731 removes the fixed source-Sonin projection block from the legal
physical-boundary trace of Proof 730.

Let

```text
J   = sourceInclusion,
R   = J J^dagger = sourceSoninProjection,
D_S = sourceActualBandForwardEndpointCoframe,
F_S = sourceActualBandForwardCoframe,
U_S = sourceEndpointCancellationResidual = D_S - J.
```

Proof 730's middle operator has the exact centered decomposition

```text
C_S   = D_S J^dagger - J F_S^dagger
      = R + C_S^0,

C_S^0 = U_S J^dagger - J F_S^dagger.
```

Lean proves the two exact off-diagonal readbacks

```text
R C_S^0 = -J F_S^dagger,
C_S^0 R = U_S J^dagger,
```

and consequently both diagonal corners vanish:

```text
R C_S^0 R = 0,
(I-R) C_S^0 (I-R) = 0.
```

The genuine three-branch detector owner is

```text
K = cc20ThreeBranchCommutator = [R,W].
```

Because `RJ=J` and `J^dagger R=J^dagger`, Lean proves

```text
J^dagger K J = 0.
```

This zero is transported through the existing common Hilbert--Schmidt pair,
not through an unrestricted infinite-dimensional trace cycle:

```text
                  boundedPrecomp by J on both legs
K on ambient  -------------------------------------->  J^dagger K J = 0
     |                                                        |
     | legal Hilbert--Schmidt cycle                           | trace = 0
     v                                                        v
right R left^dagger on boundary --------------------------->  0
```

Therefore the fixed projection sandwich disappears exactly, and the Gate
trace is reduced to the centered physical boundary response:

```text
Tr_source(GateResponse_S)
  = Tr_boundary(right C_S^0 left^dagger).
```

Both the fixed projection sandwich and the centered response are proved trace
legal in the named common boundary basis. Every scalar trace-norm bound
transfers in both directions between the Gate response and this centered
boundary response.

## Why This Matters

The analytic Gate 3U owner now contains only the two genuine off-diagonal
channels:

```text
source Sonin  --U_S J^dagger-->  source complement
source Sonin  <--J F_S^dagger--  source complement
```

The family-independent `R` block is no longer carried into a uniform estimate.
This is an exact cancellation, not a norm bound and not a branchwise triangle
inequality.

## Guard

Proof 731 does not bound the remaining centered trace uniformly in `S`. The
endpoint residual corner and reverse-forward corner must remain inside one
signed boundary trace until compact root support is used. Gate 3U, the
finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and built under the shared Lake lock.

```text
focused source/audit       3354/3354  PASS
CCM25Concrete aggregate    4000/4000  PASS
full repository            4080/4080  PASS
```

Every audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new linter warning was added.
