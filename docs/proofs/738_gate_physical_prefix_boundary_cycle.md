# Proof 738: Gate Physical Prefix Boundary Cycle

## Result

Proof 738 cycles every ordered finite Gate prefix onto the existing common
physical boundary carrier.

Let

```text
P_N = projection onto span(e_0,...,e_(N-1)),
J   = sourceInclusion,
D_S = sourceActualBandForwardEndpointCoframe,
F_S = sourceActualBandForwardCoframe.
```

Lean first proves the exact finite-support identities

```text
P_N e_i = if i < N then e_i else 0,

Tr_source(A P_N)
  = sum_(i < N) <e_i,A e_i>
  = trace of the literal Fin N compression matrix.
```

It then inserts the same `P_N` into both Hilbert--Schmidt pair-data owners and
cycles them before recombination.  If `left` and `right` are the existing
common compact-root boundary factors, the finite boundary owner is

```text
BoundaryPrefix_(S,N)
  = right
      [D_S P_N J^dagger - J P_N F_S^dagger]
      left^dagger.
```

The main exact identities are

```text
GatePrefixCompressionTrace_(S,N)
  = Tr_boundary(BoundaryPrefix_(S,N)),

GatePrefixRootPairing_(S,N)
  = Tr_boundary(BoundaryPrefix_(S,N)).
```

The boundary owner is trace legal for every fixed `S` and `N`.  Consequently,
the remaining Proof 735 consumer can be stated directly as

```text
forall N,
  norm(Tr_boundary(BoundaryPrefix_(S,N))) <= C
```

for the complete signed prefix.

## Why This Matters

Proof 737 exposed compact root support inside a finite source-basis pairing.
Proof 738 moves that same finite scalar to the carrier where the repository's
actual boundary factors live:

```text
source Gate response
        |
        | right-compose by P_N
        v
finite ordered source trace
        |
        | two legal Hilbert--Schmidt cycles
        v
right [D_S P_N J^dagger - J P_N F_S^dagger] left^dagger
        |
        | only here seek one signed bound
        v
uniform Gate 3U producer
```

The projection is inserted between the family-dependent coframes and their
source adjoint legs.  It is not moved through those operators, so no false
commutation or finite-dimensional trace-cyclicity assumption is introduced.

## Guard

Keep

```text
D_S P_N J^dagger - J P_N F_S^dagger
```

inside one boundary sandwich.  Estimating the two terms separately recovers
the direct-sum Hilbert--Schmidt bound rejected by the Gate 3U guards.  Also do
not replace ordered prefixes by arbitrary finite subsets: that again permits
adversarial sign selection and approaches total variation.

Proof 738 proves no bound uniform in `S` or `N`.  Gate 3U, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror.  The Proof 738 source, import-facing audit, and `CCM25Concrete`
aggregate batch passed with `4007/4007` jobs; `CCM25Concrete` itself completed
at job `4006`.  The full repository passed with `4087/4087` jobs.

All eight audited Proof 738 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source has no `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, overlong
line, or new linter warning.
