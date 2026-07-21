# Proof 474: Detector completed kernel operator

## Result

Proof 473 left the physical scalar as two signed-kernel response terms plus
one coupled second-support/prolate pairing.  Proof 474 assembles all of them
as one operator on the original finite-S carrier.

With `T` the translation by `log(lambda)`, `L=E Q`, and
`J=P^dagger N-N^dagger P`, define

```text
O_outer = L T^dagger J T + T^dagger J T L^dagger,

O_complete
  = O_outer + remainder.traceProduct.
```

Lean proves

```text
physicalPairing(x,y)=<x,O_complete y>.
```

More importantly, this is a same-object identification:

```text
O_complete=sourceThreeBranchPairData.traceProduct.
```

Therefore `O_complete` inherits `IsTraceClassAlong` from the genuine complete
three-branch Hilbert--Schmidt pair.  The displacement atom trace is now one
global-basis `tsum` of matrix coefficients of this single completed operator.

## Verification

The Windows source was copied one way into the Ubuntu 24.04 ext4 verification
mirror. The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 474 source plus focused audit                  |  3270 | PASS   |
| CCM25Concrete aggregate                              |  3749 | PASS   |
| full repository                                      |  3830 | PASS   |
+------------------------------------------------------+-------+--------+
```

The six audited theorems depend exactly on

```text
[propext, Classical.choice, Quot.sound]
```

The Proof 474 source and audit contain no `sorry`, `admit`, or new `axiom`.
The build emitted only existing repository linter warnings and the local WSL
proxy notice; the new Proof 474 module emitted no linter warning.

## Boundary

No summand of `O_complete` may be estimated separately.  The next analytic
producer must apply compact root support to the complete matrix coefficient,
retaining the outer signed-kernel and second-support/prolate cancellation.

The uniform Gate 3U bound, renewal trace exchange, finite-S sign, negative
owner integration, Burnol identity, and `_root_.RiemannHypothesis` remain
open.
