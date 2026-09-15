# 1481 — R3 actual-cutoff paired cross-channel trace limit

**Status:** FORMAL trace convergence for both ordered actual G8
leakage/source cross channels and for their real paired sum. The paired value
is not identified with `qw`.

**Consumer:** the paired leakage/source part of the actual cutoff metric ledger
on the selected healthy-`CompactLog` owner. The downstream B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The leaf
[`C1G8R3ActualCutoffPairedCrossTrace.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffPairedCrossTrace.lean)
proves that the literal source/leakage channel is the adjoint of the already
controlled leakage/source channel. The identity uses self-adjointness of the
detector Gram while retaining the exact finite G8 cutoff and same owner.
Ordinary trace along the same source basis therefore conjugates the forward
channel trace. Continuity of complex conjugation transfers the limit, and
linearity of the trace gives convergence of the paired sum to

```text
2 * Re(trace(C∞† * (-sourceBandGramResponse†) * C∞))
```

where `C∞` is the same-owner source compression of the global detector
convolution from record 1479. This closes both ordered cross orientations and
their signed real pairing. It does not close the survivor-survivor,
survivor-boundary, or boundary-boundary channels in the separate four-channel
coframe ledger; it also does not prove remainder decay, construct
`G8SameOwnerReadbackData`, or read the full positive trace back as `qw`.

The paired audit has three declarations, each printing only
`[propext, Classical.choice, Quot.sound]`. Acceptance log
`0915_paired_cross_try4.log`: `Build completed successfully (3957 jobs)`, zero
`error:` lines, zero `sorryAx`, and three `Quot.sound]` occurrences.
