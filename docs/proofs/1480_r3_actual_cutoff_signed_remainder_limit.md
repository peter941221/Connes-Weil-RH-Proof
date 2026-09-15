# 1480 — R3 actual-cutoff same-owner signed remainder limit

**Status:** FORMAL ordinary-trace convergence for the signed finite-Euler
remainder response after the actual source-compressed G8 cutoff. Its limit is
not shown to vanish, and the full G8 trace-to-`qw` readback remains open.

**Consumer:** the signed remainder leg of the actual G8 cutoff ledger on the
selected healthy-`CompactLog` owner. The downstream B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The new leaf
[`C1G8R3ActualCutoffSignedRemainderLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffSignedRemainderLimit.lean)
proves

```text
trace(C_n† * R * C_n) -> trace(C∞† * R * C∞)

R = sourceActualBandFiniteEulerSoninResponse
      - sourceBandGramResponse
C_n = the actual source-compressed physical G8 cutoff
C∞ = the same-owner source compression of the global convolution
```

The proof transfers the first-jet and source-band terms separately through
their existing same-owner Hilbert--Schmidt pair data, using the actual
uniformly bounded doubled strong limit from record 1479, then subtracts their
ordinary traces. This preserves the signed remainder orientation.

The result is a cutoff-transport theorem, not a remainder estimate. It does
not prove that the limiting signed remainder is zero, identify the other G8
metric channels, construct `G8SameOwnerReadbackData`, or identify the full
positive trace limit with `qw`. The detector-specific semi-local sign, C3,
and RH remain open.

The paired audit prints only `[propext, Classical.choice, Quot.sound]`.
Acceptance log `0915_signed_remainder_try3.log`: `Build completed
successfully (3956 jobs)`, zero `error:` lines, zero `sorryAx`, and one
`Quot.sound]` occurrence for the one audit print. The frozen-route guard also
passed; no route namespace or binding route selection changed.
