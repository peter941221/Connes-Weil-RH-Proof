# 1489 — R3 leakage energy diverges on an ambient orthonormal orbit

Date: 2026-09-16.

**Consumer:** the detector-specific healthy-`CompactLog` B5 chain, for the
same selected owner and finite visible-prime family.

**Evidence:** formal Lean result in
[`C1G8R3LeakageOrbitEnergy.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageOrbitEnergy.lean),
with paired audit in
[`C1G8R3LeakageOrbitEnergyAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageOrbitEnergyAudit.lean).
Acceptance is included in `0916_leakage_three_batches_final.log`.

The actual unit-scale leakage operator applied to the normalized orbit from
record 1488 equals the normalized scalar multiple of its untranslated
leakage columns at indices spaced by the source support diameter. Record 1487
gives an eventual lower bound for those raw translated columns. After
normalization, Lean proves that the output norms remain eventually at least
`sourceTestRootImageNorm / (2 * sourceTestLpNorm)`, a positive constant. Since
summable real sequences tend to zero, the squared output norms cannot be
summable along this orthonormal input sequence.

This is an ambient `finiteSCarrier` energy obstruction for the uncompressed
unit-scale leakage leg. The actual G8 diagonal energy identity in record 1484
uses root-leg columns on a named basis of `sourceSoninCarrier` after the
literal source compression. No theorem transfers the orbit in record 1488 to
that basis or identifies these ambient columns with those compressed columns.
Thus this result does not refute either G8 diagonal estimate, establish the
trace-to-`qw` readback, prove detector-specific `qw` positivity, or close C3.
The healthy-`CompactLog` B5 route remains unchanged.
