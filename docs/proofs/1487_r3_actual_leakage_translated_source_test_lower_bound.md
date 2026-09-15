# 1487 — R3 actual leakage lower bound on translated source tests

**Consumer:** the detector-specific healthy-`CompactLog` B5 chain, with target
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

**Evidence:** formal Lean result in
[`C1G8R3LeakageTranslateLowerBound.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageTranslateLowerBound.lean),
paired audit in
[`C1G8R3LeakageTranslateLowerBoundAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageTranslateLowerBoundAudit.lean).
Focused build log: `0916_leakage_translate_lower_bound_try18.log`; 3683 jobs,
zero `error:` lines, zero `sorryAx`, and two standard-axiom audit terminators.

For a selected owner and a parameter at which its compact source test has a
nonzero Laplace value, the theorem
`sourceRootCompletedRightCommutatorLeftLeg_sourceTest_translate_norm_lowerBound`
proves that the actual unit-scale R3 leakage output on right translates of
that source test eventually has norm at least half the selected-root output
norm. The latter is positive: the source test is nonzero, and its positive
autocorrelation at zero makes its root convolution nonzero.

The leakage identity used is the exact same-carrier Fourier-leakage normal
form. Far enough right, the translated compact source test is fixed by the
positive-half-line projection. The translated source Fourier-support
projection tends to zero, while root convolution commutes with global-log
translation. The triangle inequality then gives the stated output lower
bound.

This proves an ambient lower-energy orbit for the leakage leg. It does not
formalize normalization or pairwise orthogonality of the translated inputs,
and therefore does not yet refute Hilbert--Schmidt or trace-class behavior.
It also does not identify this input orbit with the source-compressed G8
diagonal leg or establish a cutoff-to-trace readback. No detector sign, C3,
`SourceRH`, or RH conclusion follows from this record.

Follow-up records [1488](1488_r3_leakage_orthonormal_translation_orbit.md)
and [1489](1489_r3_leakage_orthonormal_orbit_energy_obstruction.md) close the
normalization and orthonormality step and prove non-summability on that ambient
orbit. The source-compressed G8 diagonal transfer remains open.
