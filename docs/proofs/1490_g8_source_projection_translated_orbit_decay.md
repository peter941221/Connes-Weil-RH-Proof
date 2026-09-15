# 1490 — Source projection kills the translated ambient leakage orbit

Date: 2026-09-16.

**Consumer:** the same-owner G8 detector-root energy readback for the
healthy-`CompactLog`, B5-shaped semi-local positivity branch.

**Evidence:** formal Lean theorem
[`sourceSoninProjection_selectedSourceTranslationOrbit_norm_tendsto_zero`](../../ConnesWeilRH/Dev/C1G8R3SourceProjectionTranslatedDecay.lean),
with paired audit
[`C1G8R3SourceProjectionTranslatedDecayAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3SourceProjectionTranslatedDecayAudit.lean).
Acceptance log: `0916_source_projection_decay_try2.log`; build completed
successfully (3685 jobs), zero `error:` lines, zero `sorryAx`, and one
standard-axiom audit terminator.

For the separated right-translation orbit of the selected compact source
test, the unit-scale archimedean Fourier-support projection tends to zero by
the existing Hardy translated-tail theorem. The complete source-Sonin
projection is absorbed by that Fourier-support projection and has operator
norm at most one. Hence the source-Sonin projection of the orbit also tends to
zero in norm.

This formally rules out transferring the ambient leakage lower bound by
projecting that particular orbit into `sourceSoninCarrier` and normalizing:
the projected vectors lose their norm. It is not a counterexample to either
G8 diagonal energy estimate, and it does not identify any ambient trace with
the source-basis trace. A new source-carrier witness must be built through the
actual compressed convolution/coframe interface. The G8 readback, semi-local
sign, C3, and RH remain open.
