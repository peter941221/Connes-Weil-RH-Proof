# Proof record 1796: polynomially weighted exponential tails

Date: 2026-09-21

Status: formal, reusable analytic interface.

`C1G8R3WeightedExponentialTail.lean` proves that `t^2 * exp(-a*t)` is
integrable on the positive half-line for every `a > 0`, by instantiating
Mathlib's real-power times exponential tail theorem at power `p = 1` and
real power `s = 2`. A measure-preserving negation transport supplies the
corresponding `t^2 * exp(a*t)` estimate on the negative half-line.

This is the scalar tail consumer required when the quadratic scattering-phase
bound is multiplied into the critical Mellin profile. It does not yet prove
the weighted integrability of the actual profile or its derivative formulas;
those remain the next substantive consumer. The S3 kernel-diagonal estimate,
detector-specific semi-local positivity, and RH remain open.

Verification: focused paired build log
`/home/peter/rh/build-logs/weighted-exp-tail-v4.log`; build completed
successfully (3559 jobs), no `error:` lines, and the paired audit reports
only `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
