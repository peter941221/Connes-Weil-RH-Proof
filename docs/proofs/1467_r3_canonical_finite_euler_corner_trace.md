# 1467 — R3 canonical finite-Euler source-corner trace

**Date:** 2026-09-15.

**Status:** formal source-side trace bridge; G8 cutoff/readback remains open.

**Consumer:** same-owner, detector-selected `CompactLog` B5 positivity for the
healthy tower detector, followed by the existing `SourceRH` contradiction.

## Result

The all-scale prolate-factor square-sum from record 1465 now supplies the
trace-legality input for the source root-completed finite-Euler corner using
the exact canonical family of the selected owner:

```text
g8CanonicalFamily owner := FinitePrimePowerFamily.ofSelectedOwner owner.
```

The new leaf proves
`g8CanonicalSourceFiniteEulerCorner_isTraceClassAlong_all_scales` along the
explicitly named global basis. It also exports the existing exact ordered
renewal readback as
`g8CanonicalSourceFiniteEulerCorner_trace_eq_orderedRenewalPairing`:
the basis sum is outside and the finite-prime renewal sum is inside. No
exchange of these sums is claimed.

This is an actual selected-owner source-corner trace theorem. It supplies the
canonical finite-prime instance of the paired finite-Euler trace interface
without assuming a Hilbert--Schmidt estimate for the common-right leg by
itself.

## Boundary

The source root-completed corner is not the G8 cutoff pair
`g8SourceCutoffPairData`. This theorem does not identify their traces, prove a
vanishing cutoff remainder, read the limit back as `qw`, or establish the
detector-specific semi-local sign. In particular, it does not close SC4 or
construct `G8SameOwnerReadbackData`; those remain the next R3 obligations.

## Acceptance

Focused log: `20260915_r3_canonical_finite_euler_trace_try3.log` (WSL ext4 build log).

- `Build completed successfully (3829 jobs)`
- zero `error:` lines and zero `sorryAx`
- two `#print axioms` results, both the standard
  `[propext, Classical.choice, Quot.sound]`

The first two compile attempts exposed missing namespace opens and invalid
local option syntax; try3 is the accepted source and audit build.
