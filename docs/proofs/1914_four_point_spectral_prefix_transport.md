# 1914 — Four-Point Spectral Prefix Transport on the Selected Detector

Date: 2026-09-23.

Status: Formal same-owner reduction; not an RH proof and not a completed tail
estimate.

## Owner and purpose

The active consumer is the phase-balanced Two-Span Spectral Contradiction route
on `CompactLogTest`. The existing two-point annihilator kills only the marked
Hermitian pair. Its two conjugate orbit points can therefore contaminate a
finite spectral prefix. This brick composes a second two-point annihilator,
without changing the owner or widening support:

`fullFunctionalEquationOrbitAnnihilator g rho`

kills all four points of `sourceFunctionalEquationOrbit rho`.

## Formal results

`C1FourPointSpectralPrefixTransport.lean` and its audit prove:

- `fullFunctionalEquationOrbitAnnihilator_support_subset_Icc`: support remains
  in the input interval;
- `fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple`: the CC20
  triple vanishing is preserved;
- `fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_of_laplaceAt_eq_zero`:
  any zero of the original detector square is transported to the span square;
- `fullOrbitSpanVector_convolutionSquare_laplaceAt_eq_zero_or_neg_sq_of_mem_orbit`:
  each orbit term of the transported square is either zero or `-lambda^2`;
- `finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport`:
  for a finite source-zero prefix containing `rho`, if every non-orbit point
  is already killed by the original detector square and the centered detector
  has the negative raw orbit values, then
  `Re(prefix) <= -xiMultiplicity(rho) * lambda^2`;
- `halfDensityShift_centered_negativeSourceOrbitValues`: the raw construction
  values read back at centered coordinates of the actual half-density-shifted
  detector.

The exact Laplace multiplier is also recorded by
`laplaceAt_fullFunctionalEquationOrbitAnnihilator` and
`laplaceAt_fullOrbitSpanVector`: the annihilator contributes four centered
linear factors, and the span subtracts `lambda` from that multiplier. The next
tail proof must therefore supply the corresponding weighted square estimate;
the earlier unweighted fourth-order tail theorem is not an automatic consumer.

This is a strict reduction of the live assumption ledger: the finite-prefix
obligation no longer includes any unproved sign or cancellation for the other
three orbit points. The remaining input is exactly the existing non-orbit
finite square-zero certificate plus the high-shell tail margin.

## What remains open

The brick does not prove `qw >= 0` for the detector, does not prove the
high-shell tail is smaller than the negative prefix margin, and does not prove
the transported span has the gate sign required by the semi-local route. Those
are the next core obligations; generic exit wrappers and normalized-owner
density work remain frozen.

## Verification

Focused log: `build-logs/20260923_four_point_prefix_transport_try13.log`.

The build completed successfully (3808 jobs), with zero `error:` lines, zero
`sorryAx`, and each audited declaration depending only on
`[propext, Classical.choice, Quot.sound]`.
