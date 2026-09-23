# 1916 — Fixed-owner decay constants for the four-point span

Date: 2026-09-23.

Status: FORMAL quantitative reduction. The joint tail-to-`lambda^2` margin,
the same-span gate sign, and the RH contradiction remain open. This record is
a project derivation from existing compact-log decay theorems, not an
originality or RH claim.

## Owner and result

For fixed `CompactLogTest` owners `base` and `correction` and fixed
hypothetical zero parameter `rho`, the Lean theorem
`exists_selectedOwner_fullOrbit_span_fourthOrderSpectralTail_constants`
chooses nonnegative constants `C4`, `C2`, and `T` before the convolution count
`n`, span coefficient `lambda`, and tail tolerance `epsilon`. The constants
provide:

- quartic vertical decay for `base`;
- quadratic vertical decay for `correction`;
- half-contraction for `base` above `T`;
- the existing four-point spectral tail whenever its explicit scalar budget
  is below `epsilon^2`.

The proof obtains the quartic and quadratic bounds from
`C1SpectralWeil.exists_uniform_compactLog_laplaceAt_vertical_quartic_decay`
and
`C1SpectralWeil.exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay`.
It obtains `T` from
`exists_laplaceAt_vertical_half_contraction_of_quadratic_bound` applied to the
base's generic quadratic estimate. Thus the correction estimate and base
threshold are no longer separate assumptions whose choice can drift with
`n` or `lambda`.

## Remaining obligation

The theorem still requires the actual joint scalar margin

```text
(3 + norm(rho))^4 * ((3 + norm(rho))^4 + abs(lambda))^2 * (2*pi)^12
  * ((1/2)^n * C4 * C2)^2 < epsilon^2.
```

In particular, it proves no lower bound for a gate-selected `lambda_n` and
does not establish the same-span gate sign. The 103 campaign's core
obligation is therefore reduced only by fixing all analytic decay constants
in advance; Cut 1 remains open.

## Verification

Focused command:

```text
lake build ConnesWeilRH.Dev.C1FourPointHighShellTail ConnesWeilRH.Dev.C1FourPointHighShellTailAudit
```

The build completed successfully in 3809 jobs with zero `error:` lines.
The audit prints exactly `[propext, Classical.choice, Quot.sound]` for the new
theorem, with no `sorryAx`.
