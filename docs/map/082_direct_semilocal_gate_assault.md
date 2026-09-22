# 082 — Direct semi-local gate assault (Option A)

Date: 2026-09-22.

Status: formal producer contract landed; analytic existence of the witness geometry remains open.
Subordinate to binding B5 route ruling in [003](003_b1_b5_minimal_exit_route_selection.md).

Consumer: the healthy `CompactLog`, detector-specific B5 statement `0 <= qw g`,
through `SourceRH` and Mathlib RH.

## Result

`C1P2DirectSemiLocalGate.lean` establishes the direct consumer interface for Option A
(Bone 4 direct assault) without intermediate matrix or coboundary wrappers.

It proves:
```text
archimedeanTerm(g * g) + finitePrimeSum(g * g) <= 0
  ==> orbitWindowSemiLocalGate(g)
  ==> 0 <= qw(g)
  ==> SourceRH
```

Specifically:
- `sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate`: existence of an `OrbitG8Geometry`
  satisfying `orbitWindowSemiLocalGate g` for each hypothetical right-hand zero directly
  implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_primeAbsorption`: if the finite prime sum is absorbed
  by the negative Archimedean margin `- archimedeanTerm g.convolutionSquare`, `SourceRH` follows.
- `sourceRH_of_right_orbitGeometry_archimedean_and_finitePrimeSum_nonpos`: componentwise
  nonpositivity directly implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_bilateralProfile_nonpos`: pointwise profile nonpositivity
  implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_margin_transfer`: intermediate scalar margin transfer
  implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_signedBudget`: signed credit/deficit budget absorption
  implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_primeAbsorb_norm`: norm-level prime absorption implies `SourceRH`.
- `sourceRH_of_right_orbitGeometry_primeRange_majorant`: finite-range absolute profile majorant
  absorption implies `SourceRH`.

## Boundary and Open Obligation

This formalizes the cleanest possible exit for Bone 4. The remaining open mathematical
obligation is to construct an `OrbitG8Geometry` whose actual finite visible-prime sum
satisfies the absorption condition.

Evidence: `ConnesWeilRH/Dev/C1P2DirectSemiLocalGate.lean` and `C1P2DirectSemiLocalGateAudit.lean`;
build log `build-logs/1833_direct_semilocal_gate_extensions.log` (clean, standard axioms, zero sorryAx).
