# 1832 — P2 direct semi-local gate producer

Date: 2026-09-22

## Result

`C1P2DirectSemiLocalGate.lean` formalizes the direct Option A producer contract
for the healthy `CompactLog` B5 mainline without intermediary span matrices,
coboundary primitives, or credit/deficit decompositions.

It proves:
1. `orbitWindowSemiLocalGate_eq_archimedean_add_finitePrimeSum`: exact definitional
   identity of the semi-local gate as `archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare <= 0`.
2. `sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate`: if for every right-hand
   off-line zero there exists an `OrbitG8Geometry rho g` satisfying `orbitWindowSemiLocalGate g`,
   then `SourceRH` holds unconditionally.
3. `sourceRH_of_right_orbitGeometry_finiteRangeGate`: equivalent explicit finite-range
   bilateral profile formulation.
4. `sourceRH_of_right_orbitGeometry_primeAbsorption`: the absorption formulation
   `finitePrimeSum g.convolutionSquare <= - archimedeanTerm g.convolutionSquare`
   directly implying `SourceRH`.
5. `sourceRH_of_right_orbitGeometry_archimedean_and_finitePrimeSum_nonpos`:
   componentwise nonpositivity of Archimedean and finite-prime parts.
6. `sourceRH_of_right_orbitGeometry_bilateralProfile_nonpos`: pointwise
   nonpositivity of the bilateral profile at visible primes.
7. `sourceRH_of_right_orbitGeometry_margin_transfer`: intermediate scalar
   margin absorption.
8. `sourceRH_of_right_orbitGeometry_signedBudget`: signed profile credit/deficit
   budget absorption.
9. `sourceRH_of_right_orbitGeometry_primeAbsorb_norm`: absolute-value norm
   absorption.
10. `sourceRH_of_right_orbitGeometry_primeRange_majorant`: finite-range
    absolute profile majorant absorption.

The leaf and its paired audit `C1P2DirectSemiLocalGateAudit.lean` build clean with
3784 jobs, zero `error:`, zero `sorryAx`, and only the standard three axioms
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This closes the direct consumer bridge for Bone 4 in its unadorned, native form.
The analytic construction of the witness geometry satisfying `orbitWindowSemiLocalGate g`
remains an open mathematical obligation.

## Verification

Build log: `/home/peter/rh/build-logs/1833_direct_semilocal_gate_extensions.log`.
All ten declarations verified on standard axioms with zero sorryAx.
