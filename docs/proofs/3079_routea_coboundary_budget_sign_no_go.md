# 3079 - Route A coboundary budget sign no-go

Date: 2026-10-20

Status: `SAME-OWNER CERTIFICATE EXCLUDED UNDER A HYPOTHETICAL RIGHT ZERO`.

## Result

`C1RouteAFixedOwnerGroupedResidual.lean` now proves:

- `groupedResidual_pos_of_healthyOrbitGeometry`: every `OrbitG8Geometry`
  attached to a right-of-line zero has
  `archimedeanTerm + integral(canonical residual) > 0`.
- `no_coboundaryCertificate_of_healthyOrbitGeometry`: no
  `OrbitPhysicalKernelCoboundaryCertificate` with `residual_budget <= 0` can
  be attached to that same geometry.
- `no_rightZero_coboundaryProducer_witness`: under a hypothetical right zero,
  the exact existential producer consumed by
  `sourceRH_of_right_orbitGeometry_coboundaryCertificate` has no witness.

The proof uses three compiled identities. The canonical grouped residual
total equals `ICgate`; health of the same geometry gives `ICgate > 0`; and an
arbitrary certificate residual has the same interval integral as the actual
physical kernel by its derivative identity and zero boundary values. The last
step is necessary because the certificate permits an arbitrary residual
function, not only the canonical residual.

## Consequence

This identifies the proposed certificate's sign interface as the central
RH-level step. The consumer needs a nonpositive budget, while the same-owner
healthy detector theorem gives a strictly positive value under the
right-zero hypothesis. A continuum enclosure or tighter tail estimate cannot
bridge those signs as an auxiliary bound: proving the requested inequality
would itself supply the RH-level contradiction. This is not a proof that a
right-of-line zero exists, and it is not a proof of RH.

The producer/consumer signs are aligned, not accidentally reversed:
`sourceRH_of_right_orbitGeometry_signedBudget` turns the signed budget into
the orbit-window gate and then uses
`qw_nonneg_of_archimedean_plus_bilateralProfile_weighted_sum_nonpos` to get
`qw >= 0`. The same geometry's healthy detector gives `qw < 0`. Thus the
nonpositive budget is exactly the missing contradiction, not a convention
bug to fix.

The geometry is not missing:
`exists_healthyOrbitG8Geometry_of_sourceNontrivialZero_right` in
`C1G8R0OrbitGeometry.lean` constructs it for each hypothetical right zero.
What cannot be attached is the nonpositive coboundary certificate. Further
Route A work should keep the owner and signs fixed and target a genuinely new
analytic argument for the RH-equivalent inequality. Do not spend time on the
3076-3078 fixed coefficient repair owner for this purpose; it is a different
owner.

## Verification

Linux ext4 Lean 4.30 verification passed for
`C1RouteAFixedOwnerGroupedResidual` and its audit. `#print axioms` reports
exactly `[propext, Classical.choice, Quot.sound]` for all three new theorems.
No new axiom or RH claim was introduced.
