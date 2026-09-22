# 1863 - Explicit affine base in the healthy all-index producer

Date: 2026-09-23.

Status: Formally verified in Lean; same-owner producer wiring.

`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets_all_indices_of_base_data`
is the base-data consumer for the all-index healthy unscaled assembly. The
former existential-base theorem remains available as a compatibility wrapper.

`exists_indexed_orbitG8Geometry_of_sourceNontrivialZero_right` now obtains its
base from `exists_affine_base_with_unit_targets_and_quadratic_decay`, then
feeds the explicit support, unit target equations, and quadratic tail into the
same all-index assembly and indexed `OrbitG8Geometry` owner.

Verification: WSL focused build `explicit-affine-g8.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and paired Audit declarations with only
`[propext, Classical.choice, Quot.sound]`.

This closes an interface boundary only. The finite coefficient/basis budget
needed for strict contraction and detector-specific signed semi-local
positivity remain open; no RH conclusion is asserted.
