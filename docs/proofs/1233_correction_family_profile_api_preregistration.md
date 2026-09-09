# 1233 - Explicit residual correction-family/profile API

Date: 2026-09-09.

Status: LANDED focused formal interface brick.  This record does not claim an
affine family, a profile factorization, a sign, or RH.

Consumer: the same healthy-`CompactLog` selected-detector P2 owner from map
record [`003`](../map/003_b1_b5_minimal_exit_route_selection.md).  This brick
serves the owner/API gap identified by G4/G6; it is not itself an L4/A4
producer.

## Target

For a finite node set `nodes` and a fixed residual window `(lower, upper)`,
package the existing theorem
`exists_residualWindow_correction` as a data-bearing family

```text
y : (FiniteMellinNode nodes → ℂ) → CompactLogTest
```

with checked support and node readback fields.  Add the selected-owner
physical observable

```text
(base, n, y, x) ↦
  bilateralProfile ((selectedOwner base (family.value y) n).convolutionSquare) x.
```

The API must retain the genuine physical `log n` observable and must not
replace it by a finite Mellin-node value.  The construction may use classical
choice for this first selector layer; no claim of affinity or canonical
linear dependence on `y` is made.

## Falsifiers and guards

The brick fails if support or node readback cannot be transported from the
existing interpolation theorem, or if the selected-owner profile does not
typecheck on the same `CompactLogTest` owner.  It must not add a positivity
field, `qw` field, RH premise, or a node/profile equality.  A successful build
only removes the first existential API wrapper; G4.4 and the G6 internal
counterterm remain open.

## Verification

Deliver a focused module and paired `...Audit` module.  Acceptance requires
the owning build footer, zero `error:` lines, and audited declarations with
only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

RH is not claimed.

## 4 Post-run addendum

The API landed in
`ConnesWeilRH/Dev/C1HealthyYoshidaCorrectionFamily.lean` with paired audit
module `C1HealthyYoshidaCorrectionFamilyAudit.lean`.

The declarations are:

```text
ResidualCorrectionFamily
residualCorrectionFamily
residualCorrectionFamily_value_support
residualCorrectionFamily_laplaceAt_value
selectedOwnerBilateralProfile
selectedOwnerBilateralProfile_eq
selectedOwnerVisiblePrimeSet
selectedOwnerVisiblePrimeProfileWeightedSum
selectedOwnerFinitePrimeSum_eq_visibleProfileWeightedSum
```

Focused WSL verification used the resource runner and completed successfully
(`3661 jobs`) with zero `error:` lines and zero `sorryAx`.  Every audited
declaration reports exactly `[propext, Classical.choice, Quot.sound]`.

The brick removes the nested existential wrapper for the residual correction
and exposes the actual finite visible-prime weighted profile on the selected
owner.  It deliberately leaves the selector non-affine and choice-based;
there is still no theorem that finite node data determine this profile, no
internal positive kernel, and no `0 <= qw` result.
