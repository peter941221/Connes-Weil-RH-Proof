# 09D Direct Term Mass Rows

Date: 2026-07-09

Status:
  Parallel manual-AI lane.  This document owns only the two source-Weil-form
  direct finite-prime term mass rows.

  2026-07-09 result: accepted-candidate classification, not coordinator
  accepted route progress.  The direct term mass owner is equivalent to the
  existing route pole-collapse calibrations, so it is not an independent lower
  source-arithmetic producer.


## Result First

Current result:

```text
Classified as pole-collapse-level.

direct term mass rows
  <-> source-Weil-form restricted QW pole collapse
      + source-Weil-form global psi pole collapse
  <-> existing route restricted QW pole-collapse calibration
      + existing route psi pole-collapse calibration
```

Target owner:

```lean
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
```

Component rows:

```lean
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRestrictedTermMassCalibration
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalTermMassCalibration
```


## What It Is

This lane tries to prove the two finite-prime mass identities directly in the
source-Weil-form term API:

```text
restricted:
  sum over restricted prime powers of W.finitePrimeTerm
    =
  W.archimedeanTerm

global:
  sum over global prime powers of W.finitePrimeTerm
    =
  -W.archimedeanTerm
```


## Why It Matters

These rows are the current lower mass owner.  They avoid the old existential
source-evaluation API and keep the same `sourceWeilForm` selected by the carrier.


## How To Attack

1. Work from `SourceWeilFormData` and `WeilFormSymbols`, not from legacy
   `SourceEvaluationData` unless a named read-off theorem makes the bridge exact.

2. Search for source-side finite-prime summation identities over:
   `restrictedPrimeIndexSet`, `globalPrimeIndexSet`, `finitePrimeTerm`, and
   `archimedeanTerm`.

3. Prove restricted and global rows separately if possible.

4. If one row is equivalent to no-off-line source-zero or SourceRH, reject it
   with named evidence instead of wrapping it.


## Files

Allowed:

```text
plan/09D_2026-07-09_direct_term_mass_rows.md
ConnesWeilRH/Dev/Parallel09D_DirectTermMassRows.lean
```

Read-only evidence files:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/CCM25Concrete.lean
ConnesWeilRH/Source/CC20.lean
```

Forbidden:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
plan/08A_2026-07-08_D1_restricted_test_cc20_sufficiency_plan.md
MEMORY.md
AGENTS.md
```


## Acceptance Gate

Accepted if the lane provides one of:

```text
Good:
  Named theorems for both restricted and global direct term mass rows, or a
  named owner bundling both, with no sorryAx.

Partial:
  One row is proved cleanly and the other has a concrete named blocker.

Rejected:
  A named equivalence to SourceRH / no-off-line source-zero, or a concrete
  counterexample to one of the mass identities.
```

Do not close this lane through detector-only coverage, stored Mellin rows,
stored determinant rows, `True`, or `Set.univ`.


## 2026-07-09 Scratch Result

Scratch file:

```text
ConnesWeilRH/Dev/Parallel09D_DirectTermMassRows.lean
```

Named evidence:

```text
Parallel09DRestrictedQWPoleCollapse
Parallel09DGlobalPsiPoleCollapse
parallel09D_directRestrictedTermMass_iff_restrictedQWPoleCollapse
parallel09D_directGlobalTermMass_iff_globalPsiPoleCollapse
parallel09D_directTermMassRows_imply_sourceWeilFormPoleCollapses
parallel09D_restrictedQWPoleCollapse_iff_routeRestrictedQWPoleCollapse
parallel09D_globalPsiPoleCollapse_iff_routePsiPoleCollapse
parallel09D_directTermMassRows_iff_routePoleCollapses
parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations
```

Interpretation:

```text
This lane did not prove the direct term mass rows as ordinary finite-prime
source arithmetic.  It proved that requiring those rows is exactly requiring
the route-level restricted QW pole collapse and psi pole collapse guards.
```


## Verification

Smallest WSL command:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09D_DirectTermMassRows.lean'
```

Focused audit:

```lean
#check <09D theorem name>
#print axioms <09D theorem name>
```

2026-07-09 verification, run from fresh ext4 WSL verification directory
`/home/peter/verify/Connes-Weil-RH-Proof-09D-20260709084608` because the
persistent mirror was dirty with unrelated session work:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09D_DirectTermMassRows.lean &&
   lake build ConnesWeilRH.Dev.Parallel09D_DirectTermMassRows'
```

Result:

```text
Build completed successfully.
```

Focused import-facing audit:

```lean
import ConnesWeilRH.Dev.Parallel09D_DirectTermMassRows

#check ConnesWeilRH.Route.parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations
#print axioms ConnesWeilRH.Route.parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations
```

Result:

```text
'ConnesWeilRH.Route.parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears in the focused audit.


## Handoff Template

```text
AI session handoff:
  status: accepted-candidate classification; not coordinator-accepted
  files changed:
    ConnesWeilRH/Dev/Parallel09D_DirectTermMassRows.lean
    plan/09D_2026-07-09_direct_term_mass_rows.md
  declarations changed:
    Parallel09DDirectTermMassRowsCalibration
    Parallel09DRestrictedQWPoleCollapse
    Parallel09DGlobalPsiPoleCollapse
    parallel09D_directRestrictedTermMass_iff_restrictedQWPoleCollapse
    parallel09D_directGlobalTermMass_iff_globalPsiPoleCollapse
    parallel09D_directTermMassRows_imply_sourceWeilFormPoleCollapses
    parallel09D_restrictedQWPoleCollapse_iff_routeRestrictedQWPoleCollapse
    parallel09D_globalPsiPoleCollapse_iff_routePsiPoleCollapse
    parallel09D_directTermMassRows_iff_routePoleCollapses
    parallel09D_directTermMassRows_iff_routePoleCollapseCalibrations
  old paths removed: none
  remaining blockers:
    Coordinator must decide whether to reject 09D as a lower producer or port
    the guard equivalence theorem into the production route module.
  WSL build:
    lake env lean + lake build passed in
    /home/peter/verify/Connes-Weil-RH-Proof-09D-20260709084608
  focused axiom audit:
    final theorem axioms are [propext, Classical.choice, Quot.sound];
    no sorryAx
  next safe action:
    Do not edit production route in this parallel lane.  Coordinator should
    port/reject using the named equivalence theorem.
```
