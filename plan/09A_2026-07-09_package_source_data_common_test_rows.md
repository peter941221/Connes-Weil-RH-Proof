# 09A Package Source-Data Common-Test Rows

Date: 2026-07-09

Status:
  Parallel manual-AI lane.  This document owns only the common-test selection
  row below the 08A split package source-data owner.


## Result First

Current result:

```text
Open.
```

Target:

```lean
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageSourceDataCommonTestRowsCalibration
```

Source shape in `ConnesWeilRH/Route/CC20RouteRealization.lean`:

```lean
∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
  r.sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction =
    r.sourceBackedTest.weilTest
```


## What It Is

This lane checks whether the source-data owner stored on each square restricted
route test was built from the same `weilTest` used by that route test.

```text
route test r
|
+-- r.sourceBackedTest.weilTest
|
+-- r.sourceBackedTest.finitePrimeSourceDataOwner.commonTestFunction
|
+-- 09A target: these two are equal
```


## Why It Matters

If this equality fails, later package-source rows may be proving finite-prime
arithmetic for a different test function than the route is consuming.  That
would make the package-source path invalid for 08A.


## How To Attack

1. Trace the constructor of `NormalizedRouteBackedCC20SquareRestrictedTest`.

2. Trace the construction of `sourceBackedTest`.

3. Check whether `finitePrimeSourceDataOwner.commonTestFunction` is assigned
   from `weilTest` definitionally.

4. If it is definitional, produce a tiny candidate theorem in the scratch file.

5. If it is not definitional, record the exact constructor field that permits
   mismatch and mark the lane `rejected`.


## Files

Allowed:

```text
plan/09A_2026-07-09_package_source_data_common_test_rows.md
ConnesWeilRH/Dev/Parallel09A_CommonTestRows.lean
```

Read-only evidence files:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Route/RouteTheorem.lean
ConnesWeilRH/Source/CCM25Concrete.lean
ConnesWeilRH/Source/AnalyticCore.lean
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
  A named theorem proving the common-test row from existing constructors,
  with no sorryAx.

Rejected:
  A named counterexample-style route-constructor mismatch, or a precise field
  audit proving that the row is not derivable from current data.
```

Do not close this lane by adding the equality as a new primitive field.


## Verification

Smallest WSL command:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09A_CommonTestRows.lean'
```

Focused audit:

```lean
#check <09A theorem name>
#print axioms <09A theorem name>
```


## Handoff Template

```text
AI session handoff:
  status:
  files changed:
  declarations changed:
  old paths removed:
  remaining blockers:
  WSL build:
  focused axiom audit:
  next safe action:
```


## 2026-07-09 Codex Handoff

```text
AI session handoff:
  status: rejected for constructor-only closure; accepted as precise field audit
  files changed:
    ConnesWeilRH/Dev/Parallel09A_CommonTestRows.lean
    plan/09A_2026-07-09_package_source_data_common_test_rows.md
  declarations changed:
    ConnesWeilRH.Dev.Parallel09A.expandedSourcePackage_commonTestRow_iff
    ConnesWeilRH.Dev.Parallel09A.sourceObjectCommonData_has_commonTestRow
    ConnesWeilRH.Dev.Parallel09A.sourceObjectPackage_commonTestRow_is_standalone
    ConnesWeilRH.Dev.Parallel09A.yoshidaDetectorSquare_commonTestRow_iff
  old paths removed:
    none
  remaining blockers:
    The 09A row is not forced by the square detector helper constructor.  It
    reduces to the external same-test requirement:

      sourceDataOwner.commonTestFunction =
        normalizedCC20TestSpace.toRouteTest
          (normalizedCC20TestSpace.starConvolution detector.test)

    The lower SourceObjectCommonData layer has this owner/common-test equality,
    but SourceObjectPackage and the route square helper do not expose it as a
    route-facing field.
  WSL build:
    fresh ext4 verification copy, preserving .lake cache from the persistent
    mirror because the persistent mirror had unrelated dirty route changes.
    Command:
      flock /tmp/connes-weil-rh-lake.lock -c \
        'lake build ConnesWeilRH.Dev.Parallel09A_CommonTestRows'
    Result:
      pass
  focused axiom audit:
    import ConnesWeilRH.Dev.Parallel09A_CommonTestRows
    #check / #print axioms for all four declarations above.
    Result:
      all four declarations import-facing; axioms were only
      [propext, Classical.choice, Quot.sound], no sorryAx.
  next safe action:
    Coordinator should not try to prove
    PackageSourceDataCommonTestRowsCalibration from arbitrary
    NormalizedRouteBackedCC20SquareRestrictedTest constructors.  Either carry
    the SourceObjectCommonData owner/common-test equality through a
    data-bearing route/package boundary, or reject the package-source path for
    constructors that accept an unconstrained sourceDataOwner.
```
