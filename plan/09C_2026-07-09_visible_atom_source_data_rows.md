# 09C Visible Atom Source-Data Rows

Date: 2026-07-09

Status:
  Parallel manual-AI lane.  This document owns only the visible atom
  source-data normalization row.


## Result First

Current result:

```text
Partial lower proof in the 09C scratch module.
```

Target:

```lean
NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomSourceDataRowsCalibration
```

Source shape in `ConnesWeilRH/Route/CC20RouteRealization.lean`:

```lean
∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
  let data := r.sourceBackedTest.finitePrimeSourceDataOwner
  let f := r.sourceBackedTest.weilTest
  let lambda := r.bridge.sourceTraceReadOff.lambda
  (((fixedLambdaArithmeticSourceTestCertificatesForAllTests data) f f)
    .certificate lambda r.bridge.sourceTraceReadOff.oneLtLambda)
    .atomsWithSourceTest.toNormalization =
  (sourceAtoms.atomsWithSourceTest r).toNormalization
```


## What It Is

This lane checks whether the visible atom normalization used by the
source-Weil-form path is exactly the atom normalization read from the
source-data certificate for the same `data`, `f`, and `lambda`.

```text
source-data certificate
  data, f, lambda
        |
        v
certificate.atomsWithSourceTest.toNormalization
        |
        | should equal
        v
sourceAtoms.atomsWithSourceTest r .toNormalization
```


## Why It Matters

09A and 09B can prove that the route package uses the source-data certificate
family, but 09C is the row that ties that certificate family to the visible atom
normalization used by the finite-prime read-off.


## How To Attack

1. Inspect the definition of
   `NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormVisibleAtomForSourceTestNormalizationCalibration`.

2. Compare its source atom object against
   `fixedLambdaArithmeticSourceTestCertificatesForAllTests data`.

3. Avoid broad `simp`; use exact read-off lemmas where available.

4. If the objects are different by construction, record the mismatch and reject
   this route boundary.


## Files

Allowed:

```text
plan/09C_2026-07-09_visible_atom_source_data_rows.md
ConnesWeilRH/Dev/Parallel09C_VisibleAtomSourceDataRows.lean
```

Read-only evidence files:

```text
ConnesWeilRH/Route/CC20RouteRealization.lean
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
  A named theorem proving the visible atom source-data row, with no sorryAx.

Rejected:
  A precise mismatch showing `sourceAtoms` can be chosen independently from
  the source-data certificate normalization.
```

Do not replace this with a package atom wrapper or a raw Prop stating equality.


## 2026-07-09 Scratch Result

Result:

```text
Partial / lowered, not production-integrated.
```

What moved:

```text
VisibleAtomSourceDataRows
|
+-- source-data certificate source-test read-off
|     certificate.support.sourceTest = concrete common source test
|
+-- source-data certificate visible read-off
      certificate atoms, reindexed to the concrete common source test,
      agree with the source-Weil-form visible arithmetic data
```

Lean evidence in `ConnesWeilRH/Dev/Parallel09C_VisibleAtomSourceDataRows.lean`:

```text
parallel09C_sourceDataCertificateAtoms_toNormalization
parallel09C_visibleAtomSourceDataRows_of_toNormalization_eq
parallel09C_visibleAtomSourceDataRows_of_sourceDataCertificateVisibleReadOff
parallel09C_sourceAtoms_forced_eq_sourceDataCertificateAtoms
```

Meaning:

```text
09C should not try to prove 09A's common-test selector row internally.  The
source-data certificate atoms are indexed by the certificate support source
test, while the route `sourceAtoms` owner is indexed by the concrete common
source test.  The scratch proof therefore takes the source-test read-off as an
explicit dependency and leaves 09C with the visible arithmetic atom read-off.
```

Verification:

```text
fresh ext4 verification directory:
  /home/peter/verify/Connes-Weil-RH-Proof-09c-20260709084601

commands:
  flock /tmp/connes-weil-rh-lake.lock -c \
    'lake env lean ConnesWeilRH/Dev/Parallel09C_VisibleAtomSourceDataRows.lean'

  flock /tmp/connes-weil-rh-lake.lock -c \
    'lake build ConnesWeilRH.Dev.Parallel09C_VisibleAtomSourceDataRows'

focused audit:
  import ConnesWeilRH.Dev.Parallel09C_VisibleAtomSourceDataRows
  #check / #print axioms for the four declarations above

axioms:
  [propext, Classical.choice, Quot.sound]
  no sorryAx
```

Next safe action:

```text
Coordinate with 09A for the source-test read-off, then attack
`Parallel09C.SourceDataCertificateVisibleReadOff`.  Do not port this scratch
module into production until the coordinator combines the non-overlapping 09A
and 09C leaves.
```


## Verification

Smallest WSL command:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake env lean ConnesWeilRH/Dev/Parallel09C_VisibleAtomSourceDataRows.lean'
```

Focused audit:

```lean
#check <09C theorem name>
#print axioms <09C theorem name>
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
