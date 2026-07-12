# 05B D1 CC20 Concrete Test-Space Owner Plan

Date: 2026-07-07

Status: parallel execution shard for Plan 05.  This shard creates the concrete
CC20 test-space owner used by the Yoshida and Proposition C.1 shards.

Execution result, 2026-07-07:

```text
Result:
  05B shard-good for the concrete owner.  This does not close Plan 05.

New concrete owner:
  ConnesWeilRH.Source.normalizedCC20TestSpace

Implemented files:
  ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
  ConnesWeilRH/Source/CC20Concrete.lean

Field provenance:
  Test:
    SourceConcreteBaseLayer.concreteTestAlgebra.Test

  toRouteTest:
    SourceConcreteBaseLayer.concreteTestAlgebra.legacy.encode

  mellinAt:
    SourceEvaluationData.mellinAt on normalizedCC20ConcreteEvaluationData

  starConvolution:
    SourceConcreteBaseLayer.concreteTestAlgebra.convolutionSquare

  weilLocalSum:
    - SourceEvaluationData.polePairing on normalizedCC20ConcreteEvaluationData

  compactSupportSmooth:
    HasCompactSupport of the encoded route test

Build:
  WSL ext4 mirror:
    lake build ConnesWeilRH.Source.CC20ConcreteTestSpace
      ConnesWeilRH.Source.CC20Concrete
  Result:
    passed

Focused axiom audit:
  normalizedCC20ConcreteCarrierData
  normalizedCC20MellinCompactData
  normalizedCC20WeilOperationData
  normalizedCC20TestSpace
  normalizedCC20TestSpace_toRouteTest_eq
  normalizedCC20TestSpace_mellinAt_eq
  normalizedCC20TestSpace_starConvolution_eq
  normalizedCC20TestSpace_weilLocalSum_eq
  normalizedCC20TestSpace_compactSupportSmooth_eq

  Output for every target:
    [propext, Classical.choice, Quot.sound]

Remaining Plan 05 dependency:
  05C must prove detector existence for normalizedCC20TestSpace.
  05D must prove the route realization bridge for this exact owner.
  05E must consume those lower facts in the Dev root.
```


## 1. Result First

Hard completion gate:

```text
Good:
  This is shard-good only.  It is not Plan 05 Good and does not close
  `normalizedCoreCC20RHExitObjectPackageFromTheorems` until 05C, 05D, and 05E
  consume the owner.

  A concrete owner supplies:

    Source.normalizedCC20TestSpace : Source.CC20TestSpace

  or a more specific source-level owner with the same payload.

  The owner defines the actual test type, route-test projection, Mellin
  evaluation, star convolution, Weil local sum, and compact-smooth predicate
  from lower project/Mathlib objects.

Partial:
  The shard only keeps abstract `CC20TestSpace` definitions.  This is useful
  infrastructure but not a concrete owner.

Rejected:
  `Test := Empty`, `Test := Unit` with dummy operations, `weilLocalSum := 0`,
  `mellinAt := 0`, `compactSupportSmooth := True`, or any fake owner whose
  operations are not tied to the CC20 route objects.

  The abstract `CC20TestSpace` interface by itself is not accepted as the owner.
  The gate must build and audit the concrete module that supplies
  `normalizedCC20TestSpace`.
```


## 2. File Ownership

Allowed files:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
ConnesWeilRH/Source/CC20Concrete.lean
```

Do not edit:

```text
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
ConnesWeilRH/Source/CC20PropositionC1.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Route/*.lean
```

If a root import list needs updating, leave that to the coordinator.


## 3. Old Weak Path

The current infrastructure has only an abstract record:

```text
CC20TestSpace
```

An arbitrary `C : CC20TestSpace` cannot support detector existence.  For
example, `C.Test = Empty` makes `Nonempty (YoshidaDetector C F rho)` false.


## 4. Execution Tree

The 05B work is accepted only if the concrete owner survives all six field
provenance checks.  The plan should not start by filling a record.  It should
first identify the lower object behind each field, then assemble the owner.

```text
05B concrete CC20 test-space owner
|
+-- 05B1 carrier and route projection
|   |
|   +-- define the concrete test carrier
|   +-- prove it is not Empty or Unit-by-dummy
|   +-- connect it to TestFunction through a real projection
|   +-- expected output:
|       normalizedCC20TestCarrierData or equivalent
|
+-- 05B2 Mellin evaluation and compact-smooth predicate
|   |
|   +-- define mellinAt from lower Mellin/source evaluation data
|   +-- define compactSupportSmooth from a real predicate
|   +-- reject mellinAt := 0 and compactSupportSmooth := True
|   +-- expected output:
|       normalizedCC20MellinCompactData or equivalent
|
+-- 05B3 convolution and Weil local sum
|   |
|   +-- connect starConvolution to the source/Weil convolution object
|   +-- connect weilLocalSum to the CC20 local Weil sum
|   +-- reject constant zero local sums and identity-like convolution aliases
|   +-- expected output:
|       normalizedCC20WeilOperationData or equivalent
|
+-- 05B4 owner assembly and downstream contract
    |
    +-- assemble Source.normalizedCC20TestSpace
    +-- prove field projection lemmas used by 05C and 05D
    +-- run the concrete module build and focused axiom audit
    +-- expected output:
        Source.normalizedCC20TestSpace : Source.CC20TestSpace
```

The split is deliberately field-based.  A fake owner can elaborate if the
record fields have the right types, so the acceptance gate must inspect field
provenance before it inspects route consumers.

Subplans:

```text
05B1:
  plan/05B1_2026-07-07_D1_cc20_test_carrier_projection_plan.md

05B2:
  plan/05B2_2026-07-07_D1_cc20_mellin_compact_predicate_plan.md

05B3:
  plan/05B3_2026-07-07_D1_cc20_convolution_weil_sum_plan.md

05B4:
  plan/05B4_2026-07-07_D1_cc20_owner_assembly_contract_plan.md
```


## 5. Implementation Route

Define a concrete owner that makes these fields non-dummy:

```lean
structure CC20TestSpace where
  Test : Type
  toRouteTest : Test -> TestFunction
  mellinAt : Test -> ℂ -> ℂ
  starConvolution : Test -> Test
  weilLocalSum : Test -> ℝ
  compactSupportSmooth : Test -> Prop
```

The owner must document the lower source for each field:

```text
Test:
  <real CC20 test object>

toRouteTest:
  <transport into TestFunction>

mellinAt:
  <Mellin evaluation>

starConvolution:
  <CC20 star convolution>

weilLocalSum:
  <local Weil sum>

compactSupportSmooth:
  <actual compact smooth predicate>
```

Do not build 05B by proving detector existence.  Detector existence belongs to
05C.  The 05B output is the concrete `CC20TestSpace` object and enough
projection lemmas for 05C and 05D to consume it without importing dummy rows.


## 6. Rejection Scans

```text
rg -n "Test := Empty|Test := Unit|mellinAt := fun .*=> 0|weilLocalSum := fun .*=> 0|compactSupportSmooth := fun .*=> True|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Source/CC20TestSpace.lean ConnesWeilRH/Source/CC20ConcreteTestSpace.lean ConnesWeilRH/Source/CC20Concrete.lean
```


## 7. WSL Build Gate

Use the main WSL ext4 mirror.  Do not run `lake` from `/mnt/c`.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20TestSpace ConnesWeilRH.Source.CC20Concrete'
```

If `ConnesWeilRH/Source/CC20ConcreteTestSpace.lean` is created, the accepted
gate is:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20ConcreteTestSpace ConnesWeilRH.Source.CC20Concrete'
```

Building only `ConnesWeilRH.Source.CC20TestSpace` is not enough, because that
checks the abstract interface but not the concrete owner.


## 8. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20ConcreteTestSpace

#check ConnesWeilRH.Source.normalizedCC20TestSpace
#print axioms ConnesWeilRH.Source.normalizedCC20TestSpace
```


## 9. Acceptance Text

```text
Result:
  Good / partial / rejected.

Shard scope:
  Good here means 05B shard-good only.  Plan 05 remains partial until the
  detector, C.1, and Dev integration shards consume this owner.

New concrete owner:
  <exact declaration>

Field provenance:
  Test:
  toRouteTest:
  mellinAt:
  starConvolution:
  weilLocalSum:
  compactSupportSmooth:

Build:
  <command and result>

Remaining Plan 05 dependency:
  Yoshida detector existence and C.1 source criterion remain outside this shard.
```
