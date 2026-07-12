# 05B1 D1 CC20 Test Carrier And Route Projection Plan

Date: 2026-07-07

Status: planning shard under 05B.  This shard does not prove detector existence
and does not close Plan 05.


## 1. Result First

Hard completion gate:

```text
Good:
  A concrete source-level carrier is named and connected to TestFunction through
  a real projection:

    <owner>.Test
    <owner>.toRouteTest : <owner>.Test -> TestFunction

  The carrier and projection are the exact fields used later by
  Source.normalizedCC20TestSpace.

Partial:
  The plan only points at TestFunction as a possible carrier but does not name
  the owner module or the projection theorem.

Rejected:
  Test := Empty.
  Test := Unit with dummy operations.
  toRouteTest ignores the source test.
  The carrier is a same-object alias introduced only to satisfy the record.
```


## 2. Evidence

Current interface:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
  structure CC20TestSpace where
    Test : Type
    toRouteTest : Test -> TestFunction
```

Current lower project boundary:

```text
ConnesWeilRH/Basic.lean
  abbrev TestFunction := SchwartzMap ℝ ℂ

ConnesWeilRH/Source/AnalyticCoreBase.lean
  structure LegacyTestEquiv
  structure SourceTestAlgebra
  namespace SourceConcreteBaseLayer
    abbrev ConcreteTest : Type := TestFunction
```

The likely first carrier is therefore either `TestFunction` itself, or the
`SourceConcreteBaseLayer.ConcreteTest` alias if the implementation wants to
route through `SourceTestAlgebra`.


## 3. Dependency Tree

```text
05B1 carrier/projection
|
+-- locate concrete carrier
|   |
|   +-- candidate A:
|   |     TestFunction
|   |
|   +-- candidate B:
|         SourceConcreteBaseLayer.ConcreteTest
|
+-- locate projection
|   |
|   +-- if carrier is TestFunction:
|   |     toRouteTest := id
|   |
|   +-- if carrier is SourceTestAlgebra.Test:
|         toRouteTest := A.legacy.encode
|
+-- prove downstream shape
    |
    +-- C.Test is inhabited by real route tests only if later 05C supplies one
    +-- 05B must not fake detector existence through Nonempty
    +-- 05D may use toRouteTest to connect route positivity to CC20 predicates
```


## 4. Implementation Route

Preferred implementation shape:

```lean
structure CC20ConcreteCarrierData where
  Test : Type
  toRouteTest : Test -> TestFunction
  carrierSource : Prop
```

The `carrierSource` field may document the chosen lower source only if it does
not restate a target theorem.  If the selected carrier is `TestFunction`, prefer
a theorem explaining the choice over a raw `Prop` field.

Expected owner names:

```text
ConnesWeilRH.Source.normalizedCC20ConcreteCarrierData
ConnesWeilRH.Source.normalizedCC20Concrete_toRouteTest
```


## 5. Rejection Scans

```text
rg -n "Test := Empty|Test := Unit|toRouteTest := fun _|carrierSource : Prop|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Source/CC20ConcreteTestSpace.lean ConnesWeilRH/Source/CC20Concrete.lean
```


## 6. WSL Build Gate

Use the main WSL ext4 mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20ConcreteTestSpace'
```


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20ConcreteTestSpace

#check ConnesWeilRH.Source.normalizedCC20ConcreteCarrierData
#print axioms ConnesWeilRH.Source.normalizedCC20ConcreteCarrierData
```


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Carrier:
  <exact declaration>

Projection:
  <exact declaration>

Why it is not a dummy owner:
  <short evidence>

Remaining 05B dependency:
  Mellin, compact-smooth, convolution, Weil local sum, and final owner assembly.
```
