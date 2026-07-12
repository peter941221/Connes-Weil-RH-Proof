# 05B3 D1 CC20 Convolution And Weil Sum Plan

Date: 2026-07-07

Status: planning shard under 05B.  This shard supplies the star-convolution and
local Weil-sum fields for the concrete CC20 test-space owner.


## 1. Result First

Hard completion gate:

```text
Good:
  The concrete owner supplies:

    starConvolution : Test -> Test
    weilLocalSum : Test -> ℝ

  starConvolution comes from the source/Weil convolution object.  weilLocalSum
  comes from the CC20 local Weil sum or a named lower source expression.

Partial:
  The shard identifies the exact missing local-Weil-sum API and reports it as
  the first non-Mathlib black box.

Rejected:
  starConvolution := id.
  starConvolution ignores its input.
  weilLocalSum := fun _ => 0.
  Weil positivity or C.1 is smuggled into a raw Prop field.
```


## 2. Evidence

Current interface:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
  starConvolution : Test -> Test
  weilLocalSum : Test -> ℝ

ConnesWeilRH/Source/CC20TestSpace.lean
  CC20WeilNonpositive C g :=
    C.weilLocalSum (C.starConvolution g) <= 0
```

Existing lower source objects to inspect first:

```text
ConnesWeilRH/Basic.lean
  structure WeilFormSymbols where
    convolutionStar : TestFunction -> TestFunction -> TestFunction

ConnesWeilRH/Source/AnalyticCoreBase.lean
  structure SourceTestAlgebra where
    convolutionStar : Test -> Test -> Test
    convolutionSquare : Test -> Test

ConnesWeilRH/Source/Objects.lean
  sourceCC20WeilNonpositivity and sourceCC20PropositionC1 fields exist, but
  they are rejected as direct producers for 05B if they only store C.1 rows.
```


## 3. Dependency Tree

```text
05B3 convolution/Weil data
|
+-- starConvolution
|   |
|   +-- if carrier is TestFunction:
|   |     use WeilFormSymbols.convolutionStar or a concrete SourceTestAlgebra
|   |
|   +-- if carrier is SourceTestAlgebra.Test:
|         use A.convolutionSquare or A.convolutionStar g g
|
+-- weilLocalSum
|   |
|   +-- preferred:
|   |     named CC20 local Weil sum expression
|   |
|   +-- fallback:
|         report missing local-Weil-sum API as black box
|
+-- downstream use
    |
    +-- 05C:
    |     off-line detector sign needs 0 < weilLocalSum (starConvolution test)
    |
    +-- 05D:
          fullWeilPositivity must imply CC20FiniteVanishingWeilCriterion
```


## 4. Implementation Route

Preferred owner shape:

```lean
structure CC20WeilOperationData
    (Carrier : Type) where
  starConvolution : Carrier -> Carrier
  weilLocalSum : Carrier -> ℝ
```

The implementation must also expose projection lemmas with names stable enough
for 05C and 05D:

```text
normalizedCC20_starConvolution_eq
normalizedCC20_weilLocalSum_eq
```

If the current route only has `input.fullWeilPositivity : Sort 1`, do not use it
as the definition of `weilLocalSum`.  That proposition belongs to 05D's route
realization bridge, not 05B's owner construction.


## 5. Rejection Scans

```text
rg -n "starConvolution := id|starConvolution := fun _ =>|weilLocalSum := fun .*=> 0|fullWeilPositivity.*weilLocalSum|sourceCC20PropositionC1|C1Accepted|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Source/CC20ConcreteTestSpace.lean ConnesWeilRH/Source/CC20Concrete.lean
```


## 6. WSL Build Gate

Use the main WSL ext4 mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20ConcreteTestSpace'
```


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20ConcreteTestSpace

#check ConnesWeilRH.Source.normalizedCC20WeilOperationData
#print axioms ConnesWeilRH.Source.normalizedCC20WeilOperationData
```


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Convolution field:
  <exact declaration and lower source>

Weil local sum field:
  <exact declaration and lower source>

First black box, if any:
  <exact declaration/type>

Remaining 05B dependency:
  final owner assembly and downstream projection checks.
```
