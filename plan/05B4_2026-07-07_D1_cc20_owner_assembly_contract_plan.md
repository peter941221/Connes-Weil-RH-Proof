# 05B4 D1 CC20 Owner Assembly And Downstream Contract Plan

Date: 2026-07-07

Status: planning shard under 05B.  This shard assembles the concrete
`Source.CC20TestSpace` owner from 05B1, 05B2, and 05B3.


## 1. Result First

Hard completion gate:

```text
Good:
  The concrete owner exists:

    Source.normalizedCC20TestSpace : Source.CC20TestSpace

  Each field projects from the accepted 05B1, 05B2, and 05B3 data.  05C and 05D
  can import the concrete owner without creating a Source/Route import cycle.

Partial:
  The record elaborates but one field still points at a missing lower API or a
  black-box report.

Rejected:
  The owner is built from dummy fields.
  The owner stores detector existence.
  The owner stores Proposition C.1 or SourceRH.
  The owner imports Route files and creates a source/route cycle.
```


## 2. Evidence

05C consumes:

```text
Source.normalizedCC20TestSpace
Source.CC20YoshidaDetectorExists
  Source.normalizedCC20TestSpace
  Source.cc20TripleFiniteVanishingSet
```

05D consumes:

```text
CC20RouteInputRealizesFiniteVanishingCriterion
  normalizedCC20TestSpace
  cc20TripleFiniteVanishingSet
  input
```

Current source theorem stack:

```text
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
  cc20_proposition_c1_from_yoshida_detector

ConnesWeilRH/Source/CC20PropositionC1.lean
  cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors
```

Those theorems are conditional infrastructure.  05B4 must not turn them into
fields on the owner.


## 3. Assembly Tree

```text
05B4 final owner
|
+-- inputs
|   |
|   +-- 05B1:
|   |     carrier and toRouteTest
|   |
|   +-- 05B2:
|   |     mellinAt and compactSupportSmooth
|   |
|   +-- 05B3:
|         starConvolution and weilLocalSum
|
+-- output
|   |
|   +-- Source.normalizedCC20TestSpace
|   |
|   +-- projection lemmas:
|         normalizedCC20TestSpace_toRouteTest_eq
|         normalizedCC20TestSpace_mellinAt_eq
|         normalizedCC20TestSpace_starConvolution_eq
|         normalizedCC20TestSpace_weilLocalSum_eq
|         normalizedCC20TestSpace_compactSupportSmooth_eq
|
+-- consumers
    |
    +-- 05C imports the owner and proves detector existence
    +-- 05D imports the owner and proves route realization
```


## 4. Implementation Route

Implementation shape:

```lean
noncomputable def normalizedCC20TestSpace : CC20TestSpace where
  Test := <05B1 carrier>
  toRouteTest := <05B1 projection>
  mellinAt := <05B2 Mellin>
  starConvolution := <05B3 convolution>
  weilLocalSum := <05B3 local sum>
  compactSupportSmooth := <05B2 predicate>
```

Projection lemmas should be `rfl` or short definitional equalities when the
field is assembled directly from the accepted data.  They must not prove new
mathematics.  New mathematical content belongs in the producing shards.


## 5. Rejection Scans

```text
rg -n "YoshidaDetectorExists|YoshidaDetector|PropositionC1|SourceRH|RiemannHypothesis|mathlib_rh|Route\\.|Test := Empty|Test := Unit|mellinAt := fun .*=> 0|weilLocalSum := fun .*=> 0|compactSupportSmooth := fun .*=> True|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Source/CC20ConcreteTestSpace.lean ConnesWeilRH/Source/CC20Concrete.lean
```


## 6. WSL Build Gate

Use the main WSL ext4 mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20ConcreteTestSpace ConnesWeilRH.Source.CC20Concrete'
```


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20ConcreteTestSpace

#check ConnesWeilRH.Source.normalizedCC20TestSpace
#print axioms ConnesWeilRH.Source.normalizedCC20TestSpace

#check ConnesWeilRH.Source.normalizedCC20TestSpace_toRouteTest_eq
#print axioms ConnesWeilRH.Source.normalizedCC20TestSpace_toRouteTest_eq

#check ConnesWeilRH.Source.normalizedCC20TestSpace_mellinAt_eq
#print axioms ConnesWeilRH.Source.normalizedCC20TestSpace_mellinAt_eq

#check ConnesWeilRH.Source.normalizedCC20TestSpace_weilLocalSum_eq
#print axioms ConnesWeilRH.Source.normalizedCC20TestSpace_weilLocalSum_eq
```


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Concrete owner:
  Source.normalizedCC20TestSpace

Field provenance:
  Test:
  toRouteTest:
  mellinAt:
  starConvolution:
  weilLocalSum:
  compactSupportSmooth:

Downstream contract:
  05C can import the owner without route imports.
  05D can reference the owner in route realization.

Build:
  <command and result>

Focused axiom audit:
  <output>
```
