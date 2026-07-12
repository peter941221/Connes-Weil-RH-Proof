# 05D D1 CC20 Proposition C.1 Route Realization Plan

Date: 2026-07-07

Status: parallel execution shard for Plan 05.  This shard connects route
positivity/triple-vanishing inputs to the concrete CC20 predicates and proves
the source criterion from 05B and 05C.

Execution correction, 2026-07-07:
  The original naked target

  ```text
  ∀ input : Source.WeilPositivityInput,
    Source.CC20PropositionC1InputData standard F input ->
      standard.SourceRH
  ```

  is too strong for the current API unless a realization provider is also
  supplied for every input.  `WeilPositivityInput` stores only:

  ```text
  tripleVanishing : Prop
  fullWeilPositivity : Sort 1
  ```

  so the bare `input.fullWeilPositivity` field does not imply the concrete
  predicate:

  ```text
  Source.CC20FiniteVanishingWeilCriterion
    Source.normalizedCC20TestSpace
    Source.cc20TripleFiniteVanishingSet
  ```

  05D therefore closes its own shard by proving the load-bearing bridge for a
  selected explicit CC20 finite-vanishing input, and by exposing the source
  theorem that converts any realized input into `standard.SourceRH`.
  05E / Plan 06 must consume the selected theorem or provide a stronger
  all-input realization provider.  Do not fill the gap by reading
  `sourceCC20PropositionC1` or a stored `SourceRH`.


## 1. Result First

Hard completion gate:

```text
Good:
  This is shard-good only.  It is not Plan 05 Good and does not close
  `normalizedCoreCC20RHExitObjectPackageFromTheorems` until 05E consumes the C.1
  theorem in the Dev root.

  05D route-realization-good means these audited declarations exist:

    Source.cc20_proposition_c1_standard_source_rh_of_realized_input

    Source.cc20_proposition_c1_standard_source_rh_of_realized_cc20_triple_input

    Route.normalizedCC20FiniteVanishingWeilCriterionInput

    Route.normalizedCC20RouteInputRealizesFiniteVanishingCriterion

    Route.normalizedCC20_source_rh_of_realized_finite_vanishing_input

    Route.normalizedCC20_source_rh_of_finite_vanishing_rows

  The proof uses:
    concrete CC20 test-space owner from 05B;
    detector existence as an explicit 05C input;
    route realization from the selected finite-vanishing input.

Partial:
  The shard only proves the old conditional theorem
  `cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors`, or
  proves a selected theorem but does not expose/audit the route realization
  declaration itself.

Rejected:
  The theorem reads SourceRH or Mathlib RH from a stored field, calls
  `mathlib_rh_to_source_rh`, ignores the input data, or imports C.1 as an
  accepted-source theorem.

  A route realization theorem that is not itself audited is rejected, even if
  the final source criterion theorem elaborates.  The route realization bridge
  is the load-bearing statement for this shard.
```


## 2. File Ownership

Allowed files:

```text
ConnesWeilRH/Source/CC20PropositionC1.lean
ConnesWeilRH/Route/CC20RouteRealization.lean
```

Read-only dependencies:

```text
ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
ConnesWeilRH/Source/CC20YoshidaConstruction.lean
ConnesWeilRH/Route/Bridge.lean
ConnesWeilRH/Route/Exhaustion.lean
```

Do not edit:

```text
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
ConnesWeilRH/Source/CC20TestSpace.lean
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Source/CC20RHExit.lean
```


## 3. Old Weak Path

Current route data reaches:

```text
WeilPositivityInput
  input.tripleVanishing
  input.fullWeilPositivity
```

The old weak path stores the final `sourceCC20PropositionC1` as a field on the
source object package.  That is not an acceptable producer for the core 05
root.

Current overstrong path rejected:

```text
arbitrary input : WeilPositivityInput
|
+-- input.tripleVanishing : Prop
|
+-- input.fullWeilPositivity : Sort 1
|
+-- missing bridge:
|     input.fullWeilPositivity
|       -> CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace F
|
+-- impossible to prove without an additional realization provider
```

Correct 05D selected route path:

```text
normalizedCC20FiniteVanishingWeilCriterionInput
|
+-- tripleVanishing :=
|     forall g,
|       normalizedCC20TestSpace.compactSupportSmooth g ->
|       CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g
|
+-- fullWeilPositivity :=
|     PLift
|       (CC20FiniteVanishingWeilCriterion
|         normalizedCC20TestSpace
|         cc20TripleFiniteVanishingSet)
|
+-- normalizedCC20RouteInputRealizesFiniteVanishingCriterion
      |
      +-- routeInputIsCC20Criterion:
      |     fullWeilPositivity.down is the finite-vanishing criterion
      |
      +-- routeTripleVanishingIsMellinVanishing:
            tripleVanishing is definitionally the CC20 vanishing family
```


## 4. Implementation Route

Build:

```lean
noncomputable def normalizedCC20FiniteVanishingWeilCriterionInput :
    WeilPositivityInput

theorem normalizedCC20RouteInputRealizesFiniteVanishingCriterion :
    CC20RouteInputRealizesFiniteVanishingCriterion
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet
      normalizedCC20FiniteVanishingWeilCriterionInput
```

Then prove:

```lean
theorem cc20_proposition_c1_standard_source_rh_of_realized_input
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (hfinite : SourceFiniteSetAdmissibility F)
    (hexists : CC20YoshidaDetectorExists C F)
    {input : WeilPositivityInput}
    (hrealize :
      CC20RouteInputRealizesFiniteVanishingCriterion C F input)
    (hdata :
      CC20PropositionC1InputData RHDefinitionBridge.standard F input) :
    RHDefinitionBridge.standard.SourceRH

theorem normalizedCC20_source_rh_of_finite_vanishing_rows
    (hexists :
      CC20YoshidaDetectorExists
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet)
    (hdisjoint :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard cc20TripleFiniteVanishingSet)
    (hvanish :
      normalizedCC20FiniteVanishingWeilCriterionInput.tripleVanishing)
    (hcriterion :
      normalizedCC20FiniteVanishingWeilCriterionInput.fullWeilPositivity) :
    RHDefinitionBridge.standard.SourceRH
```

The proof should call:

```text
cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors
```

or the lower single-input theorem with the concrete owner from 05B and detector
existence from 05C.  The detector theorem itself remains 05C's owner.

Tree 1: source theorem.

```text
cc20_proposition_c1_standard_source_rh_of_realized_input
|
+-- inputs
|   |
|   +-- C : CC20TestSpace
|   +-- F : Finset CriticalVanishingPoint
|   +-- hfinite : SourceFiniteSetAdmissibility F
|   +-- hexists : CC20YoshidaDetectorExists C F
|   +-- hrealize : CC20RouteInputRealizesFiniteVanishingCriterion C F input
|   +-- hdata : CC20PropositionC1InputData standard F input
|
+-- derives
|   |
|   +-- hcriterion :=
|   |     hrealize.routeInputIsCC20Criterion hdata.fullWeilPositivity
|   |
|   +-- cc20_proposition_c1_from_yoshida_detector
|
+-- output
    |
    +-- RHDefinitionBridge.standard.SourceRH
```

Tree 2: route selected input.

```text
normalizedCC20FiniteVanishingWeilCriterionInput
|
+-- explicit triple row
|   |
|   +-- forall normalized test g
|       |
|       +-- compactSupportSmooth g
|       +-- CC20VanishesOn normalizedCC20TestSpace F g
|
+-- explicit positivity row
    |
    +-- PLift (CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace F)
```

Tree 3: route selected C.1 output.

```text
normalizedCC20_source_rh_of_finite_vanishing_rows
|
+-- 05C input:
|     normalizedCC20YoshidaDetectorExists
|
+-- 05A input:
|     SourceFiniteSetDisjointFromNontrivialZeros standard cc20Triple
|
+-- selected rows:
|     hvanish, hcriterion
|
+-- cc20_proposition_c1_input_data
|
+-- normalizedCC20_source_rh_of_realized_finite_vanishing_input
|
+-- standard.SourceRH
```

Do not introduce a Source/Route import cycle.  If the concrete route
realization must live under `ConnesWeilRH.Route`, keep the source-side theorem
parameterized where necessary and put the route-facing instantiation in
`ConnesWeilRH/Route/CC20RouteRealization.lean`.  The acceptance gate must audit
the route-facing theorem that is actually consumed by the Dev integration.


## 5. Rejection Scans

```text
rg -n "mathlib_rh_to_source_rh|source_rh_to_mathlib_rh|SourceRH\s*:=|RiemannHypothesis\s*:=|sourceCC20PropositionC1|accepted|C1Accepted|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b|Set\.univ|\bTrue\b" ConnesWeilRH/Source/CC20PropositionC1.lean ConnesWeilRH/Route/CC20RouteRealization.lean
```


## 6. WSL Build Gate

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CC20PropositionC1 ConnesWeilRH.Route.CC20RouteRealization'
```


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CC20PropositionC1
import ConnesWeilRH.Route.CC20RouteRealization

#check ConnesWeilRH.Route.normalizedCC20RouteInputRealizesFiniteVanishingCriterion
#print axioms ConnesWeilRH.Route.normalizedCC20RouteInputRealizesFiniteVanishingCriterion

#check ConnesWeilRH.Source.cc20_proposition_c1_standard_source_rh_of_realized_input
#print axioms ConnesWeilRH.Source.cc20_proposition_c1_standard_source_rh_of_realized_input

#check ConnesWeilRH.Route.normalizedCC20_source_rh_of_realized_finite_vanishing_input
#print axioms ConnesWeilRH.Route.normalizedCC20_source_rh_of_realized_finite_vanishing_input

#check ConnesWeilRH.Route.normalizedCC20_source_rh_of_finite_vanishing_rows
#print axioms ConnesWeilRH.Route.normalizedCC20_source_rh_of_finite_vanishing_rows
```

If the final C.1 instantiation lives in the Route namespace to avoid an import
cycle, audit that exact route-facing theorem instead of the source theorem, and
05E must name that route-facing theorem as the lower source criterion it
consumes.


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Shard scope:
  Good here means 05D shard-good only.  Plan 05 remains partial until 05E wires
  this criterion into `normalizedCoreCC20RHExitObjectPackageFromTheorems`.

Route realization theorem:
  <exact declaration>

Source C.1 theorem:
  <exact declaration>

Build:
  <command and result>

Focused axiom audit:
  <output>

Remaining Plan 05 dependency:
  Dev/root package integration remains outside this shard.
```
