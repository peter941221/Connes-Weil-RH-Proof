# D1 04A Selected Restricted Evaluator Lane

Date: 2026-07-07

Status: partial-good, rejected as solved.  This is the only 04A tree document.
Keep all future 04A splits, evidence, and handoff notes in this file.


## 1. Result First

04A is not closed.

Good result from this pass:

```text
lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed after removing an invalid forward/self-reference proof attempt
```

Bad result that remains:

```text
normalizedSelectedQWLambdaScalarIdentificationFromTheorems
  -> normalizedCoreS2B1ActualScalarIdentificationFromTheorems
      -> sorryAx
```

Current focused audit:

```text
normalizedSelectedQWLambdaScalarIdentificationFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedCoreS2B1ActualScalarIdentificationFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedTraceReadOffEqualityRowsFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]

normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
  [propext, sorryAx, Classical.choice, Quot.sound]
```


## 2. Hard Completion Gate

04A is solved only when all of these hold:

```text
1. The active selected chain proves:

     normalizedSeedFromTheorems.traceAmplitude(sourceTraceTest)^2
       =
     selected restricted evaluator

   for the active tuple:

     normalizedSeedFromTheorems
     normalizedRemaindersFromTheorems
     normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
     normalizedSourceBackedFixedSTestFromTheorems.weilTest
     normalizedTraceLambdaInputFromTheorems.lambda
     normalizedTraceCCM25ArithmeticPackageFromTheorems

2. The proof does not call:

     normalizedCoreS2B1ActualScalarIdentificationFromTheorems
     normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
     normalizedActualScalarIdentificationFromTheoremBasePackage
     Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
     Source.normalizedSeedMatchedRestrictedEvaluatorScalarIdentification
     normalizedTraceReadOffEqualityRowsFromTheorems
     normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
     restricted_trace_read_off_of_source_trace_data

3. WSL build passes:

     lake build ConnesWeilRH.Dev.UnconditionalSkeleton

4. Focused axiom audit for the 04A targets returns only:

     [propext, Classical.choice, Quot.sound]
```


## 3. Current Bad Tree

The active path is:

```text
04A active path
|
+-- normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
    |
    +-- normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
        |
        +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
            |
            +-- Source.normalizedSeedSupportSquareCC20ReadOffData
            |
            +-- normalizedSelectedQWLambdaScalarIdentificationFromTheorems
            |   |
            |   +-- normalizedCoreS2B1ActualScalarIdentificationFromTheorems
            |       |
            |       +-- sorryAx
            |
            +-- Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
                |
                +-- clean formula bridge:
                    selected QW_lambda = selected restricted evaluator
```

Meaning:

```text
Move 2 is clean:
  selected QW_lambda = selected restricted evaluator

Move 1 is still missing:
  active traceAmplitude(sourceTraceTest)^2 = selected QW_lambda
```


## 4. Rejected Trees

Do not close 04A through the old fixed-tuple row:

```text
old fixed-tuple row
|
+-- normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
    |
    +-- normalizedBaseFromTheorems.s2b1NormalizedSeedSupportSquareQWLambdaRow
```

Do not close 04A through theorem-base scalar readback:

```text
theorem-base scalar readback
|
+-- normalizedActualScalarIdentificationFromTheoremBasePackage
    |
    +-- Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
```

Do not close 04A by switching the seed:

```text
matched/scalar seed replacement
|
+-- Source.normalizedSeedMatchedRestrictedEvaluatorScalarIdentification
|   |
|   +-- proves the identity for normalizedSeedMatchedToCCM25Evaluator
|
+-- TraceFrontEnd.normalizedRestrictedScalarTraceSeed
+-- Source.normalizedScalarAsLegalSquareSeed
|
+-- rejected:
    these construct a new seed instead of proving the active
    normalizedSeedFromTheorems identity.
```

Do not close 04A through TraceData readback:

```text
circular TraceData route
|
+-- normalizedTraceDataFromTheorems
    |
    +-- SourceTraceReadOffData
        |
        +-- restricted_trace_read_off_of_source_trace_data
```

Do not close 04A through source trace read-off rows:

```text
raw read-off row route
|
+-- normalizedTraceReadOffEqualityRowsFromTheorems
|   |
|   +-- normalizedSourceObjectTheoremBaseInputFromTheorems
|
+-- normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
    |
    +-- sorryAx
```

Why rejected:

```text
NormalizedSourceTraceReadOffEqualityRows stores:

  cc20Trace.supportSquareTrace sourceTraceTest
    =
  base.ccm25Model.toWeilFormSymbols.qwLambda lambda commonTest commonTest

as a row.  It is the target equality, not a lower proof of the target.
```

Do not close 04A through selected trace read-off data:

```text
selected trace read-off route
|
+-- normalizedTraceSelectedReadOffDataFromTheorems
|   |
|   +-- Source.CC20SelectedTraceReadOffData.ofSupportSquareQWLambda
|       |
|       +-- normalizedTraceSelectedPositiveTraceEqSupportSquareFromTheorems
|       |   |
|       |   +-- clean selected legality + ordinary trace/support-square row
|       |
|       +-- normalizedTraceSelectedSupportSquareQWLambdaReadOffSourceDataFromTheorems
|           |
|           +-- normalizedTraceSupportSquareQWLambdaReadOffSourceDataFromTheorems
|               |
|               +-- normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
|                   |
|                   +-- normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
|                       |
|                       +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
|                           |
|                           +-- normalizedSelectedQWLambdaScalarIdentificationFromTheorems
|                               |
|                               +-- normalizedCoreS2B1ActualScalarIdentificationFromTheorems
|                                   |
|                                   +-- sorryAx
```

Why rejected:

```text
CC20SelectedTraceReadOffData.positiveTrace_eq_qwLambda is clean only after
supportSquare_qwLambda is already supplied.  In the current Dev chain that
supportSquare_qwLambda input is exactly the 04A row, so this is downstream
of 04A, not a replacement for it.

Current focused audit for normalizedTraceSelectedReadOffDataFromTheorems and
normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems still returns:

  [propext, sorryAx, Classical.choice, Quot.sound]
```

Do not close 04A through source-trace support-square read-off parts:

```text
source-trace parts route
|
+-- normalizedTraceSupportSquareQWLambdaReadOffFromParts
    |
    +-- TraceFrontEndData.source_trace_support_square_qw_lambda_read_off_of_parts
        |
        +-- restricted_trace_read_off_of_source_trace_data
            |
            +-- reads RestrictedTraceReadOffEquality from SourceTraceReadOffData
```

Why rejected:

```text
TraceFrontEndData.source_trace_support_square_qw_lambda_read_off_of_parts
proves supportSquare = QW_lambda by reading
restricted_trace_read_off_of_source_trace_data.  That is a TraceData readback
loop for 04A.

Current focused audit for normalizedTraceSupportSquareQWLambdaReadOffFromParts
still returns:

  [propext, sorryAx, Classical.choice, Quot.sound]
```

Do not close 04A by self-bootstrapping the core root:

```text
invalid self-bootstrap
|
+-- normalizedCoreS2B1ActualScalarIdentificationFromTheorems
|   |
|   +-- tries to use normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
|       before that theorem is declared
|
+-- normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
    |
    +-- uses normalizedCoreS2B1ActualScalarIdentificationFromTheorems

build result:
  Unknown identifier normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
```


## 5. Correct Next Tree

The next real 04A cut is a selected same-test scalar owner.  The first missing
theorem/API is:

```text
normalizedSeedFromTheorems.traceAmplitude(sourceTraceTest)^2
  =
(RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
  .ccm25.weilSymbols.qwLambda
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedSourceBackedFixedSTestFromTheorems.weilTest
    normalizedSourceBackedFixedSTestFromTheorems.weilTest
```

Equivalently, Lean needs this owner without using the rejected routes above:

```text
selected same-test scalar owner
|
+-- input tuple:
|   |
|   +-- seed:
|   |     normalizedSeedFromTheorems
|   |
|   +-- remainders:
|   |     normalizedRemaindersFromTheorems
|   |
|   +-- selected trace test:
|   |     normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
|   |
|   +-- selected fixed S-test:
|   |     normalizedSourceBackedFixedSTestFromTheorems.weilTest
|   |
|   +-- selected lambda:
|   |     normalizedTraceLambdaInputFromTheorems.lambda
|
+-- output theorem:
    Source.NormalizedSeedQWLambdaScalarIdentification
      normalizedSeedFromTheorems
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedRemaindersFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceBackedFixedSTestFromTheorems.weilTest
```

Current status of this tree:

```text
not found in the current source tree.

Existing constructors either:
  - consume this scalar identity and build downstream rows, or
  - prove it for a different matched seed, or
  - read the old theorem-base support-square/QW_lambda row, or
  - read TraceData / restricted trace read-off rows.
```

Then 04A closes by reusing the clean formula bridge:

```text
selected QW-lambda identity
|
+-- Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
    |
    +-- selected QW_lambda = selected restricted evaluator
        |
        +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
            |
            +-- normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
                |
                +-- normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
```

2026-07-07 five-branch audit result:

```text
Result:
  Diagnostic-good only.  04A is not closed.

Batch size:
  5 branches checked before recording.

Branch 1. normalizedSeedFromTheorems producer chain
|
+-- evidence:
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1999
|       normalizedSeedInputDataFromTheorems
|
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2005
|       normalizedSeedFromTheorems := normalizedSeedInputDataFromTheorems.seed
|
+-- result:
      rejected as a 04A producer.

      The seed is copied from normalizedBaseFromTheorems.s2b1NormalizedSeed.
      The input data stores only the seed and an archimedean-symbol equality.
      It does not store or prove selected
        traceAmplitude(sourceTraceTest)^2 = QW_lambda.

Branch 2. normalizedSeedInputData / source-object input
|
+-- evidence:
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1503
|       normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems
|
|     ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2747
|       NormalizedSourceObjectCoreTheoremBaseConstructorInput
|
+-- result:
      rejected as a 04A producer.

      The constructor input packages the theorem-base package and finite-prime
      exact data.  It does not add the selected same-test scalar theorem.

Branch 3. package construction / expanded source package
|
+-- evidence:
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2338
|       normalizedSourceObjectPackageFromTheorems
|
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2548
|       normalizedSelectedQWLambdaScalarIdentificationFromTheorems
|
+-- result:
      rejected as a 04A producer.

      The selected proof currently reaches the core root:

        normalizedSelectedQWLambdaScalarIdentificationFromTheorems
          -> normalizedCoreS2B1ActualScalarIdentificationFromTheorems
          -> sorryAx

      Package construction preserves the selected objects, but it does not
      prove the missing scalar equality.

Branch 4. S2-B1 analytic-exclusion / fixed-tuple support-square route
|
+-- evidence:
|     ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2129
|       S2B1TraceScaleAnalyticExclusionConstructorInput
|
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1456
|       normalizedCoreS2B1TraceScaleAnalyticExclusionConstructorInputFromTheorems
|
+-- result:
      rejected as a 04A producer.

      Its support-square field is already:

        S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData

      In Dev this field is built from
        normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems,
      whose CC20 leg calls
        normalizedCoreS2B1ActualScalarIdentificationFromTheorems.

      This is the old fixed-tuple row path under a constructor-input name.

Branch 5. Source trace-scale / SourceWeilForm definitional route
|
+-- evidence:
|     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:126
|       normalizedCoreTraceAmplitudeFromTheorems g =
|         || normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0 ||
|
|     ConnesWeilRH/Source/AnalyticCore.lean:8007
|       SourceTraceScaleData stores traceAmplitude as data.
|
|     ConnesWeilRH/Source/AnalyticCore.lean:7742
|       SourceWeilFormData.qwLambda is the archimedean + pole - restricted
|       finite-prime formula.
|
+-- result:
      rejected as a definitional close.

      The active seed gives:

        traceAmplitude(g)^2
          =
        || legacy.encode g 0 ||^2

      The active Weil-form gives:

        W.qwLambda lambda f f
          =
        archimedeanTerm(convolutionStar f f)
          + poleFunctional(convolutionStar f f)
          - restricted finite-prime sum

      These are not definitionally the same object.  A real 04A close needs
      a semantic theorem connecting the selected trace amplitude square to the
      selected QW_lambda value.
```

After this batch, the exact first missing API is sharper:

```text
selected source-core scalar theorem
|
+-- inputs:
|     core trace scale:
|       normalizedCoreSourceTraceScaleDataFromTheorems
|
|     core Weil form:
|       normalizedCoreSourceWeilFormDataFromTheorems
|
|     selected test:
|       normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
|
|     selected fixed test:
|       normalizedSourceBackedFixedSTestFromTheorems.weilTest
|
|     selected lambda:
|       normalizedTraceLambdaInputFromTheorems.lambda
|
+-- required theorem:
      normalizedCoreTraceAmplitudeFromTheorems selectedTraceTest ^ 2
        =
      normalizedCoreSourceWeilFormDataFromTheorems.toWeilFormSymbols.qwLambda
        selectedLambda selectedWeilTest selectedWeilTest

+-- current status:
      not present in the current source tree.
      Do not replace it with a row provider, package wrapper, theorem-base
      readback, matched seed, TraceData readback, or raw Prop field.
```


## 6. Evidence Locations

Current source evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1026
  normalizedCoreS2B1ActualScalarIdentificationFromTheorems
  current first 04A sorryAx blocker

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2548
  normalizedSelectedQWLambdaScalarIdentificationFromTheorems
  currently calls the core scalar root

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2572
  normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems

ConnesWeilRH/Source/S2B1TraceScale.lean:665
  Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
  clean QW-lambda -> restricted evaluator formula bridge

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:2649
  NormalizedSourceTraceReadOffEqualityRows
  raw row owner for full/restricted trace read-off equalities

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1575
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
  still a sorryAx source, rejected as 04A closure

ConnesWeilRH/Route/Definitions.lean:388
  SourceBackedFixedSTest.ofExpandedSourcePackage
  shows selected weilTest is pkg.commonTest.sourceTest by rfl

ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:340
  NormalizedLegalSquareTraceScaleSymbols
  stores traceAmplitude as data.  Lean cannot prove
  traceAmplitude^2 = QW_lambda from the seed definition alone.

ConnesWeilRH/Route/TraceFrontEnd.lean:4396
  source_trace_support_square_qw_lambda_read_off_of_parts
  uses restricted_trace_read_off_of_source_trace_data, so it is rejected for
  04A closure.

ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:683
  CC20SelectedTraceReadOffData
  derives positiveTrace_eq_qwLambda only after supportSquare_qwLambda is
  already supplied.
```


## 7. Static Rejection Scans

Run before claiming progress:

```text
rg -n "normalizedSelectedQWLambdaScalarIdentificationFromTheorems|normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems|normalizedCoreS2B1ActualScalarIdentificationFromTheorems|normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems|normalizedTraceReadOffEqualityRowsFromTheorems|normalizedSourceObjectBridgeReadOffRowsInputFromTheorems|normalizedSeedMatchedRestrictedEvaluatorScalarIdentification|normalizedActualScalarIdentificationFromTheoremBasePackage|normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage|restricted_trace_read_off_of_source_trace_data" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route/TraceFrontEnd.lean
```

Accepted 04A producer scan:

```text
The body of normalizedSelectedQWLambdaScalarIdentificationFromTheorems has no
hit for:

  normalizedCoreS2B1ActualScalarIdentificationFromTheorems
  normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
  normalizedTraceReadOffEqualityRowsFromTheorems
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
  normalizedSeedMatchedRestrictedEvaluatorScalarIdentification
  normalizedActualScalarIdentificationFromTheoremBasePackage
  normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
  restricted_trace_read_off_of_source_trace_data
```


## 8. WSL Build Gate

Run from Windows PowerShell:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Dev.UnconditionalSkeleton'
```

Latest result:

```text
lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed

caveat:
  the build log still prints the existing Lean compiler panic backtrace around
  UnconditionalSkeleton line 3004, but Lake reports success.
```


## 9. Focused Axiom Audit

Use an import-based scratch file after the WSL build:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedQWLambdaScalarIdentificationFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreS2B1ActualScalarIdentificationFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceReadOffEqualityRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
```

Accepted output for solved 04A:

```text
[propext, Classical.choice, Quot.sound]
```

Current rejected output:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

Latest diagnostic audit also checked these downstream candidates:

```lean
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceSelectedReadOffDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceSupportSquareQWLambdaReadOffFromParts
```

Current rejected output for all three:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```


## 10. Handoff Text

Use this exact status shape:

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


## 11. Deep Drill Result, 2026-07-07

Result: bad for closure.  This pass drilled below the 04A record layer and did
not find a lower clean proof of the selected scalar identity.

The remaining leaf is not:

```text
NormalizedSeedRestrictedEvaluatorScalarIdentification
```

That record is only the package shape.  Its field is the real theorem:

```text
Source.normalizedSeedSupportSquareReadOffSourceScalar
  normalizedSeedFromTheorems
  normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
=
Source.normalizedSeedCCM25RestrictedEvaluatorScalar
  (RouteInputs.ofExpandedSourcePackage
    normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
  normalizedSourceBackedFixedSTestFromTheorems.weilTest
  normalizedTraceCCM25ArithmeticPackageFromTheorems
```

After unfolding the clean definitional side:

```text
left side:
  normalizedCoreTraceAmplitudeFromTheorems sourceTraceTest ^ 2

active traceAmplitude definition:
  normalizedCoreTraceAmplitudeFromTheorems g
    = || normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0 ||

right side:
  archimedeanTerm(common convolution square)
    + polePairing(common)
    - selected restricted finite-prime evaluator
```

Drilled and rejected as closure in this pass:

```text
1. Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
   clean, but proves only QW_lambda = restricted evaluator.

2. Source.normalizedSeedQWLambdaScalarIdentificationOfRestrictedEvaluator
   direction is backward for 04A; it consumes the missing evaluator identity.

3. Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
   uses pkg.s2b1NormalizedSeedSupportSquareMainTermEqualsQWLambda, the old
   theorem-base/fixed-tuple row.

4. Source.normalized_seed_support_square_eq_qwLambda_of_scalar_identification
   consumes the same scalar identification field.

5. Source.normalized_seed_source_no_defect_trace_eq_qwLambda_of_scalar_identification
   consumes the same scalar identification field.

6. Source.normalized_seed_source_no_defect_trace_eq_restricted_formula_of_scalar_identification
   consumes the same scalar identification field.

7. Source.normalized_seed_source_no_defect_eq_restricted_formula_of_certificate_boundary
   still requires a QW_lambda scalar identification.

8. TraceFrontEndData.normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff
   reads NormalizedSupportSquareQWLambdaScalarReadOff, which is the same
   support-square/QW_lambda equality in route form.

9. TraceFrontEndData.normalizedTraceAmplitudeSquareScalarContractOfSupportSquareScalarNormalForm
   is downstream of the support-square scalar contract.

10. normalizedTraceAmplitudeSquareScalarFromTheorems
    is built from normalizedTraceDataFromTheorems and the same read-off route.

11. Source.AnalyticCore.SourceTraceScaleData.toNormalizedLegalSquareTraceScaleSymbols
    only transfers traceAmplitude/support-square definitions.

12. Source.AnalyticCore.SourceWeilFormData.qwLambda
    is an independent Weil-form formula:
    archimedeanTerm + poleFunctional - restricted finite-prime sum.

13. Source.AnalyticCore.SourceEvaluationData.valueAt
    gives ||encode F x||, but there is no theorem tying the x = 0 value to
    selected QW_lambda.

14. SourceFinitePrimeExactSupportData / SourceFinitePrimeData
    cannot be used with empty or arbitrary support; project rules already
    reject that as Root 1/Root 2 fake closure.
```

Current exact first non-wrapper black box:

```text
selected active-seed source-core scalar theorem

  || normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode
       normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
       0 || ^ 2
  =
  (RouteInputs.ofExpandedSourcePackage
    normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols.qwLambda
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedSourceBackedFixedSTestFromTheorems.weilTest
    normalizedSourceBackedFixedSTestFromTheorems.weilTest
```

Equivalent evaluator form:

```text
  || encode sourceTraceTest 0 || ^ 2
  =
  archimedeanTerm(common convolution square)
    + polePairing(common)
    - selected restricted finite-prime evaluator
```

Next safe action:

```text
Either prove this selected active-seed source-core scalar theorem from a lower
analytic identity, or change the route/API so the active route does not demand
this equality from the generic source core.  Do not add another record field
that stores the equality.
```


## 12. Source-Core Calibration Drill, 2026-07-07

Result: bad for proof closure, good for black-box closure.  This pass drilled
below the route records, the S2-B1 read-off records, the CC20 trace-scale seed,
the CCM25 evaluator bridge, and the source evaluation definitions.  No lower
clean theorem was found that proves the active selected scalar identity.

No Lean code was changed in this pass.  Per instruction, no WSL build or
focused axiom audit was run.


### 12.1 Reduced Tree

The active 04A dependency now reduces to one source-core calibration theorem:

```text
04A selected restricted trace read-off
|
+-- normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
    |
    +-- normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
        |
        +-- normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
            |
            +-- CC20 leg:
            |     Source.normalizedSeedSupportSquareCC20ReadOffData
            |       proves only:
            |         supportSquareTrace(sourceTraceTest)
            |           =
            |         traceAmplitude(sourceTraceTest)^2
            |
            +-- CCM25 leg:
            |     Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
            |       proves cleanly:
            |         selected QW_lambda
            |           =
            |         selected restricted evaluator
            |
            +-- missing bridge:
                  traceAmplitude(sourceTraceTest)^2
                    =
                  selected QW_lambda
```

The exact missing equality is:

```text
|| normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode
     normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
     0 || ^ 2
  =
(RouteInputs.ofExpandedSourcePackage
  normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols.qwLambda
  normalizedTraceLambdaInputFromTheorems.lambda
  normalizedSourceBackedFixedSTestFromTheorems.weilTest
  normalizedSourceBackedFixedSTestFromTheorems.weilTest
```

Equivalent expanded formula:

```text
|| encode sourceTraceTest 0 || ^ 2
  =
archimedeanTerm(common convolution square)
  + polePairing(common)
  - selected restricted finite-prime evaluator
```


### 12.2 Primary Evidence

Active CC20 trace amplitude:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:135-138
  normalizedCoreTraceAmplitudeFromTheorems g
    =
  || normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0 ||
```

Active trace support square:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:172-178
  normalizedCoreSupportSquareTraceFromTheorems g
    =
  normalizedCoreTraceAmplitudeFromTheorems g ^ 2

  normalizedCoreSourceNoDefectTraceFromTheorems
    =
  normalizedCoreSupportSquareTraceFromTheorems
```

Source evaluation data:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:266-268
  SourceEvaluationData.valueAt E F x
    =
  || A.legacy.encode F x ||

ConnesWeilRH/Source/AnalyticCoreBase.lean:297-307
  sourcePrimePowerPairing and sourceFinitePrimeTerm use x = n and x = n^-1,
  not x = 0.
```

Active Weil-form `QW_lambda`:

```text
ConnesWeilRH/Source/AnalyticCore.lean:7742-7750
  W.qwLambda lambda f g
    =
  W.archimedeanTerm (A.convolutionStar f g)
    + W.evaluation.poleFunctional (A.convolutionStar f g)
    - sum over W.finitePrime.restrictedPrimeIndexSet lambda
```

CCM25 formula bridge:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:665-677
  normalized_seed_ccm25_qw_lambda_source_evaluator_read_off

Meaning:
  QW_lambda is unfolded to archimedean + pole - restricted finite-prime sum.
  It does not prove the CC20 trace amplitude square equals that sum.
```

Actual 04A record field:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:913-927
  NormalizedSeedRestrictedEvaluatorScalarIdentification
    stores:
      normalizedSeedSupportSquareReadOffSourceScalar A g
        =
      normalizedSeedCCM25RestrictedEvaluatorScalar W weilTest ccm25

ConnesWeilRH/Source/S2B1TraceScale.lean:937-948
  NormalizedSeedQWLambdaScalarIdentification
    stores:
      normalizedSeedSupportSquareReadOffSourceScalar A g
        =
      W.qwLambda lambda weilTest weilTest
```

Current active Dev proof still calls the core `sorry` root:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2548-2570
  normalizedSelectedQWLambdaScalarIdentificationFromTheorems
    calls:
      normalizedCoreS2B1ActualScalarIdentificationFromTheorems

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1026-1041
  normalizedCoreS2B1ActualScalarIdentificationFromTheorems := by sorry
```


### 12.3 Branches Drilled And Rejected

This batch checked and rejected these closure routes:

```text
1. Source.normalized_seed_ccm25_qw_lambda_source_evaluator_read_off
   Status:
     clean formula bridge only.
   Why rejected:
     proves QW_lambda = restricted evaluator, not traceAmplitude^2 = QW_lambda.

2. Source.normalizedSeedQWLambdaScalarIdentificationOfRestrictedEvaluator
   Status:
     direction is downstream.
   Why rejected:
     consumes NormalizedSeedRestrictedEvaluatorScalarIdentification.

3. Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
   Status:
     old theorem-base row.
   Evidence:
     ConnesWeilRH/Source/S2B1TraceScale.lean:973-993.
   Why rejected:
     reads pkg.s2b1NormalizedSeedSupportSquareMainTermEqualsQWLambda.

4. normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
   Status:
     old weak path.
   Evidence:
     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2055-2067.
   Why rejected:
     returns normalizedBaseFromTheorems.s2b1NormalizedSeedSupportSquareQWLambdaRow.

5. S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
   Status:
     visible row container.
   Evidence:
     ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:624-633.
   Why rejected:
     stores the two read-off legs; it does not derive the CC20/CCM25 scalar
     identity from lower analysis.

6. CC20SelectedTraceReadOffData.ofSupportSquareQWLambda
   Status:
     downstream selected read-off.
   Evidence:
     ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:683-713.
   Why rejected:
     positiveTrace_eq_qwLambda is derived only after supportSquare_qwLambda is
     already supplied.

7. normalizedTraceSupportSquareQWLambdaReadOffFromParts
   Status:
     TraceData readback.
   Evidence:
     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3010-3020.
   Why rejected:
     calls source_trace_support_square_qw_lambda_read_off_of_parts, which reads
     restricted_trace_read_off_of_source_trace_data.

8. normalizedTraceSupportSquareQWLambdaReadOffSourceDataFromTheorems
   Status:
     self-feed from selected 04A row.
   Evidence:
     ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3049-3063.
   Why rejected:
     its CC20 read-off is exactly
     normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems.supportSquareMainTermEqualsQWLambda,
     then the CCM25 side is rfl.

9. CC20 legal square trace-scale seed
   Status:
     definitional CC20 support-square only.
   Evidence:
     ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:340-414.
   Why rejected:
     proves supportSquareTrace = traceAmplitude^2, not traceAmplitude^2 =
     QW_lambda.

10. CC20 scalar trace seed
    Status:
      different seed.
    Evidence:
      ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:774-815.
    Why rejected:
      can make supportSquareTrace = scalarTrace by setting traceAmplitude to a
      square root, but that changes the selected active seed.

11. SourceTraceScaleData.toNormalizedLegalSquareTraceScaleSymbols
    Status:
      projection/transport.
    Evidence:
      ConnesWeilRH/Source/AnalyticCore.lean:8048-8055.
    Why rejected:
      transfers traceAmplitude, traceClass, cyclicLegal only.

12. SourceTraceScaleData.toArchimedeanTraceSymbols
    Status:
      projection/transport.
    Evidence:
      ConnesWeilRH/Source/AnalyticCore.lean:8056-8069.
    Why rejected:
      defines supportSquareTrace as traceAmplitude^2 and sets normalization
      rows to True; it does not connect to QW_lambda.

13. SourceEvaluationData.valueAt
    Status:
      low-level evaluator.
    Evidence:
      ConnesWeilRH/Source/AnalyticCoreBase.lean:266-285.
    Why rejected:
      gives ||encode F x||.  It does not identify the x = 0 value with the
      Weil-form formula.

14. SourceEvaluationData.sourcePrimePowerPairing / sourceFinitePrimeTerm
    Status:
      finite-prime evaluator input.
    Evidence:
      ConnesWeilRH/Source/AnalyticCoreBase.lean:297-334.
    Why rejected:
      uses x = n and x = n^-1.  It does not supply the missing x = 0
      calibration.

15. PrimePowerEvaluationBridge.ofSourceEvaluationData
    Status:
      evaluator exposure through legacy TestFunction.
    Evidence:
      ConnesWeilRH/Source/CCM25Concrete/PrimePowerEvaluationBridge.lean:27-72
      and 604-641.
    Why rejected:
      exposes valueAt and pairing read-off; it still requires a pairingReadOff
      input and does not prove traceAmplitude^2 = QW_lambda.

16. SourceWeilFormData.qwLambda
    Status:
      real formula owner.
    Evidence:
      ConnesWeilRH/Source/AnalyticCore.lean:7721-7750.
    Why rejected:
      it defines the right-hand side as archimedean + pole - finite-prime sum.
      It is not definitionally equal to ||encode g 0||^2.

17. SourceFinitePrimeExactSupportData / SourceFinitePrimeData
    Status:
      real finite support / finite-prime owner.
    Evidence:
      ConnesWeilRH/Source/AnalyticCore.lean:7375-7385 and 7748-7750.
    Why rejected:
      it can control restricted finite-prime support and summands, but cannot
      supply the missing archimedean/pole/x=0 calibration by itself.

18. theorem-base package support-square row
    Status:
      old weak source.
    Evidence:
      ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:3332-3344.
    Why rejected:
      it reads the same support-square/QW_lambda row out of the package; it is
      exactly the path 04A is trying to remove or demote to compatibility.
```


### 12.4 First-Principles Cut

What 04A wants is not a record problem.  It is a calibration problem:

```text
[CC20 trace side]
  amplitude(g)
    =
  || encode(g)(0) ||

  supportSquare(g)
    =
  amplitude(g)^2

                    missing theorem
                          |
                          v

[CCM25 Weil side]
  QW_lambda(lambda, f, f)
    =
  archimedeanTerm(f * f)
    + polePairing(f)
    - restrictedFinitePrimeSum(lambda, f)

                    clean theorem
                          |
                          v

[restricted evaluator]
  selected restricted evaluator scalar
```

The missing theorem must relate the selected `sourceTraceTest` on the CC20 side
to the selected `weilTest` / common convolution square on the CCM25 side:

```text
SelectedSourceCoreTraceQWLambdaCalibration
|
+-- input:
|     active source algebra
|     active trace scale
|     active Weil form
|     selected sourceTraceTest
|     selected fixed S-test / commonTest.sourceTest
|     selected lambda
|     selected concrete CCM25 arithmetic package
|
+-- theorem:
      traceAmplitude(sourceTraceTest)^2
        =
      qwLambda(lambda, weilTest, weilTest)
```

Without that theorem, every current route falls into one of two rejected shapes:

```text
old weak row:
  theorem-base / fixed-tuple package already stores supportSquare = QW_lambda

wrapper/readback:
  selected/read-off/TraceData object re-exposes supportSquare = QW_lambda
  after consuming the same equality
```


### 12.5 Closure Status

04A is not Lean-closed.

04A is black-box-closed to this exact leaf:

```text
First non-wrapper black box:

  selected active-seed source-core scalar calibration

  || encode sourceTraceTest 0 || ^ 2
    =
  archimedeanTerm(common convolution square)
    + polePairing(common)
    - selected restricted finite-prime evaluator
```

There are only two non-fake next moves:

```text
Path A. Prove the calibration theorem.
  Needed:
    a lower analytic theorem tying the zero-value trace amplitude to the
    selected Weil-form QW_lambda formula for the same selected source object.

Path B. Repair the route/API.
  Needed:
    show that the route is overstrong and should not demand generic
    traceAmplitude(sourceTraceTest)^2 = QW_lambda from the source core.
    The replacement API must expose the true lower obligation explicitly.
```

Rejected next moves:

```text
- add a record field restating the calibration theorem
- use normalizedCoreS2B1ActualScalarIdentificationFromTheorems
- use normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
- use normalizedActualScalarIdentificationFromTheoremBasePackage
- use Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
- use Source.normalizedSeedMatchedRestrictedEvaluatorScalarIdentification
- use normalizedTraceReadOffEqualityRowsFromTheorems
- use normalizedSourceObjectBridgeReadOffRowsInputFromTheorems
- use restricted_trace_read_off_of_source_trace_data
- use SourceTraceScaleData projection/readback
- use empty/arbitrary finite support, True, Set.univ, or Root 1 / Root 2
```


## 13. 2026-07-07 Active-Path Root Exposure

Result:

```text
Build-good, audit-bad for proof closure.
```

Code change:

```text
normalizedSelectedQWLambdaScalarIdentificationFromTheorems no longer calls:
  normalizedCoreS2B1ActualScalarIdentificationFromTheorems

The selected 04A path now factors through:
  normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
    -> normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
    -> normalizedSelectedQWLambdaScalarIdentificationFromTheorems
    -> normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
```

This is not proof closure.  The new source-core calibration input is the
explicit remaining 04A root:

```text
normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
```

WSL build:

```text
lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.RouteTheorem
passed under /tmp/connes-weil-rh-lake.lock.
```

Focused axiom audit:

```text
normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems
normalizedSelectedQWLambdaScalarIdentificationFromTheorems
normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems
normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple

all return:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

Acceptance status:

```text
04A old weak path removed from the active selected row.
04A proof remains open at the named selected source-core calibration root.
```
