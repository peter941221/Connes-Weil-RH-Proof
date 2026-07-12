# 05F D1 Same-Test Pole-Pairing Trace Calibration Plan

Date: 2026-07-08

Status: diagnostic hard-gate plan.  This is not accepted RH progress and not a
Lean-verified closure.

Execution update, 2026-07-08, TraceFrontEnd positive-trace/QW boundary:

```text
Result:
  Good boundary guard.  Not an unconditional RH proof.

Files changed:
  ConnesWeilRH/Route/TraceFrontEnd.lean

What changed:
  Added two rfl diagnostic guards:

    TraceScaleNoExtraBulkScalarData.toSourceTermData_positiveTraceDecomposesIntoQWLambdaRankPoleCdef_eq
    no_extra_bulk_contract_of_parts_positiveTraceDecomposesIntoQWLambdaRankPoleCdef_eq

Meaning:
  The active Dev no-extra-bulk path uses
  `TraceScaleNoExtraBulkScalarData.toSourceTermData`, whose positive-trace
  source-term field is exactly the selected-source-trace equality:

    positiveTrace(sourceTraceTest) = qwLambda(lambda, sourceBackedTest, sourceBackedTest)

  This is real selected trace/QW information, not the fully arbitrary
  `no_extra_bulk_contract_of_parts` wrapper.  But it still stops at the
  selected QW scalar.  It does not connect the Yoshida detector's same-test
  concrete local sum or pole-pairing to the route positive trace.

  The wrapper constructor `no_extra_bulk_contract_of_parts` is separately
  guarded as a raw Prop alias: it sets the positive-trace decomposition field
  to the same arbitrary `noExtraBulkScaleTerm` Prop.  Do not use that
  constructor as a formula owner.

Verification:
  No Lean build or focused axiom audit was run in this update, per Peter's
  no-build instruction.  Static scan and rfl boundary guards only.

Next hard gate:
  The lower theorem still needed for 05F is not selected
  `positiveTrace = qwLambda`.  It must relate the same Yoshida detector test's
  concrete CC20 local sum / pole-pairing quantity to the route trace scalar,
  or the final route consumer must be redesigned to use a different statement.
```

Execution update, 2026-07-08, pole-pairing nonnegative socket rejected:

```text
Result:
  Good rejection evidence.  Not an unconditional RH proof.

Files changed:
  ConnesWeilRH/Route/CC20RouteRealization.lean

What changed:
  Added detector-level and concrete-moment-data pole-pairing equivalence
  guards:

    normalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer_iff_no_offline_source_zero
    normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeRealizer_iff_no_offline_source_zero

Meaning:
  Proving pole-pairing nonnegativity for every off-critical-line Yoshida
  detector, or for every concrete Yoshida moment-data witness, is already
  equivalent to proving no-off-line source zero.  The proof passes through the
  existing pole-pairing-to-CC20-nonpositive bridge and Yoshida positivity.

  Therefore the pole-pairing nonnegative route is not a lower analytic socket.
  It is only a different surface for the same RH-level contradiction.

Verification:
  No Lean build or focused axiom audit was run in this update, per Peter's
  no-build instruction.  Static scan located the new theorem names in
  `ConnesWeilRH/Route/CC20RouteRealization.lean`.

Next hard gate:
  Do not attack 05F by trying to prove detector-wide or concrete-moment-data
  pole-pairing nonnegativity.  A valid next cut must be a lower formula owner
  that explains why the same-test route trace scalar equals the concrete
  pole-pairing/local-sum quantity without assuming source-zero exclusion.
```

Execution update, 2026-07-08, final-sign adapter dependency audit:

```text
Result:
  Good rejection evidence.  Not an unconditional RH proof.

Files changed:
  ConnesWeilRH/Route/CC20RouteRealization.lean

What changed:
  Split the Yoshida sign consumer into a raw positive-trace dependency:

    normalizedRouteBackedYoshidaNonpositive_of_localSumReadOff_positiveTraceNonnegative

  The existing route theorem now factors through this smaller theorem:

    normalizedRouteBackedYoshidaSignTheorem_of_localSumReadOff

Meaning:
  On the active Yoshida route, `SourceQWNonnegativeToCC20Nonpositive` is not
  consumed as a full formula owner connecting source QW, pole-pairing, Mellin
  half-density, and the concrete CC20 local sum.  The consumer only uses:

    route local-sum read-off
      weilLocalSum(starConvolution detector.test) = -positiveTrace a

    positiveTrace nonnegativity
      0 <= positiveTrace a

  Therefore the final-sign package is not the remaining lower socket by
  itself.  A successful cut must either supply a genuinely lower same-test
  local-sum/pole-pairing calibration, or replace the final route theorem with
  a statement whose consumer actually uses the stronger formula fields.

Verification:
  No Lean build or focused axiom audit was run in this update, per Peter's
  no-build instruction.  This is static dependency evidence only.

Next hard gate:
  Do not try to close 05F by filling extra fields of
  `SourceQWEqualsNegCC20WeilSum` unless a real route consumer is rewired to use
  those fields to prove the same-test concrete CC20 local-sum sign.
```

Execution update, 2026-07-08, archimedean-lift route rejected as lower socket:

```text
Result:
  Good rejection guard.  Not an unconditional RH proof.

Files changed:
  ConnesWeilRH/Route/CC20RouteRealization.lean

What changed:
  Added Route-level equivalence guards showing that changing the
  archimedean-test witness is not enough if the route read-off still asserts
  `weilLocalSum(starConvolution detector.test) = -positiveTrace a`.

  New guard theorems:
    normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizer_iff_no_offline_source_zero
    normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanTraceRealizer_iff_no_offline_source_zero
    normalizedRouteBackedSourceZeroYoshidaDetectorTraceRealizer_iff_no_offline_source_zero
    normalizedRouteBackedSourceZeroYoshidaDetectorRouteRealizer_iff_no_offline_source_zero

Meaning:
  A different archimedean lift `a` does not by itself lower the problem.  If
  the route object still provides Hilbert-Schmidt/trace nonnegativity and the
  same sign read-off from the detector's positive Weil sum to `-positiveTrace a`,
  then the realizer is propositionally equivalent to no-off-line source zero.

Verification:
  No Lean build or focused axiom audit was run in this update, per Peter's
  no-build instruction.  Static scan located the new theorem names in
  `ConnesWeilRH/Route/CC20RouteRealization.lean`.

Next hard gate:
  A valid route change must alter the final sign semantics or introduce a
  genuinely lower source-zero exclusion theorem.  Merely replacing
  `archimedeanTest := detector.test` with another `archimedeanTest` while
  preserving the same local-sum read-off is rejected as RH-equivalent.
```

Execution update, 2026-07-08, direct root attack without build:

```text
Result:
  Good rejection guard.  Not an unconditional RH proof.

Files changed:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean

What changed:
  Added Lean-level equivalence guards proving that the current same-test
  concrete Yoshida realizer targets are not lower than RH:

    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_standardSourceRH
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_mathlibRH
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_standardSourceRH
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_mathlibRH

Meaning:
  Filling either same-test local-sum read-off realizer or same-test
  archimedean local-sum calibration realizer would be equivalent to proving
  `Source.RHDefinitionBridge.standard.SourceRH` / `_root_.RiemannHypothesis`.
  These are rejection guards, not closure.

Verification:
  No Lean build or focused axiom audit was run in this update, per Peter's
  "do not build" instruction.  Static scan located the new theorem names in
  `ConnesWeilRH/Dev/UnconditionalSkeleton.lean`.

Next hard gate:
  Do not route the remaining sorry through these realizer targets.  A valid
  next cut must introduce a genuinely lower non-circular source-zero exclusion
  theorem/API, or the root remains actual RH-level work.
```

Execution update, 2026-07-08:

```text
Result:
  Partial architectural cleanup.  Not an unconditional RH proof.

What changed:
  The false-socket producers were removed from the active Dev final path:
    Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibrationForSourceZeroFromTheorems
    Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormulaForSourceZeroFromTheorems
    Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems

  The final selected CC20 exit now depends on the explicit root:
    Dev.normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems

Meaning:
  The black box is no longer disguised as a local trace calibration.  It is now
  named as the real RH-level obligation: every standard source nontrivial zero
  lies on the critical line.

Current active root:
  Dev.normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems

Still not solved:
  This root still has `sorry`.  The change only prevents the proof graph from
  pretending that `polePairing(convolutionSquare detector.test) =
  positiveTrace detector.test` is a routine local theorem.

Verification:
  Fixed WSL ext4 mirror, preserving `.lake`, under
  /tmp/connes-weil-rh-lake.lock:
    lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  passed.

  Focused import-facing axiom audit for:
    Dev.normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems
    Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
    Dev.unconditional_rh_skeleton
  returned:
    [propext, sorryAx, Classical.choice, Quot.sound]

Next hard gate:
  Lower `normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems` to a
  real contradiction theorem whose assumptions are strictly weaker than
  SourceRH itself, or replace the final route with a non-circular source-zero
  exclusion argument.
```

Execution update, 2026-07-08, finite-vanishing criterion rejected:

```text
Result:
  Good rejection evidence.  Not an unconditional RH proof.

New clean theorems:
  Source.CC20YoshidaInterpolationNode.not_normalizedCC20FiniteVanishingToPolePairingSign
  Source.CC20YoshidaInterpolationNode.normalizedCC20_finiteVanishingToPolePairingSign_of_weil_criterion
  Source.CC20YoshidaInterpolationNode.not_normalizedCC20FiniteVanishingWeilCriterion

Meaning:
  The old fallback target
    CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet
  is formally false for the current concrete test space.

Reason:
  `exists_normalizedCC20_halfDensityPoleSum_counterexample` constructs a
  compact test vanishing on `{0, 1/2, 1}` whose half-density pole sum is
  negative.  Any finite-vanishing Weil criterion would imply the corresponding
  pole-pairing sign, contradicting that counterexample.

Verification:
  lake build ConnesWeilRH.Source.CC20YoshidaConstruction
    ConnesWeilRH.Dev.UnconditionalSkeleton
  passed in the fixed WSL mirror.

  Focused axiom audit returned no `sorryAx` for the three new rejection
  theorems:
    [propext, Classical.choice, Quot.sound]

Rejected route:
  Do not lower 05F to the concrete normalized CC20 finite-vanishing Weil
  criterion.  It is not merely unproved; it is false in this formal model.
```

Execution update, 2026-07-08, final root exposed:

```text
Result:
  Good cleanup / hard rejection evidence.  Not an unconditional RH proof.

What changed:
  The active Dev root was reduced to:

    Dev.normalizedSelectedSourceRHFromTheorems :
      Source.RHDefinitionBridge.standard.SourceRH

  Downstream wrappers now derive from that root:

    Dev.normalizedSelectedNoOffLineSourceZeroFromTheorems
    Dev.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorLocalSumCalibrationRealizerFromTheorems
    Dev.normalizedSelectedRouteBackedSourceRHFromTheorems

New route-side equivalence:
  Route.normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanLocalSumCalibrationRealizer_iff_no_offline_source_zero

  Under:
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    all-test Hilbert-Schmidt gate for the selected route inputs

  this proves:
    local-sum calibration realizer
      iff
    forall source nontrivial zeros rho, rho.re = 1 / 2

Meaning:
  The local-sum calibration socket is not lower than RH on the active final
  route.  It is equivalent to the no-off-line source-zero statement.  Reopening
  the same-test calibration, half-density trace formula, Mathlib-bottom, or
  concrete finite-vanishing criterion paths would only rename the same black
  box.

Verification:
  WSL persistent mirror build, preserving `.lake`, under
  /tmp/connes-weil-rh-lake.lock:

    lake build ConnesWeilRH.Dev.UnconditionalSkeleton
    lake build ConnesWeilRH.Route.CC20RouteRealization
      ConnesWeilRH.Dev.UnconditionalSkeleton

  passed.

  Focused axiom audit:
    Route.normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanLocalSumCalibrationRealizer_iff_no_offline_source_zero
      [propext, Classical.choice, Quot.sound]

    Dev.normalizedSelectedSourceRHFromTheorems
    Dev.normalizedSelectedNoOffLineSourceZeroFromTheorems
    Dev.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorLocalSumCalibrationRealizerFromTheorems
    Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
    Dev.unconditional_rh_skeleton
    Dev.unconditional_rh_contract_skeleton
      [propext, sorryAx, Classical.choice, Quot.sound]

Next hard gate:
  Find or introduce a genuinely non-circular theorem/API implying
  `Source.RHDefinitionBridge.standard.SourceRH`, or replace the final route by
  a source-zero exclusion argument whose statement is not already equivalent to
  RH.  Do not continue tactic-pushing the old calibration path.
```


## 1. Result First

Current result:
  Not solved.  The earlier same-test calibration socket has been rejected as
  an active lower target, because the route-side local-sum calibration realizer
  is equivalent to no-off-line source zero on the selected route.

The active 05F/05E black box is now the explicit standard source RH root:

```text
Dev.normalizedSelectedSourceRHFromTheorems :
  Source.RHDefinitionBridge.standard.SourceRH
```

The important point is negative:

```text
This is not a typing problem.
This is not a missing HEq transport problem.
This is not a routine simp/rw problem.
This is not a route local-sum calibration problem anymore.

It is now the actual RH-level source-zero exclusion:
  forall standard source nontrivial zeros rho, rho.re = 1 / 2
```


## 2. What Counts As Solved

Hard completion gate:
  The lane is solved only if:

```text
1. Old weak path is deleted or compatibility-only:
     Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormulaForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibrationForSourceZeroFromTheorems

2. New semantic owner/API supplies the active proof object:
     a lower theorem or data owner proving same-test calibration between
     Source.normalizedCC20ConcreteEvaluationData.polePairing
       (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare detector.test)
     and
     normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
       detector.test

3. The semantic theorem does not depend on:
     source zero falsehood
     selected SourceRH
     selected fixed route certificate for a different test
     raw accepted-source fields
     True / Set.univ / determinant rows / stored Mellin rows

4. Real consumers use the new owner:
     Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     Dev.unconditional_rh_skeleton

5. Smallest WSL build passes later, when builds are allowed:
     lake build ConnesWeilRH.Route.CC20RouteRealization
     lake build ConnesWeilRH.Dev.UnconditionalSkeleton

6. Focused axiom audit passes later, when builds are allowed, for:
     Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibrationForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormulaForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems
     Dev.normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     Dev.unconditional_rh_skeleton
```

Semantic sufficiency for next route/RH step:

```text
For every off-critical-line source zero rho and Yoshida detector for rho, the
route-backed sign family must derive CC20WeilNonpositive for detector.test from
same-test route data.  Combined with Yoshida detector positivity, this excludes
the source zero.
```


## 3. What Does Not Count

Rejected as not solved:

```text
- proving only HEq.rfl for detector.test as the archimedean test;
- unfolding positiveTrace to supportSquareTrace or |encode g 0|^2;
- using only CC20SelectedTraceReadOffData.positiveTrace_eq_qwLambda;
- using the selected fixed route certificate without proving it is the same
  detector.test;
- using the old forall-g half-density nonnegative route;
- using SourceRH, accepted-source fields, True, Set.univ, or raw free Prop
  fields;
- wrapping the current sorry root in a new record;
- treating a contradiction theorem as a producer of the calibration.
```


## 4. Current Evidence

Code evidence:

```text
Current active calibration Prop:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:5263

Current sorry root:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:5371

Mellin/pole-pairing bridge:
  ConnesWeilRH/Source/AnalyticCoreBase.lean:487

Concrete CC20 local sum is negative pole-pairing:
  ConnesWeilRH/Source/CC20ConcreteTestSpace.lean:101

Route positiveTrace bottom is support-square / point-amplitude square:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:137
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:176
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:182

SourceTraceScaleData defines positiveTrace as supportSquareTrace:
  ConnesWeilRH/Source/AnalyticCore.lean:8044

Existing selected route read-off gives positiveTrace = qwLambda, not
positiveTrace = polePairing:
  ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:692
  ConnesWeilRH/Route/TraceFrontEnd.lean:875

Yoshida positivity is produced from prescribed half-density Mellin values:
  ConnesWeilRH/Source/CC20YoshidaConstruction.lean:53

Negative guard already shows the current calibration is the contradiction
socket under an off-critical-line source zero:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:5482
```


## 5. First-Principles Dependency Chain

The current proof path:

```text
off-critical-line source zero rho
  |
  v
05C Yoshida detector exists for rho
  |
  v
detector.test
  |
  +--------------------------------------------------+
  |                                                  |
  v                                                  v
concrete CC20 side                              route trace side
  |                                                  |
  | normalizedCC20TestSpace.weilLocalSum             |
  |   (starConvolution detector.test)                |
  |                                                  |
  | = - polePairing                                  |
  |     (convolutionSquare detector.test)            |
  |                                                  |
  | = - Mellin half-density sum                      |
  |                                                  |
  v                                                  |
Yoshida construction proves local sum > 0            |
                                                     |
                                                     |
                                      positiveTrace detector.test
                                                     |
                                      = supportSquareTrace
                                                     |
                                      = qwLambda selected route tuple
                                                     |
                                      = |encode detector.test 0|^2
```

The missing edge:

```text
polePairing(convolutionSquare detector.test)
  =
positiveTrace(detector.test)
```

Why this is hard:

```text
left side:
  Mellin / pole-functional statement over the double convolution.

right side:
  route trace scale statement currently modeled as a support-square trace,
  concretely the square of the point amplitude at 0 in the Dev skeleton.

There is an existing bridge from positiveTrace to qwLambda, but no discovered
bridge from this pole-pairing functional to the same positiveTrace for an
arbitrary Yoshida detector test.
```


## 6. Attack Tree

```text
05F same-test pole-pairing trace calibration
|
+-- A. Close by lower semantic theorem
|   |
|   +-- A1. Find an existing owner
|   |   |
|   |   +-- scan positiveTrace / polePairing / qwLambda / read-off data
|   |   |
|   |   +-- accepted only if it states the same detector.test identity
|   |       and does not merely project the selected fixed route tuple
|   |
|   +-- A2. Prove a new lower theorem
|       |
|       +-- target:
|       |     polePairing(convolutionSquare detector.test)
|       |       =
|       |     positiveTrace(detector.test)
|       |
|       +-- required inputs:
|       |     concrete CC20 evaluation data
|       |     route trace-scale data for the exact same test
|       |     no dependence on source-zero contradiction
|       |
|       +-- risk:
|             likely false under the current point-amplitude trace model unless
|             the trace model is refined or replaced by a Mellin-calibrated
|             owner
|
+-- B. Change the trace-scale owner
|   |
|   +-- B1. Replace or refine positiveTrace so it is mathematically calibrated
|   |       to the CC20 pole-pairing side
|   |
|   +-- B2. Reprove existing nonnegativity and positiveTrace = qwLambda
|   |
|   +-- B3. Re-audit all route consumers of positiveTrace
|   |
|   +-- warning:
|         This is architecture-level and route-wide.  Do not do this silently.
|
+-- C. Reroute final contradiction without this calibration
|   |
|   +-- C1. Use Yoshida's positive local sum directly against a route theorem
|   |       that proves CC20WeilNonpositive for detector.test
|   |
|   +-- C2. This still needs same-test route data, but may avoid equating
|   |       polePairing with route positiveTrace explicitly
|   |
|   +-- C3. Accepted only if the route theorem consumes detector.test, not the
|           selected fixed test
|
+-- D. Rejected shortcuts
    |
    +-- selected fixed certificate reused for every detector
    +-- old all-input C.1 package
    +-- old forall-g half-density route
    +-- raw SourceRH / accepted-source theorem
    +-- determinant rows / stored Mellin rows as final theorem
    +-- True / Set.univ
    +-- same-object alias or wrapper around the sorry root
```


## 7. Implementation Route

Next concrete work round should do this in order:

```text
1. Run static scans only:
     rg -n "positiveTrace.*polePairing|polePairing.*positiveTrace|mellin.*positiveTrace|positiveTrace.*mellin" ConnesWeilRH -g "*.lean"
     rg -n "positiveTrace_eq_qwLambda|supportSquareTrace|qwLambdaFormula|polePairing_eq" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

2. If an owner exists:
     write a narrow theorem from that owner to
       NormalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibration
     and reject it if it uses a selected fixed test without same-test equality.

3. If no owner exists:
     do not keep tactic-pushing the current sorry.
     Decide between:
       A. new lower Mellin-calibrated trace owner;
       B. route theorem proving CC20WeilNonpositive for detector.test directly.

4. Only after code changes, when builds are allowed:
     sync to the persistent WSL mirror preserving .lake;
     run the smallest builds under /tmp/connes-weil-rh-lake.lock;
     run the focused import-facing axiom audit.
```


## 8. Static Rejection Scans

Use these before accepting any 05F patch:

```text
rg -n "SameTestPolePairingTraceCalibrationForSourceZeroFromTheorems|SameTestHalfDensityTraceFormulaForSourceZeroFromTheorems|MathlibBottomRealizerForSourceZeroFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "True|Set\\.univ|SourceRH|Accepted|determinant|stored.*Mellin|Mellin.*row|selected.*certificate|fixed route certificate" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/CC20RouteRealization.lean

rg -n "positiveTrace.*polePairing|polePairing.*positiveTrace|positiveTrace.*mellin|mellin.*positiveTrace" ConnesWeilRH -g "*.lean"

rg -n "positiveTrace_eq_qwLambda|supportSquareTrace|qwLambda" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"
```

Manual rejection rule:

```text
If the proof only shows:
  positiveTrace = supportSquareTrace
  supportSquareTrace = qwLambda

then it has not solved 05F unless it also connects that exact qwLambda or trace
scalar to the concrete CC20 pole-pairing for detector.test.
```


## 9. WSL Build Gate

Do not run this while Peter says not to build.

When allowed:

```text
cd /home/peter/verify/Connes-Weil-RH-Proof
flock /tmp/connes-weil-rh-lake.lock /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Route.CC20RouteRealization \
  ConnesWeilRH.Dev.UnconditionalSkeleton
```

Use the persistent ext4 verification mirror and preserve `.lake`.


## 10. Focused Axiom Audit

When builds are allowed, create an import-facing scratch file and audit:

```lean
#check ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibrationForSourceZeroFromTheorems
#print axioms ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibrationForSourceZeroFromTheorems

#check ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems
#print axioms ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaDetectorMathlibBottomRealizerForSourceZeroFromTheorems

#check ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
#print axioms ConnesWeilRH.Dev.normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems

#check ConnesWeilRH.Dev.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.unconditional_rh_skeleton
```

Accepted output must not contain:

```text
sorryAx
project-local axiom
opaque constant replacing the calibration
raw free Prop field stating the target identity
```


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed or demoted:
  <exact declarations>

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem proving same-test pole-pairing/positiveTrace calibration>

Real consumers rewired:
  <exact Dev/Route declarations>

Rejected shortcuts scanned:
  <commands and result>

WSL build:
  <commands and result>

Focused axiom audit:
  <targets and output>

Remaining blocker:
  <none, or exact next black box>
```
