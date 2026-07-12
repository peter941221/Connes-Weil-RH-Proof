# 08B Source-Zero Exclusion Plan

Result:
  Backup hard-gate plan.  Not accepted proof progress until a source-zero
  contradiction theorem is proved below the RH-equivalent sockets.

## 1. What Counts As Solved

Hard completion gate:

```text
The lane is solved only if:

1. Old weak path is deleted or compatibility-only:
     same-test Mathlib-bottom
     same-test local-sum calibration
     same-test half-density trace formula
     detector-wide pole-pairing nonnegativity
     detector-wide CC20WeilNonpositive
     normalizedSelectedNoOffLineSourceZeroFromTheorems

2. New semantic owner/API supplies the active proof object:
     a theorem that assumes an off-critical-line source zero and derives a
     contradiction from lower route/source data without assuming SourceRH or
     no-off-line source-zero.

3. The theorem is not propositionally equivalent to:
     Source.RHDefinitionBridge.standard.SourceRH
     forall source non-trivial zeros rho, rho.re = 1 / 2

4. Real consumer rewired:
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     or its lower source uses this contradiction theorem.

5. Smallest WSL build passes:
     lake build ConnesWeilRH.Route.CC20RouteRealization
       ConnesWeilRH.Dev.UnconditionalSkeleton

6. Focused axiom audit passes for:
     Route.<source-zero contradiction theorem>
     Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
     Dev.unconditional_rh_skeleton
```

## 2. What Does Not Count

Rejected as not solved:

```text
- Proving a theorem already guarded as iff no-off-line source-zero.

- Using SourceRH or no-off-line source-zero to build the contradiction.

- Reopening same-test Mathlib-bottom, same-test local-sum calibration,
  same-test half-density trace formula, or detector pole-pairing nonnegativity.

- Filling detector-wide CC20WeilNonpositive; Yoshida positivity makes this
  equivalent to excluding off-line zeros under detector existence.

- Using accepted-source fields, True, Set.univ, stored Mellin rows, stored
  determinant rows, or selected fixed route certificate rows for a different
  test.
```

## 3. Current Evidence

```text
Closed support:
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists

Rejected / RH-equivalent sockets:
  normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_standardSourceRH
  normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_standardSourceRH
  normalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer_iff_no_offline_source_zero
  normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeRealizer_iff_no_offline_source_zero
```

## 4. First-Principles Dependency Chain

```text
Route B
|
+-- assume source zero rho
|   |
|   +-- hrho : standard.sourceNontrivialZero rho
|   +-- hoff : rho.re != 1/2
|
+-- 05C detector
|   |
|   +-- D : YoshidaDetector normalizedCC20TestSpace F rho
|   +-- D gives positive local sum
|
+-- lower route theorem for D.test
|   |
|   +-- must not be:
|       same-test Mathlib-bottom
|       local-sum calibration
|       pole-pairing nonnegativity
|       detector-wide nonpositive
|
+-- contradiction
    |
    +-- positive local sum
    +-- route theorem gives incompatible sign/identity
```

## 5. Implementation Route

```text
B0. Inventory every existing source-zero contradiction theorem.

B1. Classify each as:
      clean support
      RH-equivalent guard
      false shortcut
      possible lower theorem

B2. Search for a lower theorem whose statement mentions the detector's actual
    test but does not assert nonpositive local sum or pole-pairing
    nonnegativity directly.

B3. If no lower theorem exists, mark 08B rejected and keep 08A as the primary
    route.

B4. Rewire Dev only after a lower theorem survives the equivalence scan.
```

## 6. Static Rejection Scans

```text
rg -n "iff_no_offline_source_zero|iff_standardSourceRH|iff_mathlibRH|SourceRH|NoOffLineSourceZero|PolePairingNonnegative|MathlibBottom|LocalSumCalibration|HalfDensityTraceFormula|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"
```

Any candidate theorem caught by an `iff_standardSourceRH`,
`iff_mathlibRH`, or `iff_no_offline_source_zero` guard is rejected as a lower
08B proof.

## 7. WSL Build Gate

Do not run during the current no-build execution round.

Milestone build, when Peter allows:

```text
flock /tmp/connes-weil-rh-lake.lock -c \
  'lake build ConnesWeilRH.Route.CC20RouteRealization ConnesWeilRH.Dev.UnconditionalSkeleton'
```

## 8. Focused Axiom Audit

Milestone audit targets:

```lean
#check ConnesWeilRH.Route.<source-zero contradiction theorem>
#print axioms ConnesWeilRH.Route.<source-zero contradiction theorem>

#check ConnesWeilRH.Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
#print axioms ConnesWeilRH.Dev.normalizedSelectedRouteBackedSourceRHFromTheorems

#check ConnesWeilRH.Dev.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.unconditional_rh_skeleton
```

Expected final result must not contain `sorryAx`.

## 9. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path:
  <which RH-equivalent route was removed>

New semantic owner/API:
  <source-zero contradiction theorem>

Real consumer rewired:
  <Dev/Route theorem now consuming contradiction>

Same-object alias / wrapper rejection scan:
  <scan result>

Smallest WSL build:
  <command and result>

Focused axiom audit:
  <targets and result>

Semantic sufficiency for next route/RH step:
  <why this theorem is below SourceRH>
```
