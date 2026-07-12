# 07 D1 Same-Detector Nonpositive Route Plan

Date: 2026-07-08

Status: active hard-gate plan.  Do not count this as accepted proof progress
until the WSL build and focused axiom audit gates are run later.


## 1. Result First

Current result:
  Not solved.

The active Dev root is:

```text
Dev.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems :
  Route.NormalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer
```

This is better than a naked `standard.SourceRH`, but Route already exposes
that this realizer is equivalent to no-off-line source-zero under Yoshida
detector existence.  Therefore the next useful cut must lower the statement to
the same concrete detector test:

```text
for each off-critical-line source zero rho
  for each Yoshida detector D for rho
    prove the concrete sign for D.test
```


## 2. What Counts As Solved

Hard completion gate:
  The lane is solved only if:

```text
1. Old weak path is deleted or compatibility-only:
     normalizedSelectedSourceRHFromTheorems := by sorry
     normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems := by sorry
     local-sum calibration / MathlibBottom producers as final active roots

2. New semantic owner/API supplies the active proof object:
     Route.NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer
     or a strictly lower same-detector sign owner.

3. Named semantic theorem proves the lower-to-route connection:
     half-density sign
       -> pole-pairing sign
       -> CC20WeilNonpositive normalizedCC20TestSpace detector.test
       -> standard.SourceRH

4. Real consumers use the new owner:
     Dev.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems
     Dev.normalizedSelectedSourceRHFromTheorems
     Dev.normalizedSelectedCC20ExitPackageFromTheorems
     Dev.unconditional_rh_skeleton

5. Smallest WSL build passes later:
     lake build ConnesWeilRH.Route.CC20RouteRealization
       ConnesWeilRH.Dev.UnconditionalSkeleton

6. Focused axiom audit passes later for:
     Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer_iff_no_offline_source_zero
     Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegative_contradicts_moment_data
     Dev.normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeFromTheorems
     Dev.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems
     Dev.normalizedSelectedSourceRHFromTheorems
     Dev.unconditional_rh_skeleton
```


## 3. What Does Not Count

Rejected as not solved:

```text
- proving the global concrete finite-vanishing criterion;
- using local-sum calibration as the active final producer;
- using a selected fixed route certificate for every detector;
- using raw SourceRH, no-off-line source-zero, True, Set.univ, or an accepted
  source field as the proof term;
- proving only positiveTrace = supportSquareTrace = qwLambda;
- adding a wrapper around the same nonpositive realizer without exposing the
  detector.test pole-pairing / half-density sign.
```


## 4. Current Evidence

```text
CC20WeilNonpositive:
  ConnesWeilRH/Source/CC20TestSpace.lean

normalized CC20 local sum:
  normalizedCC20TestSpace.weilLocalSum g =
    -normalizedCC20ConcreteEvaluationData.polePairing g

same detector nonpositive expands to:
  0 <= normalizedCC20ConcreteEvaluationData.polePairing
         (normalizedCC20ConcreteTestAlgebra.convolutionSquare detector.test)

pole-pairing expands to the half-density Mellin sum by:
  polePairing_eq_mellin_convolutionSquare_half_sum
```


## 5. First-Principles Dependency Chain

```text
unconditional_rh_skeleton
|
+-- selected SourceRH
|   |
|   +-- Route.normalizedCC20_source_rh_of_source_zero_yoshida_detector_nonpositive
|       |
|       +-- normalizedCC20YoshidaDetectorExists
|       |
|       +-- source-zero detector nonpositive realizer
|           |
|           +-- for every off-line rho and detector D:
|               |
|               +-- CC20WeilNonpositive normalizedCC20TestSpace D.test
|                   |
|                   +-- unfold normalized CC20 local sum
|                       |
|                       +-- 0 <= polePairing (convolutionSquare D.test)
|                           |
|                           +-- polePairing = half-density Mellin sum
|                               |
|                               +-- 0 <=
|                                   Re Mellin(convolutionSquare
|                                     (convolutionSquare D.test), I/2)
|                                   +
|                                   Re Mellin(convolutionSquare
|                                     (convolutionSquare D.test), -I/2)
```

Attack tree:

```text
07 same-detector nonpositive
|
+-- A. Lower active root to same-detector pole-pairing sign
|   |
|   +-- A1. Define source-zero detector pole-pairing nonnegative realizer
|   +-- A2. Prove pole-pairing sign -> CC20WeilNonpositive
|   +-- A3. Rewire Dev active root to A1
|
+-- B. Lower one step more to concrete moment-data half-density sign
|   |
|   +-- B1. Define source-zero concrete moment-data half-density realizer
|   +-- B2. Prove half-density sign -> pole-pairing sign -> nonpositive
|   +-- B3. Rewire Dev active root to B1
|   +-- B4. Expose contradiction with ConcreteYoshidaMomentData negative
|           half-density theorem
|
+-- C. Boundary theorem
|   |
|   +-- C1. Prove half-density realizer -> no-off-line source zero
|   +-- C2. Prove no-off-line source zero -> half-density realizer
|   +-- C3. Mark equivalence as a warning: still RH-level if used as a closed
|           global root.
|
+-- D. Rejected shortcuts
    |
    +-- finite-vanishing criterion for all compact g
    +-- local-sum calibration as producer
    +-- selected fixed route certificate for arbitrary detector
    +-- raw SourceRH / no-off-line / True / Set.univ
```


## 6. Implementation Route

```text
1. Add Route-level same-detector sign owner:
     NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer

2. Add Route-level lower owner:
     NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer

3. Prove:
     concrete moment-data half-density -> pole-pairing
     pole-pairing -> nonpositive
     concrete moment-data half-density -> nonpositive
     concrete moment-data half-density iff no-off-line source-zero
     concrete moment-data half-density contradicts 05C moment data

4. Rewire Dev:
     active sorry becomes half-density nonnegative realizer
     nonpositive realizer is derived
     SourceRH is derived from nonpositive realizer
```


## 7. Static Rejection Scans

```text
rg -n "normalizedSelectedSourceRHFromTheorems\\s*:.*SourceRH\\s*:=\\s*by|normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems\\s*:.*:=\\s*by|Set\\.univ|\\bTrue\\b|accepted|Accepted" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/CC20RouteRealization.lean

rg -n "FiniteVanishingWeilCriterion|localSumCalibration|MathlibBottom|selected.*certificate|SourceRH" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/CC20RouteRealization.lean

rg -n "HalfDensityNonnegativeRealizer|PolePairingNonnegativeRealizer|NonpositiveRealizer" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/CC20RouteRealization.lean
```


## 8. WSL Build Gate

Do not run during this no-build work round.

When allowed:

```text
cd /home/peter/verify/Connes-Weil-RH-Proof
flock /tmp/connes-weil-rh-lake.lock /home/peter/.elan/bin/lake build \
  ConnesWeilRH.Route.CC20RouteRealization \
  ConnesWeilRH.Dev.UnconditionalSkeleton
```


## 9. Focused Axiom Audit

When builds are allowed:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check ConnesWeilRH.Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer_iff_no_offline_source_zero
#print axioms ConnesWeilRH.Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer_iff_no_offline_source_zero

#check ConnesWeilRH.Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegative_contradicts_moment_data
#print axioms ConnesWeilRH.Route.normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegative_contradicts_moment_data

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedSourceRHFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedSourceRHFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
```


## 10. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact declaration>

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem>

Consumer rewires:
  <exact Dev declarations>

Semantic sufficiency:
  Same-detector half-density sign is the active remaining blocker; it is still
  equivalent to no-off-line source-zero if taken as a closed global root.

Build:
  <not run in no-build round, or command/result later>

Focused axiom audit:
  <not run in no-build round, or theorem list/output later>

Remaining black box:
  <exact declaration/type>
```
