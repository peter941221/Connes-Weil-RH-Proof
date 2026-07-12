# A3 Fourier-Support Transform / Involution Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane A3.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

A3 is solved only if the active CCM24 source-to-route path proves Fourier
support as support of the transformed source test, then uses that proof to feed
the route-facing support/window consumer.

```text
old weak path:
  pkg.ccm24.sourceSoninSpaceComparisonData.2
    -> inputs.ccm24.fourierSupportInWindow semilocalTest window
    -> route consumers see only a window-subset compatibility row

new semantic owner/API:
  SourceFourierSupportInvolutionGeometryData, or an equivalent named theorem
  family owned by SourceFixedWindowCoordinateRows, that derives Fourier-support
  geometry from:
    S.fourierSupportCarrier S.sourceTest
      = S.supportCarrier (A.involution S.sourceTest)
    concreteTestAlgebra.involution f = FourierTransform.fourier f
    point-level coordinate facts for A.involution S.sourceTest

real consumer rewired:
  SourceSemilocalRows.sourceFourierSupportInWindow
  SourceSemilocalRows.sourceConvolutionSupportTransport
  SourceSemilocalRows.sourceSoninSpaceComparison
  SourceObject.CCM24SemilocalObjectPackage or a downstream package accessor
    that exposes the A3 owner
  SourceObject.SourceObjectPackage.ccm24_common_fourier_window
  SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
  SourceBackedFixedSTest.ofExpandedSourcePackage
  RouteTheorem.expanded_source_ccm24_common_convolution_support

same-object alias / wrapper rejection scan:
  rg -n "fourierSupportInWindow := pkg\\.ccm24\\.sourceSoninSpaceComparisonData\\.2|sourceSoninSpaceComparisonData\\.2|ccm24_common_fourier_window|ccm24_common_convolution_support_transported|sourceFourierSupportCarrier.*:= rfl|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"

package-owner migration gate:
  The current package stores only:
    sourceSoninSpaceComparisonData :
      sourceModel.semilocalSymbols.soninSpaceComparison sourceSupportWindow

  A3 must either add a named source/package owner for transformed-support
  geometry or add theorem accessors whose proof path starts from that owner.
  The old `sourceSoninSpaceComparisonData` field may remain for compatibility,
  but `.2` must stop being the active Fourier-support source for route-facing
  construction and route-facing wrapper theorems.

smallest WSL build:
  lake build ConnesWeilRH.Source.AnalyticSourceModel \
    ConnesWeilRH.Source.CCM24SourceModel \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution
  SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
  SourceFixedWindowCoordinateRows.fourierCoordinateLower
  SourceFixedWindowCoordinateRows.fourierCoordinateUpper
  SourceFixedWindowCoordinateRows.fourierLogScale_eq_zero
  SourceFixedWindowCoordinateRows.fourierSupportCarrier_subset_windowCarrier
  SourceFixedWindowCoordinateRows.fourierSupportInWindow
  SourceFixedWindowCoordinateRows.convolutionSupportTransported
  SourceFixedWindowCoordinateRows.soninSpaceComparison
  SourceSemilocalRows.sourceFourierSupportInWindow
  SourceSemilocalRows.sourceConvolutionSupportTransport
  SourceSemilocalRows.sourceSoninSpaceComparison
  SourceConcreteBaseLayer.concreteTestAlgebra_involution
  SourceConcreteBaseLayer.concreteSupportValue_involution_eq_fourier
  SourceConcreteBaseLayer.mem_concreteFourierSupportCarrier_iff
  SourceConcreteBaseLayer.concreteFourierSupportCarrier_eq_setOf_pointInWindow_fourier_value_ne_zero

semantic sufficiency for next route/RH step:
  Route-side fixed-S consumers must no longer rely on the second projection of
  sourceSoninSpaceComparisonData as an opaque Fourier-support row. They must get
  Fourier support/window, convolution support transport, and Sonin comparison
  through the named involution geometry owner. That owner must expose that the
  Fourier-support carrier is support of A.involution sourceTest, and in the
  concrete model A.involution is Mathlib FourierTransform.fourier.
```

Rejected as not solved:

```text
1. The patch only audits:
     fourierSupportCarrier_eq_supportCarrier_involution := rfl
   while the route consumer still reads `.sourceSoninSpaceComparisonData.2`.

2. The patch adds a theorem that projects an existing record field but does not
   show point-level geometry for `A.involution S.sourceTest`.

3. The patch proves concrete Fourier-support membership but leaves
   SourceBackedFixedSTest.ofExpandedSourcePackage on:
     fourierSupportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.2

4. The patch rewires `SourceBackedFixedSTest.ofExpandedSourcePackage` but leaves
   these route-facing wrappers reading `.sourceSoninSpaceComparisonData.2`:
     SourceObject.SourceObjectPackage.ccm24_common_fourier_window
     SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
     RouteTheorem.expanded_source_ccm24_common_convolution_support

5. The patch uses `True`, `Set.univ`, a free `Prop` field, endpoint package
   evidence, or a same-object alias to discharge Fourier support.

6. The patch passes Source builds and focused axiom audit, but the route-facing
   consumer still sees only the old weak statement.
```


## 2. Result First

Expected result:

```text
Good only if:
  A3 makes Fourier support a transformed-support theorem in the active route
  path.

Partial only if:
  A3 adds local concrete Fourier-support facts but does not rewire a route
  consumer.

Rejected if:
  A3 only renames the old `fourierSupportInWindow` projection or wraps
  `sourceSoninSpaceComparisonData.2`.
```

A3 is not A4. A4 concerns Fourier grading and coordinate Fourier equivalence.
A3 concerns the support carrier of the transformed source test.


## 3. Evidence Snapshot

Ledger source:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:84-89
  A3. Fourier-support transform / involution
    fourierSupportCarrier
    supportCarrier (A.involution sourceTest)
    sourceFourierSupportCarrier_eq_involutionSupport
    support geometry of the transformed source test
```

The source-support definition already gives the definitional bridge:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:921-935
  def fourierSupportCarrier := S.supportCarrier (A.involution f)
  theorem fourierSupportCarrier_eq_supportCarrier_involution ... := rfl

ConnesWeilRH/Source/AnalyticCoreBase.lean:1011-1015
  x in S.fourierSupportCarrier f <->
    S.supportValue (A.involution f) x != 0
```

The concrete source algebra ties involution to Mathlib Fourier transform:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:3115-3131
  concreteTestAlgebra.involution f = FourierTransform.fourier f
```

The concrete support value already has the transformed-value readback:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:3241-3246
  concreteSupportValue I (concreteTestAlgebra.involution f) x =
    concreteSupportValue I (FourierTransform.fourier f) x

ConnesWeilRH/Source/AnalyticCoreBase.lean:3308-3317
  x in concrete fourierSupportCarrier f <->
    pointInConcreteWindow I x and (FourierTransform.fourier f) x.1 != 0
```

The current route-facing consumer still reads a weak projection:

```text
ConnesWeilRH/Route/Definitions.lean:139
  inputs.ccm24.fourierSupportInWindow semilocalTest window

ConnesWeilRH/Route/Definitions.lean:201-202
  supportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.1
  fourierSupportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.2
```

Other route-facing wrappers also read the same weak projection:

```text
ConnesWeilRH/Source/ObjectDerivations.lean:74-92
  ccm24_common_fourier_window
  ccm24_common_convolution_support_transported

ConnesWeilRH/Route/RouteTheorem.lean:1211-1216
  expanded_source_ccm24_common_convolution_support
```

This evidence says the lower facts exist, but the active route path can still
hide them behind the old package projection. A3 closes only when the active
consumer path uses the lower transformed-support owner.


## 4. First-Principles Dependency Chain

```text
+--------------------------------------------------------------+
| Source test algebra                                           |
|                                                              |
|   A.involution sourceTest                                    |
|   concrete: A.involution f = FourierTransform.fourier f      |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Fourier-support carrier                                      |
|                                                              |
|   S.fourierSupportCarrier sourceTest                         |
|     = S.supportCarrier (A.involution sourceTest)              |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Point-level geometry                                          |
|                                                              |
|   membership -> supportValue (A.involution sourceTest) != 0   |
|   membership -> coordinate lower / upper / logScale = 0       |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Fixed-window source rows                                      |
|                                                              |
|   fourierSupportInWindow                                     |
|   convolutionSupportTransported                              |
|   soninSpaceComparison                                       |
+------------------------------+-------------------------------+
                               |
                               v
+--------------------------------------------------------------+
| Route-facing fixed-S consumer                                 |
|                                                              |
|   SourceBackedFixedSTest.ofExpandedSourcePackage              |
|   RouteInputs.ccm24                                           |
+--------------------------------------------------------------+
```

Why this matters:

```text
window-subset compatibility
  says: Fourier support is inside the fixed window.

transformed-support geometry
  says: Fourier support is the support of the Fourier/involution-transformed
  source test, and its window facts come from point-level geometry of that
  transformed test.
```

The second statement is stronger. It can feed later support transport,
convolution support transport, and Sonin comparison rows without treating
Fourier support as an opaque package fact.


## 5. What Counts As Solved

A3 solved means all items below hold in the same final snapshot.

```text
1. The active owner is named and source-local.
   Use either:
     SourceFourierSupportInvolutionGeometryData
   or explicit theorem family names that carry the same content.

2. The owner proves membership through the transformed source test:
     x in S.fourierSupportCarrier S.sourceTest
       <->
     S.supportValue (A.involution S.sourceTest) x != 0

3. The owner proves point geometry for the transformed source test:
     fourierCoordinateLower
     fourierCoordinateUpper
     fourierLogScale_eq_zero

4. The owner derives the fixed-window rows:
     fourierSupportCarrier_subset_windowCarrier
     fourierSupportInWindow
     convolutionSupportTransported
     soninSpaceComparison

5. Concrete readback reaches Mathlib Fourier:
     concreteTestAlgebra.involution f = FourierTransform.fourier f
     x in concrete fourierSupportCarrier f <->
       pointInConcreteWindow I x and (FourierTransform.fourier f) x.1 != 0

6. Route-facing construction stops reading the Fourier row from:
     pkg.ccm24.sourceSoninSpaceComparisonData.2
   as the active source of evidence.

7. Package-facing wrappers stop exporting `.sourceSoninSpaceComparisonData.2`
   as the route-visible Fourier-support source:
     SourceObject.SourceObjectPackage.ccm24_common_fourier_window
     SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
     RouteTheorem.expanded_source_ccm24_common_convolution_support

8. Builds and focused axiom audit pass in the WSL mirror.
```


## 6. What Does Not Count

Do not accept these shapes:

```text
same-object definitional bridge only:
  S.fourierSupportCarrier f = S.supportCarrier (A.involution f)

projection-only route:
  sourceSoninSpaceComparisonData.2
    -> fourierSupportInWindow

wrapper-only theorem:
  theorem new_name : old_fourierSupportInWindow := old_name

generic support/window theorem:
  proves subset but never mentions A.involution sourceTest

concrete-only theorem with no consumer:
  mem_concreteFourierSupportCarrier_iff passes audit, but no route-facing
  declaration uses it.

half migration:
  SourceBackedFixedSTest.ofExpandedSourcePackage no longer reads `.2`, but
  ObjectDerivations or RouteTheorem wrappers still export `.2` to route-facing
  code.
```

The definitional bridge is useful evidence. It cannot close A3 by itself
because the active route proof still needs transformed-support geometry.


## 7. Implementation Route

### Step A3.1: Pin Current Types

Run local type checks before editing:

```lean
#check SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution
#check SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
#check SourceFixedWindowCoordinateRows.fourierCoordinateLower
#check SourceFixedWindowCoordinateRows.fourierCoordinateUpper
#check SourceFixedWindowCoordinateRows.fourierLogScale_eq_zero
#check SourceFixedWindowCoordinateRows.fourierSupportInWindow
#check SourceFixedWindowCoordinateRows.convolutionSupportTransported
#check SourceSemilocalRows.sourceFourierSupportInWindow
#check SourceConcreteBaseLayer.concreteTestAlgebra_involution
#check SourceConcreteBaseLayer.mem_concreteFourierSupportCarrier_iff
```

Expected result:

```text
The existing declarations elaborate. If a name has moved, update the plan
before editing Lean.
```

### Step A3.2: Add The Semantic Owner

Preferred owner:

```lean
structure SourceFourierSupportInvolutionGeometryData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  carrier_eq_involutionSupport :
    S.fourierSupportCarrier S.sourceTest =
      S.supportCarrier (A.involution S.sourceTest)
  mem_iff_supportValue_involution_ne_zero :
    forall x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest ↔
        S.supportValue (A.involution S.sourceTest) x ≠ 0
  coordinateLower :
    forall x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I
  coordinateUpper :
    forall x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I
  logScale_eq_zero :
    forall x : S.SupportPoint,
      x ∈ S.fourierSupportCarrier S.sourceTest →
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0
```

Lean syntax can differ. The semantic content must not differ.

Construction rule:

```text
Build this owner from:
  SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution
  SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
  rows.sourceSupportCoordinateScaleModel.supportValue_coordinateLower
    (A.involution S.sourceTest)
  rows.sourceSupportCoordinateScaleModel.supportValue_coordinateUpper
    (A.involution S.sourceTest)
  rows.sourceSupportCoordinateScaleModel.supportValue_logScale_eq_zero
    (A.involution S.sourceTest)
```

Rejected construction:

```text
Store the row as a caller-supplied Prop.
Use `True`.
Use `Set.univ`.
Use an endpoint package theorem.
Copy `rows.fourierSupportInWindow` into a new name without exposing the
transformed source test.
```

### Step A3.3: Derive Fixed-Window Rows From The Owner

Add or strengthen theorem names like:

```text
SourceFourierSupportInvolutionGeometryData.fourierSupportCarrier_subset_windowCarrier
SourceFourierSupportInvolutionGeometryData.fourierSupportInWindow
SourceFourierSupportInvolutionGeometryData.convolutionSupportTransported
SourceFourierSupportInvolutionGeometryData.soninSpaceComparison
```

Then route the existing row declarations through this owner:

```text
SourceFixedWindowCoordinateRows.fourierSupportCarrier_subset_windowCarrier
SourceFixedWindowCoordinateRows.fourierSupportInWindow
SourceFixedWindowCoordinateRows.convolutionSupportTransported
SourceFixedWindowCoordinateRows.soninSpaceComparison
```

The proof terms should visibly use `coordinateLower`, `coordinateUpper`, and
`logScale_eq_zero` from the involution geometry owner.

### Step A3.4: Add Concrete Readback Theorems

The concrete lane must expose the transformed test as Mathlib Fourier:

```text
concreteFourierSupportCarrier_eq_involutionSupport
concreteFourierSupportCarrier_eq_supportCarrier_fourier
mem_concreteFourierSupportCarrier_iff
concreteFourierSupportCarrier_eq_setOf_pointInWindow_fourier_value_ne_zero
```

The key theorem must mention:

```text
FourierTransform.fourier
```

or the notation:

```text
𝓕
```

It must not stop at `A.involution` unless the same proof path also audits:

```text
concreteTestAlgebra_involution
```

### Step A3.5: Rewire The Route-Facing Consumer

Before editing `Route/Definitions.lean`, add the package-owner migration path.
The current package schema only has:

```lean
structure CCM24SemilocalObjectPackage where
  sourceModel : CCM24SourceModel
  sourceSupportWindow : sourceModel.semilocalSymbols.Window
  sourceSoninSpaceComparisonData :
    sourceModel.semilocalSymbols.soninSpaceComparison sourceSupportWindow
```

Acceptable A3 package shapes:

```text
Option 1:
  Add sourceFourierSupportInvolutionGeometryData to
  CCM24SemilocalObjectPackage, then derive compatibility
  sourceSoninSpaceComparisonData from it.

Option 2:
  Keep the package schema stable, but add theorem accessors whose proof path
  starts from SourceSemilocalRows / SourceFixedWindowCoordinateRows A3 owner and
  prove that `sourceSoninSpaceComparisonData.2` is compatibility-only.
```

Option 1 is preferred if route-facing construction needs to inspect the owner.
Option 2 is acceptable only if the final dependency path for route-facing
Fourier support visibly passes through the A3 owner, not through a projection
wrapper.

Required package/wrapper consumers:

```text
ConnesWeilRH/Source/Objects.lean
  SourceObject.CCM24SemilocalObjectPackage

ConnesWeilRH/Source/ObjectDerivations.lean
  SourceObject.SourceObjectPackage.ccm24_common_fourier_window
  SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported

ConnesWeilRH/Route/RouteTheorem.lean
  expanded_source_ccm24_common_convolution_support
```

Do not call A3 solved while any of those route-facing wrappers use
`.sourceSoninSpaceComparisonData.2` as the active proof source.

### Step A3.6: Rewire `SourceBackedFixedSTest`

Current weak route path:

```lean
fourierSupportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.2
```

Replace it with a named theorem path from the A3 owner. Acceptable shapes:

```text
pkg.ccm24.sourceFourierSupportInvolutionGeometryData.toFourierSupportInWindow
```

or:

```text
pkg.ccm24.sourceModel.sourceFourierSupportInvolutionGeometryData
  -> SourceSemilocalRows.sourceFourierSupportInWindow
```

The exact API can change during implementation. The final route proof must make
the transformed-support owner visible in the dependency path.

Do not remove `sourceSoninSpaceComparisonData` before all consumers that need
it have moved. It may remain as compatibility, but A3 cannot call it the active
Fourier-support source.


## 8. Static Rejection Scans

Run before and after implementation:

```text
rg -n "fourierSupportInWindow := pkg\\.ccm24\\.sourceSoninSpaceComparisonData\\.2|sourceSoninSpaceComparisonData\\.2|ccm24_common_fourier_window|ccm24_common_convolution_support_transported|expanded_source_ccm24_common_convolution_support" ConnesWeilRH/Route ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"

rg -n "sourceFourierSupportInWindow|sourceConvolutionSupportTransport|sourceSoninSpaceComparison|fourierSupportInWindow" ConnesWeilRH/Route ConnesWeilRH/Source -g "*.lean"

rg -n "sourceFourierSupportInvolutionGeometryData|SourceFourierSupportInvolutionGeometryData|fourierSupportInvolution|involutionGeometry" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "fourierSupportCarrier.*Set\\.univ|fourierSupportCarrier.*True|sourceFourierSupport.*Prop|involutionSupport.*Prop" ConnesWeilRH/Source -g "*.lean"

rg -n "fourierSupportCarrier_eq_supportCarrier_involution|mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero|concreteTestAlgebra_involution|FourierTransform\\.fourier|𝓕" ConnesWeilRH/Source -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"
```

Acceptance reading:

```text
1. Direct route construction through `.sourceSoninSpaceComparisonData.2` must
   disappear from the active A3 route path.

2. Direct route-facing wrappers through `.sourceSoninSpaceComparisonData.2`
   must disappear or be documented as compatibility-only:
     ccm24_common_fourier_window
     ccm24_common_convolution_support_transported
     expanded_source_ccm24_common_convolution_support

3. Remaining `.sourceSoninSpaceComparisonData.2` hits must be documented as
   compatibility-only or outside the A3 dependency path.

4. No new `sorry`, `admit`, project axiom, `constant`, `opaque`, `unsafe`,
   `True`, or `Set.univ` may appear in the A3 lane.
```


## 9. WSL Build Gate

Sync first:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Run the smallest route-facing build gate:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.AnalyticSourceModel ConnesWeilRH.Source.CCM24SourceModel ConnesWeilRH.Route.RouteTheorem'
```

If `ConnesWeilRH/Dev/UnconditionalSkeleton.lean` changes, run:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'
```

Passing Source builds alone does not close A3 because A3 has a route-facing
consumer.


## 10. Focused Axiom Audit

Create a scratch file in the WSL mirror that imports the owner modules and
checks the real semantic targets:

```lean
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Route.RouteTheorem

open ConnesWeilRH
open ConnesWeilRH.Source
open ConnesWeilRH.Source.AnalyticCore

#check SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution
#print axioms SourceSupportWindowData.fourierSupportCarrier_eq_supportCarrier_involution

#check SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
#print axioms SourceSupportWindowData.mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero

#check SourceFixedWindowCoordinateRows.fourierCoordinateLower
#print axioms SourceFixedWindowCoordinateRows.fourierCoordinateLower

#check SourceFixedWindowCoordinateRows.fourierCoordinateUpper
#print axioms SourceFixedWindowCoordinateRows.fourierCoordinateUpper

#check SourceFixedWindowCoordinateRows.fourierLogScale_eq_zero
#print axioms SourceFixedWindowCoordinateRows.fourierLogScale_eq_zero

#check SourceFixedWindowCoordinateRows.fourierSupportCarrier_subset_windowCarrier
#print axioms SourceFixedWindowCoordinateRows.fourierSupportCarrier_subset_windowCarrier

#check SourceFixedWindowCoordinateRows.fourierSupportInWindow
#print axioms SourceFixedWindowCoordinateRows.fourierSupportInWindow

#check SourceFixedWindowCoordinateRows.convolutionSupportTransported
#print axioms SourceFixedWindowCoordinateRows.convolutionSupportTransported

#check SourceFixedWindowCoordinateRows.soninSpaceComparison
#print axioms SourceFixedWindowCoordinateRows.soninSpaceComparison

#check SourceSemilocalRows.sourceFourierSupportInWindow
#print axioms SourceSemilocalRows.sourceFourierSupportInWindow

#check SourceSemilocalRows.sourceConvolutionSupportTransport
#print axioms SourceSemilocalRows.sourceConvolutionSupportTransport

#check SourceSemilocalRows.sourceSoninSpaceComparison
#print axioms SourceSemilocalRows.sourceSoninSpaceComparison

#check Source.SourceObject.SourceObjectPackage.ccm24_common_fourier_window
#print axioms Source.SourceObject.SourceObjectPackage.ccm24_common_fourier_window

#check Source.SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
#print axioms Source.SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported

#check SourceConcreteBaseLayer.concreteTestAlgebra_involution
#print axioms SourceConcreteBaseLayer.concreteTestAlgebra_involution

#check SourceConcreteBaseLayer.concreteSupportValue_involution_eq_fourier
#print axioms SourceConcreteBaseLayer.concreteSupportValue_involution_eq_fourier

#check SourceConcreteBaseLayer.mem_concreteFourierSupportCarrier_iff
#print axioms SourceConcreteBaseLayer.mem_concreteFourierSupportCarrier_iff

#check SourceConcreteBaseLayer.concreteFourierSupportCarrier_eq_setOf_pointInWindow_fourier_value_ne_zero
#print axioms SourceConcreteBaseLayer.concreteFourierSupportCarrier_eq_setOf_pointInWindow_fourier_value_ne_zero
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

Rejected output:

```text
sorryAx
project-local axiom
constant
opaque
unsafe
free Prop field that states the target theorem
endpoint package theorem
certificate atom
```

Do not audit only the package projection. Audit the theorem that carries
transformed-support geometry.


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  pkg.ccm24.sourceSoninSpaceComparisonData.2 is no longer the active
  Fourier-support source for SourceBackedFixedSTest.ofExpandedSourcePackage,
  SourceObject.SourceObjectPackage.ccm24_common_fourier_window,
  SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported,
  or RouteTheorem.expanded_source_ccm24_common_convolution_support.

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem proving Fourier support is support of A.involution sourceTest>
  <exact concrete theorem tying A.involution to FourierTransform.fourier>

Consumer rewires:
  SourceFixedWindowCoordinateRows.<names>
  SourceSemilocalRows.<names>
  SourceObject.CCM24SemilocalObjectPackage or package accessor <names>
  SourceObject.SourceObjectPackage.ccm24_common_fourier_window
  SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
  SourceBackedFixedSTest.ofExpandedSourcePackage
  RouteTheorem.expanded_source_ccm24_common_convolution_support

Semantic sufficiency:
  Fourier support now reaches the route as transformed-support geometry, not
  only as a window-subset compatibility projection. This is strong enough for
  the next CCM24 route/source step because support transport and Sonin
  comparison can read the transformed test's point-level support facts.

Build:
  <exact WSL command>
  <result>

Focused axiom audit:
  <theorem list>
  <axiom output>

Remaining black box:
  <exact declaration/type, if any>
```


## 12. Stop Rule

Stop and mark A3 partial if the only buildable route leaves:

```text
fourierSupportInWindow := pkg.ccm24.sourceSoninSpaceComparisonData.2
```

as the active route evidence.

Stop and mark A3 diagnostic-only if the implementation requires changing the
meaning of `SourceSupportWindowData.fourierSupportCarrier` away from:

```text
S.supportCarrier (A.involution f)
```

That would change the semantic lane instead of completing it.
