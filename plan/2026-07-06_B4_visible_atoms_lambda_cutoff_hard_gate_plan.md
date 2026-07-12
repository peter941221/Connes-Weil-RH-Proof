# B4 Visible Atoms In Lambda Cutoff Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane B4.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

B4 is solved only when the active route-visible atom path proves that a
route-visible atom inside the lambda cutoff is the same atom used by the
source-visible arithmetic data, and a real restricted evaluator consumer uses
that bridge.

```text
old weak path:
  finitePrimeAtomVisible n (W.convolutionStar f g)
    -> route_visibility_iff_source_visibility
    -> sourceTest.sourceAtomVisible n
    -> atVisibleIndex n
    -> copied lambdaCut from SourceRestrictedIndexData or certificate support
    -> restricted evaluator consumer

new semantic owner/API:
  ConcreteCommonFixedLambdaPrimePowerSupport or lower source-Weil-form owner
  carrying one bridge:
    route-visible atom + 1 < n + (n : Real) <= lambda ^ 2
      -> source-visible arithmetic atom with the same n
      -> restricted index membership with the same lambda cutoff

real consumer rewired:
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
  SourceEvaluationVisibleFinitePrimeSupportBoundary.restrictedArithmeticData
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows

same-object alias / wrapper rejection scan:
  rg -n "route_visibility_iff_source_visibility|sourceAtomVisible|lambdaCut :=|visibleAtomsInLambdaCut|toSupportBoundary|restrictedArithmeticData|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge \
    ConnesWeilRH.Source.ObjectExpandedRows \
    ConnesWeilRH.Source.S2B1TraceScale \
    ConnesWeilRH.Route.TraceFrontEnd \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  ConcreteCommonFixedLambdaPrimePowerSupport.support_visibility_iff_common_visibility
  ConcreteCommonFixedLambdaPrimePowerSupport.route_visibility_iff_common_visible_atom_data
  FixedLambdaSourceWeilFormVisibleArithmeticData.visible
  FixedLambdaSourceWeilFormVisibleArithmeticData.sourcePrimePowerIndex
  FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  Route.normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows

semantic sufficiency for next route/RH step:
  The restricted scalar in `QW_lambda` must use exactly the route-visible atoms
  that satisfy the lambda cutoff. B4 closes the bridge between route visibility,
  source visibility, and restricted arithmetic data.
```

Rejected as not solved:

```text
1. The patch only restates `route_visibility_iff_source_visibility`.

2. The active restricted evaluator still obtains lambda membership only from:
     hdata.lambdaCut
     certificate.support.restrictedIndexData
     package exact-support endpoint

3. The proof constructs a source-visible atom unrelated to the route-visible
   atom consumed by the route.

4. The route consumer still sees only old support-boundary wrappers.
```


## 2. Result First

Expected result:

```text
Good:
  B4 rewires one restricted evaluator consumer so the same atom n flows through
  route visibility, source visibility, source arithmetic data, and lambda
  cutoff membership.

Partial:
  B4 proves a bridge theorem but no restricted evaluator consumer moves.

Rejected:
  B4 only adds another visibility wrapper or copies lambdaCut.
```


## 3. Current Evidence

Root map evidence:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:134-138
  B4. visible atoms in lambda cutoff
    visibleAtomsInLambdaCut
    source-visible / route-visible bridge
    lambda cutoff membership
```

Current route/source visibility bridge:

```text
ConnesWeilRH/Source/CCM25Concrete/CommonSourceTest.lean:77-85
  ConcreteCommonSourceTest.sourceAtomVisible
  ConcreteCommonSourceTest.route_visibility_iff_source_visibility
```

Current fixed-lambda common support bridge:

```text
ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:366-435
  ConcreteCommonFixedLambdaPrimePowerSupport ties support.sourceTest to the
  concrete common source test and proves route_visibility_iff_common_visible_atom_data.
```

Current restricted arithmetic data:

```text
ConnesWeilRH/Source/ObjectExpandedRows.lean:613-636
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData obtains
  source visibility from supportData.restrictedIndexData and then calls
  visibleData.atVisibleIndex.
```

Current lambda-cut propagation:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:239-253
  restrictedExact uses hdata.lambdaCut.1 and hdata.lambdaCut.2.

ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:300-310
  restrictedExact uses hdata.lambdaCut.1 and hdata.lambdaCut.2.
```


## 4. First-Principles Dependency Chain

```text
route-visible atom at n
  |
  v
same n is source-visible for the common source test
  |
  v
source-visible arithmetic data at n
  |
  v
1 < n and (n : Real) <= lambda ^ 2
  |
  v
n belongs to W.restrictedPrimeIndexSet lambda
  |
  v
restricted finite-prime evaluator sum uses that same atom
```

B4 is not B3 repeated. B3 proves exact restricted coverage. B4 proves the
visible atom used by the restricted evaluator is the same route-visible atom
inside the cutoff.


## 5. What Counts As Solved

All items below must hold.

```text
1. A named theorem carries route-visible atom data into source-visible
   arithmetic data for the same n.

2. The same theorem or adjacent owner carries the lambda-cut facts needed for
   restricted index membership.

3. SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData or a
   route theorem above it uses that bridge.

4. The old path that copies source visibility and lambdaCut separately is
   deleted or marked compatibility-only.
```


## 6. What Does Not Count

Reject:

```text
visibility-only wrapper:
  sourceVisible := route_visibility_iff_source_visibility hvisible
  with no lambda cutoff ownership

lambda-only wrapper:
  lambdaCut := hdata.lambdaCut
  with no route/source atom identity

package endpoint:
  restrictedData comes from package exact support only

helper-only theorem:
  bridge theorem exists, but restrictedArithmeticData still uses the old path
```


## 7. Implementation Route

### Step B4.1: Pin Types

```lean
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.RouteTheorem

#check CCM25Concrete.PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport.support_visibility_iff_common_visibility
#check CCM25Concrete.PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport.route_visibility_iff_common_visible_atom_data
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#check normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#check Route.normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

### Step B4.2: Add Or Expose The Atom-In-Cutoff Owner

Preferred owner shape:

```text
VisibleAtomInLambdaCutoffData W common lambda n
  routeVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar common.sourceTest common.sourceTest)
  sourceVisible :
    common.toSourceTestEvaluationInterface.sourceAtomVisible n
  sourceArithmetic :
    SourceFinitePrimeArithmeticData W common.sourceTest common.sourceTest n
  lambdaCut :
    1 < n and (n : Real) <= lambda ^ 2
  restrictedMem :
    n in W.restrictedPrimeIndexSet lambda
```

Use an existing theorem if it already carries this shape. Do not create a free
`Prop` that states the endpoint theorem.

### Step B4.3: Rewire Restricted Arithmetic Data

Move this path:

```text
restrictedArithmeticData.atIndex n hn
  -> supportData.restrictedIndexData n hn
  -> hvisible
  -> visibleData.atVisibleIndex n hvisible
```

to a path where the same owner proves source visibility, arithmetic atom data,
lambda cutoff, and restricted membership.


## 8. Static Rejection Scans

```text
rg -n "route_visibility_iff_source_visibility|sourceAtomVisible|lambdaCut := hdata\\.lambdaCut|restrictedIndexData n hn|supportData\\.restrictedIndexData|restrictedArithmeticData|toSupportBoundary" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route -g "*.lean"

rg -n "VisibleAtomInLambda|visibleAtomsInLambdaCut|support_visibility_iff_common_visibility|route_visibility_iff_common_visible_atom_data|restrictedExact|normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary|normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route -g "*.lean"
```


## 9. WSL Build Gate

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem'
```


## 10. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.RouteTheorem

open ConnesWeilRH
open ConnesWeilRH.Source

#print axioms CCM25Concrete.PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport.support_visibility_iff_common_visibility
#print axioms CCM25Concrete.PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport.route_visibility_iff_common_visible_atom_data
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.visible
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.sourcePrimePowerIndex
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#print axioms normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#print axioms Route.normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

If a new owner replaces the tentative names, audit that owner instead.


## 11. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact visibility and lambdaCut copy path removed or demoted>

New semantic owner:
  <exact visible-atom-in-lambda-cutoff declaration>

Semantic theorem:
  <exact theorem proving route-visible atom + cutoff -> same source arithmetic
   atom in restricted index set>

Consumer rewires:
  <exact restrictedArithmeticData / S2B1 / Route declarations>

Semantic sufficiency:
  The restricted scalar now sums over the same route-visible atoms that the
  route later reasons about, with lambda cutoff membership attached to the
  same n.

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

Stop and mark B4 partial if the only available theorem bridges visibility but
cannot carry the lambda cutoff into the restricted evaluator consumer.

Do not solve B4 with copied `lambdaCut`, `True`, `Set.univ`, a free visibility
`Prop`, or a package endpoint.
