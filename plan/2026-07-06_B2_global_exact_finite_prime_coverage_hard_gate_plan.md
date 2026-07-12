# B2 Global Exact Finite-Prime Coverage Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane B2.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

B2 is solved only when the active global finite-prime coverage path derives
`n in W.globalPrimeIndexSet` from concrete source-visible prime-power data, and
a real source/package/route consumer stops depending on a raw
`routeVisibleGlobalIndex` field.

```text
old weak path:
  SourcePrimePowerArithmeticSupportSkeletonAtLambda.routeVisibleGlobalIndex
    -> SourcePrimePowerArithmeticSupportSkeletonAtLambda.globalExact
    -> FixedLambdaArithmeticCertificateSourceTestData.globalExact
    -> CCM25SourceModel.global_prime_index_coverage / routeVisibleGlobalIndex
    -> route finite-prime visibility consumers

new semantic owner/API:
  FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact
    using:
      SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_exact
      SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible
      ConcreteCommonSourceTest.route_visibility_iff_source_visibility
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
    may package this theorem into FixedLambdaCommonFinitePrimeSupportData, but
    the packaged globalExact counts only for instances built by this
    source-Weil-form boundary path.

real consumer rewired:
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  FixedLambdaCommonFinitePrimeSupportData.globalExact only when its concrete
    supportData instance comes from supportDataOfSourceWeilForm
  SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
  Package.global_exact_of_package_exact_support
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
  route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
  final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package

same-object alias / wrapper rejection scan:
  rg -n "routeVisibleGlobalIndex :=|\\.routeVisibleGlobalIndex|support\\.routeVisibleGlobalIndex|object\\.certificate\\.support\\.routeVisibleGlobalIndex|exact_support_of_package.*globalExact|globalExact.*:=.*\\.globalExact|FixedLambdaCommonFinitePrimeSupportData\\.globalExact|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge \
    ConnesWeilRH.Source.ObjectExpandedRows \
    ConnesWeilRH.Source.S2B1TraceScale \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact
  FixedLambdaCommonFinitePrimeSupportData.globalExact
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  SourceEvaluationVisibleFinitePrimeBoundary.supportData
  SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
  Package.global_exact_of_package_exact_support
  common_finite_prime_concrete_object_global_index_data
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
  route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package

semantic sufficiency for next route/RH step:
  The route needs exact global finite-prime coverage so the global finite-prime
  evaluator sum indexes exactly the visible prime-power atoms. A raw
  `routeVisibleGlobalIndex` field only states the needed coverage again.
```

Rejected as not solved:

```text
1. The patch only proves:
     new_globalExact := old.globalExact

2. The active path still fills:
     routeVisibleGlobalIndex := support.routeVisibleGlobalIndex
     routeVisibleGlobalIndex := object.certificate.support.routeVisibleGlobalIndex

3. The proof reaches global coverage through package exact-support fields
   without exposing the source-Weil-form exact theorem.

4. The route consumer still depends on a raw global coverage field.

5. FixedLambdaCommonFinitePrimeSupportData.globalExact passes axiom audit, but
   the supportData instance was built from support.routeVisibleGlobalIndex,
   object.certificate.support.routeVisibleGlobalIndex, or any other copied raw
   routeVisibleGlobalIndex field instead of supportDataOfSourceWeilForm.
```


## 2. Result First

Expected result:

```text
Good:
  B2 removes or demotes one active raw routeVisibleGlobalIndex path and rewires
  the global coverage consumer to source-Weil-form exact support.

Partial:
  B2 proves source-Weil-form global exact coverage but no consumer moves.

Rejected:
  B2 only wraps a package/certificate exact-support theorem.
```


## 3. Current Evidence

Root map evidence:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:122-126
  B2. global exact finite-prime coverage
    SourcePrimePowerArithmeticSupportSkeletonAtLambda.globalExact
    CCM25SourceModel.global_prime_index_coverage
    routeVisibleGlobalIndex
```

Current support skeleton:

```text
ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:239-253
  SourcePrimePowerArithmeticSupportSkeletonAtLambda stores
  routeVisibleGlobalIndex as a field.

ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:289-299
  globalExact uses routeVisibleGlobalIndex in the reverse direction.
```

Current certificate source data:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:184-194
  FixedLambdaArithmeticCertificateSourceTestData stores
  routeVisibleGlobalIndex.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:224-237
  FixedLambdaArithmeticCertificateSourceTestData.globalExact uses that field.
```

Current lower source-Weil-form theorem:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean:131-160
  FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact proves global
  exactness from SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_exact
  and toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible.
```

Current object boundary:

```text
ConnesWeilRH/Source/ObjectExpandedRows.lean:463-508
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  currently constructs globalIndexData and routeVisibleGlobalIndex for the
  boundary support data.
```


## 4. First-Principles Dependency Chain

```text
SourceWeilFormData exact global index theorem
  |
  +-- n in globalPrimeIndexSet
  |     <-> IsPrimePow n and finitePrimeAtomVisible n sourceTest
  |
  v
Concrete common source-test visibility bridge
  |
  v
FixedLambdaCommonFinitePrimeSupportData.globalExact
  |
  v
global arithmetic data on the exact index set
  |
  v
global finite-prime evaluator sum in route/source formulas
```

The old chain inserts a raw field:

```text
finitePrimeAtomVisible n
  -> routeVisibleGlobalIndex n
  -> n in globalPrimeIndexSet
```

That raw field must stop being the active proof source.


## 5. What Counts As Solved

All items below must hold.

```text
1. A named source-Weil-form exact theorem supplies the global reverse
   direction:
     visible prime-power atom -> n in W.globalPrimeIndexSet.

2. At least one active consumer no longer reads routeVisibleGlobalIndex from
   SourcePrimePowerArithmeticSupportSkeletonAtLambda,
   FixedLambdaArithmeticCertificateSourceTestData, package exact support, or
   object.certificate.support.

3. SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData or a named
   RouteTheorem source-Weil-form boundary declaration uses the new global
   coverage path.

4. Compatibility fields may remain only if scans show they do not feed the
   active route/source B2 consumer.

5. Any accepted use of FixedLambdaCommonFinitePrimeSupportData.globalExact names
   the concrete supportData producer. If that producer is not
   SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm or a
   lower non-free equivalent, the use is only compatibility.
```


## 6. What Does Not Count

Reject these shapes:

```text
wrapper:
  theorem globalExact_new := old.globalExact

field move:
  routeVisibleGlobalIndex copied from one record into another record

package endpoint:
  Package.global_exact_of_package_exact_support used as the only proof

generic support wrapper:
  FixedLambdaCommonFinitePrimeSupportData.globalExact audited without proving
  that its supportData instance comes from supportDataOfSourceWeilForm or a
  lower non-free source-Weil-form owner

local clean theorem:
  source-Weil-form exactness passes audit, but no consumer leaves the old
  routeVisibleGlobalIndex path
```


## 7. Implementation Route

### Step B2.1: Pin Types

Scratch checks:

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Route.RouteTheorem

#check CCM25Concrete.PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda.globalExact
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData.globalExact
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
#check CCM25Concrete.Package.global_exact_of_package_exact_support
```

### Step B2.2: Move The Reverse Direction

Preferred route:

```text
FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact
  -> SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  -> FixedLambdaCommonFinitePrimeSupportData.globalExact on that exact instance
  -> SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
```

If the current API lacks an owner that can carry this without a raw field,
introduce the smallest owner under `FinitePrimeSourceDataBridge.lean`. Do not
put analytic bridge imports into `FinitePrimeSourceData.lean`.

Do not accept a generic `FixedLambdaCommonFinitePrimeSupportData.globalExact`
call unless the proof term shows which supportData instance it uses. In this
lane, the accepted instance must come from
`SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm` or a
lower non-free equivalent.

### Step B2.3: Rewire One Consumer

Use one of these consumers:

```text
SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
common_finite_prime_concrete_object_global_index_data
Package.global_exact_of_package_exact_support
route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package
```

If the consumer is package-facing, keep the package theorem as compatibility
and make the active proof use the source-Weil-form exact owner.


## 8. Static Rejection Scans

```text
rg -n "routeVisibleGlobalIndex :=|\\.routeVisibleGlobalIndex|object\\.certificate\\.support\\.routeVisibleGlobalIndex|support\\.routeVisibleGlobalIndex|FixedLambdaCommonFinitePrimeSupportData\\.globalExact|SourcePrimePowerArithmeticSupportSkeletonAtLambda\\.globalExact" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Route -g "*.lean"

rg -n "toWeilFormSymbols_globalPrimeIndex_exact|toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible|FixedLambdaSourceWeilFormVisibleArithmeticData\\.globalExact|supportDataOfSourceWeilForm|globalArithmeticData|common_finite_prime_concrete_object_global_index_data|route_certificate_of_normalized_source_weil_form_boundary|final_rh_of_normalized_source_weil_form_boundary" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Route -g "*.lean"
```

The first scan can report compatibility fields. The report must identify the
active path after the change.


## 9. WSL Build Gate

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Route.RouteTheorem'
```


## 10. Focused Axiom Audit

Scratch file:

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.RouteTheorem

open ConnesWeilRH
open ConnesWeilRH.Source

#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.globalExact
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData.globalExact
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
#print axioms CCM25Concrete.Package.global_exact_of_package_exact_support
#print axioms common_finite_prime_concrete_object_global_index_data
#print axioms Route.route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
#print axioms Route.route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

The FixedLambdaCommonFinitePrimeSupportData.globalExact audit target is a
wrapper check unless the acceptance report names the exact supportData producer.
For B2, the accepted producer must be
SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm or a
lower non-free equivalent.


## 11. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact routeVisibleGlobalIndex path removed or demoted>

New semantic owner:
  <exact source-Weil-form global exact declaration>

Semantic theorem:
  <exact theorem proving visible prime-power atom -> global index membership>

Consumer rewires:
  <exact support boundary / arithmetic data / route declarations>

Semantic sufficiency:
  The global finite-prime evaluator now indexes exactly the source-visible
  prime-power atoms through source-Weil-form exact support.

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

Stop and mark B2 partial if global exactness can only be proved by retaining a
raw `routeVisibleGlobalIndex` field on the active path, or if
`FixedLambdaCommonFinitePrimeSupportData.globalExact` is audited without
showing that the concrete supportData instance comes from
`SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm` or a
lower non-free equivalent.

Do not solve B2 with `True`, `Set.univ`, a copied package endpoint, or a free
coverage `Prop`.
