# B3 Restricted Exact Finite-Prime Coverage Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane B3.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

B3 is solved only when the route-facing restricted finite-prime coverage path
derives restricted index membership from source-visible prime-power data plus
the lambda cutoff, and the route consumer stops reading a certificate/package
`routeVisibleRestrictedIndex` field as its semantic source.

```text
old weak path:
  SourcePrimePowerArithmeticSupportSkeletonAtLambda.routeVisibleRestrictedIndex
    -> SourcePrimePowerArithmeticSupportSkeletonAtLambda.restrictedExact
    -> FixedLambdaArithmeticCertificateSourceTestData.restrictedExact
    -> FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
    -> Route.finite_prime_visibility_statement_of_source_backed
    -> Route.restricted_prime_index_covers_of_source_backed

new semantic owner/API:
  FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
    using:
      SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_exact
      SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible
      ConcreteCommonSourceTest.route_visibility_iff_source_visibility
      SourceLambdaCut lambda n = 1 < n and (n : Real) <= lambda ^ 2

real consumer rewired:
  FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
  Route.finite_prime_visibility_statement_of_source_backed
  Route.restricted_prime_index_covers_of_source_backed
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  FixedLambdaCommonFinitePrimeSupportData.restrictedExact
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData

same-object alias / wrapper rejection scan:
  rg -n "routeVisibleRestrictedIndex :=|\\.routeVisibleRestrictedIndex|visibility_at_lambda_of_certificate|finite_prime_visibility_statement_of_source_backed|restricted_prime_index_covers_of_source_backed|restrictedExact.*:=.*\\.restrictedExact|lambdaCut :=|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge \
    ConnesWeilRH.Source.ObjectExpandedRows \
    ConnesWeilRH.Source.S2B1TraceScale \
    ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
  Route.finite_prime_visibility_statement_of_source_backed
  Route.restricted_prime_index_covers_of_source_backed
  FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
  FixedLambdaCommonFinitePrimeSupportData.restrictedExact
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  SourceEvaluationVisibleFinitePrimeBoundary.supportData
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData

semantic sufficiency for next route/RH step:
  The route theorem needs restricted coverage for the same `QW_lambda` index
  set used by the finite-prime evaluator. A raw `routeVisibleRestrictedIndex`
  field only asserts the route statement; the replacement must expose the
  source-Weil-form proof that visible prime powers inside the cutoff belong to
  `W.restrictedPrimeIndexSet lambda`.
```

Rejected as not solved:

```text
1. The patch only proves:
     new_restrictedExact := old.restrictedExact

2. The active path still fills:
     routeVisibleRestrictedIndex := support.routeVisibleRestrictedIndex
     routeVisibleRestrictedIndex := object.certificate.support.routeVisibleRestrictedIndex

3. The lambda cutoff appears only as copied `hdata.lambdaCut` from a package or
   certificate object.

4. `Route.restricted_prime_index_covers_of_source_backed` still obtains
   restricted coverage through a certificate/package endpoint whose reverse
   direction reads `routeVisibleRestrictedIndex`.
```


## 2. Result First

Expected result:

```text
Good:
  B3 removes or demotes the active route restricted-coverage path through raw
  routeVisibleRestrictedIndex and rewires the route consumer to source-Weil-form
  exact support.

Partial:
  B3 proves source-Weil-form restricted exact coverage or improves
  restrictedArithmeticData, but `Route.restricted_prime_index_covers_of_source_backed`
  does not move.

Rejected:
  B3 only wraps a package/certificate restrictedExact theorem.
```


## 3. Current Evidence

Root map evidence:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:128-132
  B3. restricted exact finite-prime coverage
    SourcePrimePowerArithmeticSupportSkeletonAtLambda.restrictedExact
    CCM25SourceModel.restricted_prime_index_coverage
    routeVisibleRestrictedIndex
```

Current support skeleton:

```text
ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:254-262
  SourcePrimePowerArithmeticSupportSkeletonAtLambda stores
  routeVisibleRestrictedIndex.

ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean:300-310
  restrictedExact uses routeVisibleRestrictedIndex in the reverse direction.
```

Current certificate source data:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:195-203
  FixedLambdaArithmeticCertificateSourceTestData stores
  routeVisibleRestrictedIndex.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:239-253
  FixedLambdaArithmeticCertificateSourceTestData.restrictedExact uses that
  field and hdata.lambdaCut.
```

Current lower source-Weil-form theorem:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean:162-193
  FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact proves
  restricted exactness from SourceWeilFormData restricted-index exactness,
  source visibility, and lambdaCut.
```

Current S2-B1 consumer:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:733-759
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary consumes
  restrictedArithmeticData.
```

Current route consumer:

```text
ConnesWeilRH/Route/AdmissibleWindow.lean:43-49
  finite_prime_visibility_statement_of_source_backed builds the route statement
  from FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates.

ConnesWeilRH/Route/AdmissibleWindow.lean:58-65
  restricted_prime_index_covers_of_source_backed consumes
  finite_prime_visibility_statement_of_source_backed.restrictedPrimeIndexCoverage.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean:255-277
  finite_prime_visibility_of_common_source_test_certificates currently obtains
  restrictedPrimeIndexCoverage through a fixed-lambda arithmetic certificate.
```


## 4. First-Principles Dependency Chain

```text
source-visible prime-power atom
  |
  +-- IsPrimePow n
  +-- finitePrimeAtomVisible n sourceTest
  +-- 1 < n
  +-- (n : Real) <= lambda ^ 2
  |
  v
n in W.restrictedPrimeIndexSet lambda
  |
  v
SourceRestrictedFinitePrimeArithmeticData.atIndex
  |
  v
MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
  |
  v
ScopedRestrictedArchimedeanFormula
  |
  v
normalized source no-defect route consumer
```

The hard gate rejects any route where the lambda cutoff is only a copied field
with no source-Weil-form restricted-index proof behind it.


## 5. What Counts As Solved

All items below must hold.

```text
1. A named source-Weil-form exact theorem supplies:
     visible prime-power atom + 1 < n + (n : Real) <= lambda ^ 2
       -> n in W.restrictedPrimeIndexSet lambda.

2. The finite-prime visibility statement used by
   `Route.restricted_prime_index_covers_of_source_backed` stops reading
   `routeVisibleRestrictedIndex` from
   SourcePrimePowerArithmeticSupportSkeletonAtLambda,
   FixedLambdaArithmeticCertificateSourceTestData, package exact support,
   object.certificate.support, or certificate visibility-at-lambda endpoints.

3. The restricted arithmetic data that feeds
   MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet either follows the same
   owner or is documented as already source-Weil-form-backed and not the primary
   B3 route consumer.

4. Focused axioms stay clean.
```


## 6. What Does Not Count

Reject:

```text
wrapper:
  theorem restrictedExact_new := old.restrictedExact

lambda-copy path:
  lambdaCut := hdata.lambdaCut
  as the only evidence of the restricted cutoff

package endpoint:
  Package.restricted_exact_of_package_exact_support used as the only proof

source-only helper:
  source-Weil-form restricted exactness passes audit, but route/S2B1 still
  consumes the old restricted coverage path

evaluator-only move:
  restrictedArithmeticData improves, but Route.restricted_prime_index_covers_of_source_backed
  still reads the old certificate/package restricted coverage path
```


## 7. Implementation Route

### Step B3.1: Pin Types

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.RouteTheorem

#check CCM25Concrete.PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda.restrictedExact
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData.restrictedExact
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#check CCM25Concrete.FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
#check Route.finite_prime_visibility_statement_of_source_backed
#check Route.restricted_prime_index_covers_of_source_backed
#check normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
```

### Step B3.2: Move The Reverse Direction

Preferred route:

```text
FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
  -> FixedLambdaCommonFinitePrimeSupportData.ofSourceWeilForm or equivalent
  -> SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
  -> finite-prime visibility statement constructor used by Route.AdmissibleWindow
  -> Route.restricted_prime_index_covers_of_source_backed
```

Keep `FinitePrimeSourceData.lean` low-level. If an adapter is needed, put it in
`FinitePrimeSourceDataBridge.lean`.

### Step B3.3: Rewire One Consumer

The required consumer is:

```text
Route.restricted_prime_index_covers_of_source_backed
```

Secondary consumers can move in the same batch only if they follow the same
semantic owner:

```text
SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
Package.restricted_exact_of_package_exact_support as compatibility only
```


## 8. Static Rejection Scans

```text
rg -n "routeVisibleRestrictedIndex :=|\\.routeVisibleRestrictedIndex|object\\.certificate\\.support\\.routeVisibleRestrictedIndex|support\\.routeVisibleRestrictedIndex|visibility_at_lambda_of_certificate|lambdaCut := hdata\\.lambdaCut" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route -g "*.lean"

rg -n "toWeilFormSymbols_restrictedPrimeIndex_exact|toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible|FixedLambdaSourceWeilFormVisibleArithmeticData\\.restrictedExact|finite_prime_visibility_statement_of_source_backed|restricted_prime_index_covers_of_source_backed|restrictedArithmeticData|normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route -g "*.lean"
```


## 9. WSL Build Gate

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Route.RouteTheorem'
```


## 10. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.RouteTheorem

open ConnesWeilRH
open ConnesWeilRH.Source

#print axioms CCM25Concrete.FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
#print axioms Route.finite_prime_visibility_statement_of_source_backed
#print axioms Route.restricted_prime_index_covers_of_source_backed
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.restrictedExact
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData.restrictedExact
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.supportData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```


## 11. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact routeVisibleRestrictedIndex / certificate endpoint path removed or demoted>

New semantic owner:
  <exact source-Weil-form restricted exact declaration>

Semantic theorem:
  <exact theorem proving visible prime-power atom plus lambda cutoff ->
   restricted index membership>

Consumer rewires:
  <exact Route.AdmissibleWindow / finite-prime visibility statement declarations>

Semantic sufficiency:
  The route restricted coverage theorem now derives restricted membership for
  source-visible prime-power atoms inside the lambda cutoff from source-Weil-form
  exact support, not from a raw route coverage field.

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

Stop and mark B3 partial if route restricted coverage can only be proved by
retaining a raw `routeVisibleRestrictedIndex` field or certificate/package
endpoint on the active path.

Do not solve B3 with `True`, `Set.univ`, a copied lambda-cut field, or a free
restricted-coverage `Prop`.
