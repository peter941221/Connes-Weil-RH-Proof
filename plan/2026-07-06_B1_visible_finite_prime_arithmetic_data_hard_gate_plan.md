# B1 Visible Finite-Prime Arithmetic Data Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane B1.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

B1 is solved only when the active finite-prime source path gets visible
arithmetic atoms from a source-Weil-form owner or a lower non-free owner, then
a real package or route consumer uses that owner.

```text
old weak path:
  FixedLambdaArithmeticCertificateSourceTestData.visibleArithmeticData
    -> SourceVisibleFinitePrimeArithmeticData.atVisibleIndex
    -> arbitrary sourceTest.sourceAtomVisible n
    -> certificate/source-test package consumers

new semantic owner/API:
  FixedLambdaSourceWeilFormVisibleArithmeticData
    -> FixedLambdaSourceWeilFormVisibleArithmeticData.toSourceEvaluationVisibleArithmeticData
    -> SourceEvaluationVisibleFinitePrimeBoundary.ofSourceWeilForm
    -> SourceEvaluationVisibleFinitePrimeBoundary.visibleDataOfSourceWeilForm
    -> SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
       / restrictedArithmeticData

permitted bridge, not final owner:
  FixedLambdaSourceEvaluationVisibleArithmeticData may appear only when its
  fields are supplied by FixedLambdaSourceWeilFormVisibleArithmeticData or a
  lower non-free owner. It is not enough as the final semantic owner because
  it stores sourcePrimePowerIndex / visible / read-off rows as fields.

real consumer rewired:
  SourceEvaluationVisibleFinitePrimeBoundary.visibleData
  SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
  route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
  final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package

same-object alias / wrapper rejection scan:
  rg -n "SourceVisibleFinitePrimeArithmeticData\\.ofGlobalNormalization|visibleArithmeticData := object\\.visibleArithmeticData|visibleArithmeticData := data\\.visibleArithmeticData|object\\.certificate\\.atomsWithSourceTest|atomsWithSourceTest|h\\.certificate\\.atoms\\.atIndex|certificate\\.atoms|FixedLambdaFinitePrimeConcreteObject\\.atomData|FixedLambdaFinitePrimeConcreteObject\\.localFormulaData|sourceAtomVisible.*:=.*True|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge \
    ConnesWeilRH.Source.ObjectExpandedRows \
    ConnesWeilRH.Source.S2B1TraceScale \
    ConnesWeilRH.Route.TraceFrontEnd

focused axiom audit targets:
  FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData
  FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData_atVisibleIndex
  FixedLambdaSourceEvaluationVisibleArithmeticData.pairing_formula
  FixedLambdaSourceWeilFormVisibleArithmeticData.toSourceEvaluationVisibleArithmeticData
  SourceEvaluationVisibleFinitePrimeBoundary.ofSourceWeilForm
  SourceEvaluationVisibleFinitePrimeBoundary.visibleDataOfSourceWeilForm
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData_sourceVisibleArithmeticData
  SourceEvaluationVisibleFinitePrimeBoundary.visibleData
  SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
  route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package

semantic sufficiency for next route/RH step:
  The route-facing scoped restricted formula must read finite-prime atoms from
  source-visible data tied to source evaluation. It must not obtain them from a
  free certificate atom family or a bare visibility predicate.
```

Rejected as not solved:

```text
1. The patch only proves another theorem around
     SourceVisibleFinitePrimeArithmeticData.atVisibleIndex.

2. The active consumer still fills visibleArithmeticData from
     object.visibleArithmeticData
     certificate.atoms
     object.certificate.atomsWithSourceTest
     h.certificate.atoms.atIndex
     SourceVisibleFinitePrimeArithmeticData.ofGlobalNormalization

3. The proof path treats `sourceAtomVisible n` as a free enough input without
   showing how the atom data comes from source evaluation.

4. Route/TraceFrontEnd still reaches the finite-prime sum through package atoms
   instead of SourceEvaluationVisibleFinitePrimeBoundary.

5. FixedLambdaSourceEvaluationVisibleArithmeticData is the last owner on the
   accepted path, with arbitrary read-off fields supplied directly by the
   caller rather than by SourceWeilFormData or a lower non-free owner.
```


## 2. Result First

Expected result:

```text
Good:
  B1 rewires one real source/package/route consumer to visible arithmetic data
  built from SourceEvaluationData or SourceWeilFormData.

Partial:
  B1 adds source-evaluation visible data but no route or package consumer uses
  it.

Rejected:
  B1 only wraps atVisibleIndex or copies certificate atoms into a new record.
```

B1 is the finite-prime atom-data gate. It is not an invitation to add local
projection theorems around the same visible atom record.


## 3. Current Evidence

Root map evidence:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:116-120
  B1. visible finite-prime arithmetic data
    SourceVisibleFinitePrimeArithmeticData.atVisibleIndex
    SourceEvaluationVisibleFinitePrimeBoundary
    FixedLambdaArithmeticCertificateSourceTestData consumer
```

Current weak atom owner:

```text
ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean:329-335
  structure SourceVisibleFinitePrimeArithmeticData ... where
    atVisibleIndex :
      forall n, sourceTest.sourceAtomVisible n ->
        SourceFinitePrimeArithmeticData W f g n
```

Current certificate consumer:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:184-209
  FixedLambdaArithmeticCertificateSourceTestData stores:
    routeVisibleGlobalIndex
    routeVisibleRestrictedIndex
    visibleArithmeticData
    atoms
```

Current lower source-evaluation bridge:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean:68-81
  FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData
  builds SourceVisibleFinitePrimeArithmeticData via
  SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean:25-64
  FixedLambdaSourceEvaluationVisibleArithmeticData stores sourcePrimePowerIndex,
  visible, pairingReadOff, weightReadOff, and termReadOff as fields. Treat it
  as a bridge unless those fields come from FixedLambdaSourceWeilFormVisibleArithmeticData
  or a lower non-free owner.

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean:336-366
  FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData
  can consume source-evaluation visible data and supportData.
```

Current object boundary:

```text
ConnesWeilRH/Source/ObjectExpandedRows.lean:451-459
  SourceEvaluationVisibleFinitePrimeBoundary carries sourceWeilForm and
  sourceSymbols_eq.

ConnesWeilRH/Source/ObjectExpandedRows.lean:589-636
  globalArithmeticData and restrictedArithmeticData read boundary.visibleData.
```

Current route-facing S2-B1 consumer:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:733-759
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary consumes
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData.

ConnesWeilRH/Route/TraceFrontEnd.lean:8415-8456
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
  is the route-facing scoped normal-form consumer.

ConnesWeilRH/Route/RouteTheorem.lean:2607
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
  builds the route certificate from the source-Weil-form boundary.

ConnesWeilRH/Route/RouteTheorem.lean:2688
  route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
  is the route package entrypoint above the source-Weil-form boundary.

ConnesWeilRH/Route/RouteTheorem.lean:4130
  final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package
  is the final route-facing source-Weil-form boundary consumer.
```


## 4. First-Principles Dependency Chain

```text
source evaluation at prime-power points
  |
  v
SourceFinitePrimeArithmeticData.ofSourceEvaluationData
  |
  v
SourceVisibleFinitePrimeArithmeticData.atVisibleIndex
  |
  v
FixedLambdaArithmeticCertificateSourceTestData
  |
  v
SourceEvaluationVisibleFinitePrimeBoundary
  |
  v
ScopedRestrictedArchimedeanFormula
  |
  v
normalized source no-defect route consumer
```

The old path allows a certificate to hand over visible atom data. The hard gate
requires the visible atom to be tied to source evaluation before the route uses
it.


## 5. What Counts As Solved

All items below must hold in the same final snapshot.

```text
1. A named source-Weil-form visible-data owner, or a lower non-free owner,
   supplies SourceVisibleFinitePrimeArithmeticData. A bare
   FixedLambdaSourceEvaluationVisibleArithmeticData owner counts only as a
   bridge because it stores read-off rows as fields.

2. FixedLambdaArithmeticCertificateSourceTestData uses that owner through
   ofSourceEvaluationVisibleData or ofSourceWeilFormVisibleData.

3. SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData and
   restrictedArithmeticData read the new owner, not certificate atoms.

4. A real downstream theorem, at minimum
   normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary or a
   TraceFrontEnd theorem above it, follows the new path.

5. The focused axiom audit shows no sorryAx, project-local axiom, hidden
   theorem-source axiom, free Prop field, endpoint package theorem, constant,
   opaque, or unsafe dependency.
```


## 6. What Does Not Count

Do not accept these shapes:

```text
visible-data wrapper:
  newVisibleData.atVisibleIndex n hn := oldVisibleData.atVisibleIndex n hn

certificate copy:
  visibleArithmeticData := object.visibleArithmeticData

global-normalization shortcut:
  SourceVisibleFinitePrimeArithmeticData.ofGlobalNormalization
  with no source-evaluation owner used by the route

free source-evaluation owner:
  FixedLambdaSourceEvaluationVisibleArithmeticData supplied directly by caller
  fields, with no SourceWeilFormData theorem or lower owner behind those fields

old atom endpoint:
  FixedLambdaFinitePrimeConcreteObject.atomData n := h.certificate.atoms.atIndex n

route-invisible helper:
  a clean theorem about atVisibleIndex with no consumer rewired
```


## 7. Implementation Route

### Step B1.1: Pin Types

Use a scratch Lean file:

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.TraceFrontEnd

#check CCM25Concrete.PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData
#check CCM25Concrete.PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData
#check CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.visibleData
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#check normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#check normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

Do not leave scratch checks in accepted code.

### Step B1.2: Rewire The Boundary Owner

Change the active object/package path so this owner supplies visible arithmetic:

```text
FixedLambdaSourceWeilFormVisibleArithmeticData
  -> toSourceEvaluationVisibleArithmeticData
  -> visibleArithmeticData
  -> FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData
```

Do not stop at `FixedLambdaSourceEvaluationVisibleArithmeticData` unless a
separate lower theorem supplies each stored field. Otherwise the patch only
moves free read-off assumptions into a new record.

Keep older constructors only as compatibility if no active route consumer uses
them.

### Step B1.3: Rewire A Real Consumer

Use one of these consumers:

```text
SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package
```

If no consumer moves, mark B1 prep-only.


## 8. Static Rejection Scans

Run these after editing:

```text
rg -n "SourceVisibleFinitePrimeArithmeticData\\.ofGlobalNormalization|visibleArithmeticData := object\\.visibleArithmeticData|visibleArithmeticData := data\\.visibleArithmeticData|object\\.certificate\\.atomsWithSourceTest|atomsWithSourceTest|h\\.certificate\\.atoms\\.atIndex|certificate\\.atoms|FixedLambdaFinitePrimeConcreteObject\\.atomData|FixedLambdaFinitePrimeConcreteObject\\.localFormulaData" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "SourceEvaluationVisibleFinitePrimeBoundary|ofSourceEvaluationVisibleData|ofSourceWeilFormVisibleData|visibleArithmeticData_atVisibleIndex|route_certificate_of_normalized_source_weil_form_boundary|final_rh_of_normalized_source_weil_form_boundary|normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route/TraceFrontEnd.lean -g "*.lean"
```

The first scan may find compatibility paths. The acceptance report must state
which hits are active and which are compatibility-only.


## 9. WSL Build Gate

Sync:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'
```

Build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Route.TraceFrontEnd'
```

This build is necessary. It does not prove B1 solved unless the semantic gate
above also passes.


## 10. Focused Axiom Audit

Scratch file:

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.TraceFrontEnd

open ConnesWeilRH
open ConnesWeilRH.Source

#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceEvaluationVisibleArithmeticData.visibleArithmeticData_atVisibleIndex
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceEvaluationVisibleArithmeticData.pairing_formula
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData.toSourceEvaluationVisibleArithmeticData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.ofSourceWeilForm
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.visibleDataOfSourceWeilForm
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleData
#print axioms CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData.ofSourceWeilFormVisibleData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.visibleData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#print axioms normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#print axioms normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
#print axioms Route.route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
#print axioms Route.route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
```

Accepted output:

```text
[propext, Classical.choice, Quot.sound]
```

The three FixedLambdaSourceEvaluationVisibleArithmeticData audit targets are
bridge checks only. They do not prove B1 solved unless the accepted path also
shows that those fields come from FixedLambdaSourceWeilFormVisibleArithmeticData
or a lower non-free owner, and a named route/source consumer uses that path.


## 11. Final Acceptance Text

Use this shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact visibleArithmeticData / certificate atom path removed or demoted>

New semantic owner:
  <exact source-Weil-form visible-data declaration, or lower non-free owner>

Semantic theorem:
  <exact theorem tying atVisibleIndex to SourceEvaluationData / SourceWeilFormData>

Consumer rewires:
  <exact boundary/package/route declarations>

Semantic sufficiency:
  The scoped restricted formula now receives finite-prime atoms from source
  evaluation, not from free certificate atom data.

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

Stop and mark B1 partial if the only buildable change leaves the route on
certificate atoms, `atomsWithSourceTest`,
`SourceVisibleFinitePrimeArithmeticData.ofGlobalNormalization`, or a directly
filled `FixedLambdaSourceEvaluationVisibleArithmeticData` whose fields are not
derived from SourceWeilFormData or a lower non-free owner.

Do not replace source-visible arithmetic data with `True`, `Set.univ`, a free
`Prop`, or an endpoint package theorem.
