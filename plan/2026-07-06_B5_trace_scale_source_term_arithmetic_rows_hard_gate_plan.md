# B5 Trace-Scale Source-Term Arithmetic Rows Hard-Gate Plan

Date: 2026-07-06

Scope: `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lane B5.

Status: planning only. This file is ignored by Git through `plan/`.


## 1. Hard Completion Gate

B5 is solved only when the normalized source no-defect trace reaches the
scoped restricted source formula through concrete source-term arithmetic rows,
not through a package equality, a nonnegativity-matched synthetic trace scale,
or a free scalar-identification field.

```text
old weak path:
  NormalizedSeedRestrictedEvaluatorScalarIdentification.traceAmplitudeSquare_eq_restrictedEvaluator
    -> NormalizedSeedQWLambdaScalarIdentification.traceAmplitudeSquare_eq_qwLambda
    -> normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula
    -> normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows

new semantic owner/API:
  SourceArchimedeanTermData / SourceWeilFormData archimedean owner
  SourceEvaluationData.valueAt source-evaluation owner
  SourceEvaluationVisibleFinitePrimeBoundary restricted finite-prime data
  ScopedRestrictedArchimedeanFormula source-term owner:
    archimedeanTerm + polePairing - restricted finite-prime evaluator sum

real consumer rewired:
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  normalized_seed_source_no_defect_trace_eq_source_scoped_restricted_formula_of_boundary_rows
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
  Route.Bridge scoped restricted formula consumers

same-object alias / wrapper rejection scan:
  rg -n "traceAmplitudeSquare_eq_restrictedEvaluator|traceAmplitudeSquare_eq_qwLambda|normalizedSeedMatchedToCCM25Evaluator|h_nonneg|ScopedRestrictedArchimedeanFormula|source_common_restricted_finite_prime_evaluator_scoped_sum|source_restricted_finite_prime_evaluator_scoped_sum|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.S2B1TraceScale \
    ConnesWeilRH.Source.ObjectExpandedRows \
    ConnesWeilRH.Route.TraceFrontEnd \
    ConnesWeilRH.Route.Bridge

focused axiom audit targets:
  SourceArchimedeanTermData.archimedeanTerm_convolutionStar
  SourceScopedRestrictedArchimedeanFormula
  SourceScopedArchimedeanContributionBalance
  SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
  normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
  normalized_seed_source_no_defect_trace_eq_source_scoped_restricted_formula_of_boundary_rows
  normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula_of_boundary_rows
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows

semantic sufficiency for next route/RH step:
  The route needs the normalized no-defect trace to equal the source restricted
  formula with the actual archimedean term, pole pairing, and restricted
  finite-prime evaluator sum. A scalar field that states this equality does not
  close the trace-scale/source-term row.
```

Rejected as not solved:

```text
1. The patch only adds a wrapper around
     traceAmplitudeSquare_eq_restrictedEvaluator
     traceAmplitudeSquare_eq_qwLambda

2. The proof constructs normalizedSeedMatchedToCCM25Evaluator from an assumed
   nonnegativity row and treats that synthetic trace scale as the real source
   term.

3. The route still uses package formula equality as the active source-term
   owner.

4. The proof reintroduces `SourceEvaluationData.valueAt` as a record field or
   restores old theorem-source fields.
```


## 2. Result First

Expected result:

```text
Good:
  B5 rewires a route-facing normalized source no-defect consumer to concrete
  source-term arithmetic rows under the scoped restricted formula.

Partial:
  B5 proves a source-term read-off but leaves the route consumer on scalar
  identification fields.

Rejected:
  B5 wraps package formulas, matched synthetic trace scales, or free scalar
  identification fields.
```


## 3. Current Evidence

Root map evidence:

```text
01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md:140-145
  B5. trace-scale / source-term arithmetic rows
    SourceWeilFormData.archimedeanTerm
    SourceEvaluationData.valueAt
    ScopedRestrictedArchimedeanFormula source term
    normalized source no-defect formula consumer
```

Project rule evidence:

```text
AGENTS.md:934-948
  Future trace-scale work should drill below ScopedRestrictedArchimedeanFormula:
    SourceWeilFormData.archimedeanTerm
    FinitePrimeSourceData.visibleIff
    FinitePrimeSourceData.globalExact
    FinitePrimeSourceData.restrictedExact
    FinitePrimeSourceData.visibleAtomsInLambdaCut
```

Current source formula:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:25-33
  SourceScopedRestrictedArchimedeanFormula W f lambda restrictedData :=
    W.archimedeanTerm (W.convolutionStar f f) +
    W.polePairing f -
    MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet ...

ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:55-80
  SourceArchimedeanTermData stores and reads back W.archimedeanTerm.
```

Current package formula:

```text
ConnesWeilRH/Source/CCM25Concrete/Package.lean:357-391
  ScopedRestrictedArchimedeanFormula is the package formula.
  qwLambda_eq_scopedRestrictedArchimedeanFormula_of_package bridges QW_lambda.
```

Current S2-B1 scalar-identification surface:

```text
ConnesWeilRH/Source/S2B1TraceScale.lean:861-896
  NormalizedSeedRestrictedEvaluatorScalarIdentification and
  NormalizedSeedQWLambdaScalarIdentification store scalar equalities.

ConnesWeilRH/Source/S2B1TraceScale.lean:1095-1117
  normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula
  uses scalar identification plus package formula equality.  B5 may keep this
  theorem as compatibility, but it cannot close the lane.
```

Current route consumer:

```text
ConnesWeilRH/Route/TraceFrontEnd.lean:8415-8456
  normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
  is the route-facing theorem-base consumer.
```

Source evaluation bottom rule:

```text
MEMORY.md
  SourceEvaluationData.valueAt E F x := norm (A.legacy.encode F x)
  Do not reintroduce SourceEvaluationData.valueAt as a record field.
```


## 4. First-Principles Dependency Chain

```text
normalized CC20 no-defect trace
  |
  v
actual support-square / trace-amplitude source scalar
  |
  v
source restricted formula:
  archimedeanTerm(convolutionStar f f)
  + polePairing f
  - restricted finite-prime evaluator sum
  |
  v
ScopedRestrictedArchimedeanFormula
  |
  v
route normalized source no-defect formula consumer
```

The old scalar-identification field can state the equality without proving the
source-term arithmetic rows. B5 forces the rows to become the owner of the
equality.


## 5. What Counts As Solved

All items below must hold.

```text
1. The active no-defect trace read-off uses concrete source-term rows:
     archimedeanTerm read-off
     polePairing read-off
     restricted finite-prime evaluator sum read-off
     SourceEvaluationData.valueAt-derived prime-power pairings

2. `normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows`
   or a route theorem above it no longer depends on a free scalar
   identification field as the active source-term proof.

3. Package `ScopedRestrictedArchimedeanFormula` remains only as a compatibility
   formula when the active owner is the source formula or a theorem proving the
   package formula equals the source formula from lower rows.

4. Focused axiom audit is clean for the formula owner and route consumer.
```


## 6. What Does Not Count

Reject:

```text
scalar field:
  traceAmplitudeSquare_eq_restrictedEvaluator is carried as a primitive field

synthetic trace scale:
  normalizedSeedMatchedToCCM25Evaluator builds the trace amplitude from the
  evaluator and then proves the equality by construction

package wrapper:
  source no-defect trace = Package.ScopedRestrictedArchimedeanFormula
  with no lower source formula rows

field restoration:
  SourceEvaluationData.valueAt, archimedeanTerm, qw, qwLambda, or psi restored
  as record fields to make the proof immediate
```


## 7. Implementation Route

### Step B5.1: Pin Types

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.TraceFrontEnd
import ConnesWeilRH.Route.Bridge

#check CCM25Concrete.FinitePrimeSourceData.SourceScopedRestrictedArchimedeanFormula
#check CCM25Concrete.FinitePrimeSourceData.SourceArchimedeanTermData.archimedeanTerm_convolutionStar
#check SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#check normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#check NormalizedSeedRestrictedEvaluatorScalarIdentification
#check NormalizedSeedQWLambdaScalarIdentification
#check normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

### Step B5.2: Make The Source Formula The Owner

Preferred owner path:

```text
SourceScopedRestrictedArchimedeanFormula
  uses:
    SourceArchimedeanTermData.archimedeanTerm_convolutionStar
    SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
    source finite-prime evaluator sum read-off
  proves:
    normalized source no-defect trace =
      SourceScopedRestrictedArchimedeanFormula ...
```

If package formula names remain, add a theorem that rewrites package formula to
source formula from lower rows. Do not leave the package formula as the only
active source-term owner.

Required new theorem names:

```text
normalized_seed_source_no_defect_trace_eq_source_scoped_restricted_formula_of_boundary_rows
  proves the normalized no-defect trace equals the source formula from:
    normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
    SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
    SourceArchimedeanTermData.archimedeanTerm_convolutionStar

normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula_of_boundary_rows
  is allowed only as the package/source formula compatibility bridge after the
  source-row theorem above exists.
```

### Step B5.3: Rewire Route Consumer

Target:

```text
normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

This theorem must consume the source formula row or a theorem derived from it.
If only helper theorems move, mark B5 partial.


## 8. Static Rejection Scans

```text
rg -n "traceAmplitudeSquare_eq_restrictedEvaluator|traceAmplitudeSquare_eq_qwLambda|normalizedSeedMatchedToCCM25Evaluator|h_nonneg|ScopedRestrictedArchimedeanFormula|SourceScopedRestrictedArchimedeanFormula|source_common_restricted_finite_prime_evaluator_scoped_sum" ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Route -g "*.lean"

rg -n "structure SourceEvaluationData|valueAt .*where|mellinAt .*where|archimedeanTermReadOff|SourceArchimedeanTermData|restrictedArithmeticData|normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows" ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b|\\bTrue\\b|Set\\.univ" ConnesWeilRH/Source/CCM25Concrete ConnesWeilRH/Source/ObjectExpandedRows.lean ConnesWeilRH/Source/S2B1TraceScale.lean ConnesWeilRH/Route -g "*.lean"
```


## 9. WSL Build Gate

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Source.S2B1TraceScale ConnesWeilRH.Source.ObjectExpandedRows ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.Bridge'
```


## 10. Focused Axiom Audit

```lean
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.ObjectExpandedRows
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Route.TraceFrontEnd
import ConnesWeilRH.Route.Bridge

open ConnesWeilRH
open ConnesWeilRH.Source

#print axioms CCM25Concrete.FinitePrimeSourceData.SourceArchimedeanTermData.archimedeanTerm_convolutionStar
#print axioms CCM25Concrete.FinitePrimeSourceData.SourceScopedRestrictedArchimedeanFormula
#print axioms CCM25Concrete.FinitePrimeSourceData.SourceScopedArchimedeanContributionBalance
#print axioms SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData
#print axioms normalized_seed_qw_lambda_source_evaluator_read_off_of_boundary
#print axioms normalized_seed_source_no_defect_trace_eq_source_scoped_restricted_formula_of_boundary_rows
#print axioms normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula_of_boundary_rows
#print axioms normalized_source_no_defect_reduces_to_scoped_normal_form_of_theorem_base_rows
```

Compatibility-only audit:

```lean
#print axioms normalized_seed_source_no_defect_trace_eq_restricted_formula_of_scalar_identification
#print axioms normalized_seed_source_no_defect_trace_eq_scopedRestrictedArchimedeanFormula
```

These two old scalar/package theorems may stay for callers that have not moved
yet.  They do not satisfy B5.  A final acceptance block must show that the
route-facing consumer no longer uses them as the active source-term proof.


## 11. Final Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact scalar-identification / package formula path removed or demoted>

New semantic owner:
  <exact source-term arithmetic row owner>

Semantic theorem:
  <exact theorem proving no-defect trace equals source scoped restricted
   formula from archimedean, pole, and restricted finite-prime rows>

Consumer rewires:
  <exact S2B1 / TraceFrontEnd / Route.Bridge declarations>

Semantic sufficiency:
  The route no-defect trace now reaches the finite-lambda source formula through
  lower source-term arithmetic rows, so the next restricted-to-full / ledger
  step can reason about actual terms rather than a stored scalar equality.

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

Stop and mark B5 partial if the only buildable change keeps the route-facing
consumer on `traceAmplitudeSquare_eq_restrictedEvaluator` or a package formula
with no lower source-term rows.

Do not reintroduce `SourceEvaluationData.valueAt`, `archimedeanTerm`, `qw`,
`qwLambda`, or `psi` as record fields. Do not solve B5 with a synthetic matched
trace scale, `True`, `Set.univ`, or a free scalar `Prop`.
