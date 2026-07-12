# D1 Final No-Argument RH Audit And Closure Plan

Date: 2026-07-07

Status: executable plan only. This file does not prove RH, remove `sorryAx`, or
count as Lean progress.

Scope:
  This plan covers the remaining D1 work after plans 03, 04, and 05. It does
  not reopen the deleted Root 1 / Root 2 all-test plans. It proves that those
  old roots are absent from the active no-argument RH route, or it rejects the
  final claim.


## 1. Result First

Current result:

```text
Rejected as solved.
```

## 2026-07-07 audit closeout after 04/05C

Result:
  Build-good, final no-sorry not closed.

Hard completion gate status:
  `lake build ConnesWeilRH.Source.AnalyticCore`:
    pass on a locked WSL ext4 verification copy at HEAD `667e6d5`.

  `lake build ConnesWeilRH`:
    pass on a locked WSL ext4 verification copy at HEAD `667e6d5`.

  `lake build ConnesWeilRH.Dev.UnconditionalSkeleton`:
    pass, but Lean reports the remaining explicit Dev `sorry` declarations.

Focused clean audit:
  The following route/CC20 sockets returned only `[propext, Classical.choice,
  Quot.sound]`:

  ```text
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
  Route.normalizedCC20_source_rh_of_finite_vanishing_rows
  Source.riemannZeta_half_ne_zero_of_full_lseries_cosZeta_half_period_abel_limit
  Source.cc20_triple_disjoint_of_full_lseries_cosZeta_half_period_abel_limit
  ```

Focused final audit:
  The final no-argument route still returns `[propext, sorryAx,
  Classical.choice, Quot.sound]` for:

  ```text
  Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
  Dev.UnconditionalSkeleton.unconditional_rh_skeleton
  Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
  ```

Active route components still carrying `sorryAx`:

```text
normalizedSourceObjectPackageFromTheorems
normalizedSourceBackedFixedSTestFromTheorems
normalizedRouteLedgersForRouteFromTheorems
normalizedRouteTraceDataFromTheorems
normalizedSignDefectClassificationForRouteFromTheorems
normalizedRouteFinalSignNonpositiveFromTheorems
```

First hard blocker:
  `normalizedCoreSourceWeilFormDataFromTheorems`.

Why it does not close from the current concrete support/window API:
  `SourceEvaluationData.sourceFinitePrimeTerm` is defined from arbitrary
  test-function values at `n` and `n⁻¹`.  The current concrete support/window
  data does not prove finite support for every `TestFunction`, so an empty or
  arbitrary support carrier would be a false closure.

Second hard blocker:
  the 05A half-period `cosZeta` Abel-boundary theorem.  The existing
  LSeries/cosZeta declarations are clean conditional sockets; they do not prove
  the boundary theorem needed for unconditional `ζ(1/2) ≠ 0`.

Rejected closure routes:
  Do not close the final RH outlet by `True`, `Set.univ`, raw `SourceRH`, raw
  `mathlibRH`, accepted-source theorem fields, empty finite support, arbitrary
  finite support, or a selected-route wrapper that stores the missing route
  rows as primitive Props.

Reason:

```text
The last recorded D1 audit still showed:

  normalizedRouteCertificateFromTheorems:
    [propext, sorryAx, Classical.choice, Quot.sound]

  unconditional_rh_skeleton:
    [propext, sorryAx, Classical.choice, Quot.sound]

  unconditional_rh_contract_skeleton:
    [propext, sorryAx, Classical.choice, Quot.sound]
```

Complete result required by this plan:

```text
Good only if:

  1. Plans 03, 04, and 05 have passed their own hard gates.

  2. The final no-argument route uses only those accepted producers and the
     already accepted finite-prime certificate-boundary route cut, both in
     proof rows and in the source-object package data carried by the final
     theorem.

  2A. If the current `SourceObjectPackage` / `RouteInputs.ofExpandedSourcePackage`
      route still imports all-test theorem-base data, Plan 06 itself performs
      the route API migration.  It does not defer that migration to a later
      plan.  The final accepted route must be able to consume selected
      route-facing data without carrying:
        SourceWeilFormData
        CommonFinitePrimeArithmeticSourceData for all tests
        normalizedSourceObjectCoreFinitePrimeExactFromTheorems
        normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
        normalizedCoreSourceWeilFormDataFromTheorems

  3. Old Root 1 and Root 2 remain compatibility-only or inactive:
        normalizedCoreSourceWeilFormDataFromTheorems
        normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

     The final theorem may not depend on either root through:
        normalizedCoreSourceModelConstructorCoreFromTheorems
        normalizedCoreCCM25SourceModelFromTheorems as a proof source
        normalizedSourceObjectCoreFinitePrimeExactFromTheorems
        SourceWeilFormData.toCCM25SourceModel
        CommonFinitePrimeArithmeticSourceData all-test package construction

  4. The fixed-test triple-vanishing row is clean because it is supplied by the
     accepted plan-05 CC20 RH-exit package, not by a new raw
     TripleVanishingStatement field.

  5. `#print axioms` for the final no-argument theorem targets contains no
     `sorryAx`, project-local axiom, `constant`, `opaque`, or `unsafe`.

  6. The no-argument package does not store `_root_.RiemannHypothesis` as an
     active field.  If `NormalizedNoArgumentRouteCertificatePackage.mathlibRH`
     remains for compatibility, final acceptance must ignore it and prove every
     no-argument RH outlet from the route certificate.

  7. The route-level final exit package also does not store Mathlib RH as an
     active field.  `RouteFinalExitPackage.mathlibRH` and
     `RouteFinalExitPackage.mathlibRHMatchesSourceBridge` must be removed or
     compatibility-only.  `mathlib_rh_of_route_final_exit_package` must compute
     Mathlib RH from `sourceRH` through `RHDefinitionBridge.source_rh_to_mathlib_rh`.
```

This plan is the final D1 closure gate:

```text
_root_.RiemannHypothesis
  <- unconditional_rh_skeleton
  <- routeCertificateFromTheorems
  <- normalizedRouteCertificateFromTheorems
  <- accepted plan 03 / 04 / 05 producers
  <- accepted certificate-boundary finite-prime route cut
  <- no active Root 1 / Root 2 all-test dependency
```


## 2. What Counts As Solved

Hard completion gate:

```text
old weak path:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4924-5076
    normalizedNoArgumentRouteCertificatePackageFromTheorems
    routeCertificateFromTheorems
    cc20FiniteVanishingExitFromTheorems
    rhDefinitionBridgeToMathlibFromTheorems
    unconditional_rh_skeleton
    unconditional_rh_contract_skeleton

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1506-1509
    normalizedSourceObjectCoreFinitePrimeExactFromTheorems still maps directly
    to normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems in the
    current tree.

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4802-4824
    NormalizedNoArgumentRouteCertificatePackage currently stores only
    routeCertificate and finalExitPackage, and
    mathlib_rh_of_normalized_no_argument_route_certificate_package derives
    Mathlib RH from the route certificate.  This shape is the required
    no-stored-Mathlib-RH invariant.

  ConnesWeilRH/Route/RouteTheorem.lean:1497-1545
    RouteFinalExitPackage currently stores sourceRH, not Mathlib RH, and
    mathlib_rh_of_route_final_exit_package derives Mathlib RH through
    RHDefinitionBridge.source_rh_to_mathlib_rh.  Plan 06 must preserve this
    shape as a regression gate.

  MEMORY.md:1044-1052
    final D1 audit still showed `sorryAx` for the route certificate and both
    no-argument RH theorem targets.

  MEMORY.md:1054-1066
    remaining producer roots included plan 03 roots, plan 04 roots, plan 05,
    fixed-test triple vanishing, and the old Root 1 / Root 2 names.

new semantic owner/API:
  Accepted plan 03 producers:
    source-order S2B1 / scalar semantic owners named by
    plan/03_2026-07-07_D1_s2b1_scalar_semantic_roots_hard_gate_plan.md.

  Accepted plan 04 producers:
    selected read-off / bridge APIs named by
    plan/04_2026-07-07_D1_readoff_bridge_roots_hard_gate_plan.md.

  Accepted plan 05 producer:
    Source.SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard,
    converted to the CC20 RH-exit package only after its lower fields are
    supplied by accepted facts.

  Already accepted finite-prime route cut:
    SourceObjectConcreteCommonData.CommonFinitePrimeCertificateBoundary
    SourceObjectConcreteCommonData.common_finite_prime_visibility_statement
    normalized_seed_qw_lambda_source_evaluator_read_off_of_certificate_boundary
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedCertificateBoundaryRowsFromContract
    route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff

  Plan 06 selected final-route API:
    NormalizedSelectedFinalRouteInput
    normalizedSelectedFinalRouteInputFromTheorems
    route_certificate_of_selected_final_route_input
    final_connes_weil_rh_of_selected_final_route_input

    These names are the intended API boundary.  Equivalent names are allowed
    only if they expose the same semantic cut: selected plan 03 / 04 / 05
    producers plus the certificate-boundary finite-prime route cut, with no
    all-test SourceWeilFormData or CommonFinitePrimeArithmeticSourceData field.

real consumer rewired:
  normalizedSourceObjectCoreFinitePrimeExactFromTheorems
  normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems
  normalizedSourceObjectTheoremBaseInputFromTheorems
  Source.sourceObjectPackageOfNormalizedCC20Trace
  RouteInputs.ofExpandedSourcePackage
  normalizedSelectedFinalRouteInputFromTheorems
  route_certificate_of_selected_final_route_input
  final_connes_weil_rh_of_selected_final_route_input
  normalizedFixedSTestTripleVanishingInputFromTheorems
  normalizedFixedSTestSourceInputFromTheorems
  normalizedFixedTestFromTheorems
  normalizedFixedDataFromTheorems
  normalizedSourceBackedFixedSTestFromTheorems
  normalizedTraceDataFromTheorems
  normalizedRouteCertificateFromTheorems
  normalizedNoArgumentRouteCertificatePackageFromTheorems
  routeCertificateFromTheorems
  route_final_exit_package_of_certificate
  mathlib_rh_of_route_final_exit_package
  route_final_exit_mathlib_rh_uses_source_bridge
  cc20FiniteVanishingExitFromTheorems
  rhDefinitionBridgeToMathlibFromTheorems
  unconditional_rh_skeleton
  unconditional_rh_contract_skeleton

same-object alias / wrapper rejection scan:
  rg -n "normalizedCoreSourceWeilFormDataFromTheorems|normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems|normalizedCoreSourceModelConstructorCoreFromTheorems|normalizedCoreCCM25SourceModelFromTheorems|SourceWeilFormData\\.toCCM25SourceModel|CommonFinitePrimeArithmeticSourceData|normalizedSourceObjectCoreFinitePrimeExactFromTheorems|NormalizedSourceObjectTheoremBaseInput|sourceObjectPackageOfNormalizedCC20Trace|RouteInputs\\.ofExpandedSourcePackage|finitePrimeExact\\s*:=|normalizedFixedSTestTripleVanishingInputFromTheorems|normalizedScalarFixedSTestTripleVanishingInputFromTheorems|TripleVanishingStatement\\s*:=|sourceTripleVanishing\\s*:=|mathlibRH\\s*:|\\.mathlibRH|SourceRH\\s*:=|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Route.FixedTestFrontEnd ConnesWeilRH.Route.RouteTheorem
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
  lake build ConnesWeilRH

focused axiom audit targets:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedSTestTripleVanishingInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedSTestSourceInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedTestFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedDataFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceBackedFixedSTestFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.routeCertificateFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton

semantic sufficiency for next route/RH step:
  There is no later D1 route step.  The final no-argument theorem itself must
  pass the axiom gate.  Proof-row closure is not enough: the final theorem's
  source-object package and carried data must also avoid the old Root 1 / Root
  2 constructors, and final RH must come from the route certificate rather than
  a stored `mathlibRH` field.
```

Solved means all of the following hold:

```text
1. Plans 03, 04, and 05 are accepted by their own final acceptance text.
2. `normalizedRouteCertificateFromTheorems` uses the accepted certificate-boundary
   route constructor and no old all-test finite-prime root as a proof source.
3. The final source-object package and theorem-base input no longer carry
   `normalizedSourceObjectCoreFinitePrimeExactFromTheorems` or
   `normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems` as active
   dependencies.
3A. If `normalizedSourceObjectPackageFromTheorems` or
   `Source.sourceObjectPackageOfNormalizedCC20Trace` still necessarily carries
   all-test `finitePrimeExact`, then the accepted final route is no longer
   built from that package.  It is built from the selected final-route input
   introduced by this plan.
4. Fixed-test triple vanishing comes through the accepted CC20 RH-exit source
   finite-vanishing package.
5. Old Root 1 and Root 2 may still exist as compatibility declarations, but the
   final no-argument audit does not depend on them.
6. `NormalizedNoArgumentRouteCertificatePackage.mathlibRH` is removed, or it
   remains only as a compatibility field that no acceptance theorem reads.
7. `RouteFinalExitPackage.mathlibRH` is removed, or it remains only as a
   compatibility field that no acceptance theorem reads.
8. The final `#print axioms` output contains no `sorryAx`.
```


## 3. What Does Not Count

Rejected:

```text
- treating old Root 1 or Root 2 as solved by filling them with an arbitrary
  finite set, `True`, `Set.univ`, endpoint package rows, source-object package
  projections, or a renamed raw Prop;
- reopening deleted plan 01 / plan 02 as required final work;
- claiming Root 1 / Root 2 are bypassed without a final route-certificate
  axiom audit;
- claiming Root 1 / Root 2 are bypassed because proof rows use the
  certificate-boundary route while the final source-object package still stores
  `finitePrimeExact` from the old all-test root;
- treating "the type still requires all-test data" as a reason to open a later
  plan.  For D1 final closure, Plan 06 must perform the selected final-route
  API migration itself or report the final RH route as rejected;
- keeping the final route on `Source.sourceObjectPackageOfNormalizedCC20Trace`
  or `RouteInputs.ofExpandedSourcePackage` if that package/input still unfolds
  through `NormalizedSourceObjectTheoremBaseInput.finitePrimeExact`;
- proving fixed-test triple vanishing from a new record that stores
  TripleVanishingStatement directly;
- proving final RH from a record field named `mathlibRH`;
- keeping `mathlibRH : _root_.RiemannHypothesis` as an active no-argument
  package payload and counting that package as final closure;
- keeping `RouteFinalExitPackage.mathlibRH` as an active route-level payload
  and counting `mathlib_rh_of_route_final_exit_package` as final closure;
- relying on `source_rh_to_mathlib_rh` before SourceRH has been produced by the
  accepted route certificate;
- leaving any final target with `[propext, sorryAx, Classical.choice, Quot.sound]`;
- using build success as a substitute for the final focused axiom audit.
```

Root 1 / Root 2 rule:

```text
The old all-test roots are not execution targets.

Accepted:
  prove they are absent from the active no-argument route.

Rejected:
  backfill them from weak all-test packages or count their presence as harmless
  without final dependency evidence.
```


## 4. Current Evidence

Plan and memory evidence:

```text
MEMORY.md:43-67
  plan 01 / 02 were removed.  The active route should be rewritten away from
  old all-test SourceWeilFormData / CommonFinitePrimeArithmeticSourceData roots.

MEMORY.md:990-1042
  the certificate-boundary finite-prime/QW_lambda route cut was accepted, and
  its focused route targets audited clean.

MEMORY.md:1044-1052
  final D1 audit still failed for normalizedRouteCertificateFromTheorems and
  both no-argument RH theorem targets.

MEMORY.md:1068-1071
  the certificate-boundary route is clean, but the Dev no-argument theorem still
  inherits upstream skeleton placeholders.
```

Lean evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1506-1509
  normalizedSourceObjectCoreFinitePrimeExactFromTheorems currently points to
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems.  This is a
  package/type-level old-root dependency, not merely a proof-row dependency.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2334-2354
  normalizedFixedSTestTripleVanishingInputFromTheorems currently takes the
  triple-vanishing statement from
  normalizedSourceObjectPackageFromTheorems.cc20RHExit.sourceFiniteVanishingCriterionPackage.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:2387-2415
  normalizedFixedDataFromTheorems builds FixedSTestObligationData for the
  selected normalized source package.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4889-4912
  normalizedRouteCertificateFromTheorems consumes normalizedTraceDataFromTheorems
  and the accepted certificate-boundary route constructor.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4932-5076
  the no-argument RH outlets all depend on normalizedRouteCertificateFromTheorems
  or routeCertificateFromTheorems.

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4802-4824
  NormalizedNoArgumentRouteCertificatePackage currently stores routeCertificate
  and finalExitPackage only.  Its Mathlib RH theorem is external and derives
  from cc20_source_rh_of_route_certificate plus
  RHDefinitionBridge.source_rh_to_mathlib_rh.

ConnesWeilRH/Route/RouteTheorem.lean:1497-1545
  RouteFinalExitPackage currently stores sourceRH, not Mathlib RH.  Its
  Mathlib RH theorem is external and derives from
  RHDefinitionBridge.source_rh_to_mathlib_rh.
```

Route evidence:

```text
ConnesWeilRH/Route/Definitions.lean:170-188
  SourceBackedTripleVanishingRouteRows turns a source triple-vanishing statement
  into the route fixed-test triple-vanishing row through an explicit bridge.

ConnesWeilRH/Route/FixedTestFrontEnd.lean:28-56
  FixedSTestObligationData stores source triple-vanishing evidence and the
  bridge to the fixed test.

ConnesWeilRH/Route/RouteTheorem.lean:43-63
  RouteBackedCC20TripleVanishingInputData is one input to the route-backed CC20
  exit package.
```


## 5. First-Principles Dependency Chain

The final theorem has only one acceptable proof shape:

```text
accepted source package
  -> no old finitePrimeExact / all-test Root 1 / Root 2 dependency
  -> accepted fixed-test obligation data
  -> accepted trace front-end data
  -> accepted route certificate
  -> SourceRH through cc20_source_rh_of_route_certificate
  -> Mathlib RiemannHypothesis through RHDefinitionBridge.standard
```

The final theorem must not use this shape:

```text
old skeleton root
  -> source/package projection
  -> old finitePrimeExact all-test root carried by the package
  -> route certificate builds
  -> final theorem still audits with sorryAx
```

Root 1 / Root 2 are handled by absence from the route, not by local closure:

```text
deleted old all-test root plan
  -> accepted certificate-boundary route cut
  -> final dependency audit proves no active use
```


## 6. Implementation Route

### Phase 0: lock prerequisites

Before editing this lane, verify plans 03, 04, and 05 have accepted final text.
Do not use their planned declarations until their build and axiom gates pass.

Required checks:

```text
rg -n "Result:|Good|rejected|sorryAx|unconditional_rh_skeleton" \
  plan/03_2026-07-07_D1_s2b1_scalar_semantic_roots_hard_gate_plan.md \
  plan/04_2026-07-07_D1_readoff_bridge_roots_hard_gate_plan.md \
  plan/05_2026-07-07_D1_cc20_rh_exit_object_package_hard_gate_plan.md
```

Prerequisite interpretation:

```text
Plan 03 accepted only if:
  normalizedRouteCertificateFromTheorems no longer depends on S2B1/scalar
  Prop roots named by plan 03.

Plan 04 accepted only if:
  normalizedRouteCertificateFromTheorems no longer depends on forall read-off
  row providers named by plan 04.

Plan 05 accepted only if:
  normalizedCoreCC20RHExitObjectPackageFromTheorems no longer uses `sorry` and
  its source package fields are supplied by lower accepted disjointness and
  source criterion theorems.  A partial black-box report is not accepted.

If any prerequisite is partial / blocked / rejected, stop.  Do not edit Plan 06
closure code.
```

### Phase 0A: declaration-level rewrite table

Use this table before editing.  Each row must end as accepted or blocked.

```text
declaration:
  normalizedCoreCC20RHExitObjectPackageFromTheorems

old dependency:
  `sorry`

required new dependency:
  normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems from Plan 05,
  converted by Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage.

accepted edit:
  replace the `by sorry` body with the Plan 05 direct-completion expression.

blocked if:
  Plan 05 only produced a first non-Mathlib black-box report.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems

---

declaration:
  normalizedSourceObjectCoreFinitePrimeExactFromTheorems

old dependency:
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

required new dependency:
  a selected common-test finite-prime owner accepted by the finite-prime
  route cut, not the all-test CommonFinitePrimeArithmeticSourceData root.

accepted edit:
  either remove this declaration from the final no-argument dependency chain,
  or replace its consumer with route-facing selected finite-prime data so the
  final theorem no longer requires CommonFinitePrimeArithmeticSourceData for
  all tests.

blocked if:
  NormalizedSourceObjectCoreTheoremBaseConstructorInput still requires
  finitePrimeExact : CommonFinitePrimeArithmeticSourceData
  base.ccm25Model.toWeilFormSymbols for the final theorem package.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreFinitePrimeExactFromTheorems

---

declaration:
  normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems

old dependency:
  finitePrimeExact := normalizedSourceObjectCoreFinitePrimeExactFromTheorems

required new dependency:
  a theorem-base constructor/API that does not require the all-test
  finitePrimeExact field for the final route, or a proof that this constructor
  is compatibility-only and absent from final no-argument theorem dependencies.

accepted edit:
  introduce/use a selected-route theorem-base input whose finite-prime data are
  the certificate-boundary objects consumed by normalizedRouteCertificateFromTheorems.

blocked if:
  the final route still passes through NormalizedSourceObjectTheoremBaseInput
  with data.core.finitePrimeExact.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems

---

declaration:
  normalizedSourceObjectTheoremBaseInputFromTheorems

old dependency:
  NormalizedSourceObjectTheoremBaseConstructorInput.toInput copies
  data.core.finitePrimeExact into input.finitePrimeExact.

required new dependency:
  selected final-route package/input that omits all-test finitePrimeExact, or a
  compatibility-only proof that final RH no longer imports this input.

accepted edit:
  move final route construction to the selected route-facing input and keep
  this declaration outside final no-argument audits.

blocked if:
  normalizedBaseFromTheorems, normalizedCommonFromTheorems,
  normalizedTraceDataFromTheorems, or normalizedRouteCertificateFromTheorems
  still unfold through normalizedSourceObjectTheoremBaseInputFromTheorems.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectTheoremBaseInputFromTheorems

---

declaration:
  normalizedNoArgumentRouteCertificatePackageFromTheorems

old dependency:
  a possible regression to
    NormalizedNoArgumentRouteCertificatePackage.mathlibRH :
      _root_.RiemannHypothesis

required new dependency:
  routeCertificate and finalExitPackage only, or a package whose RH theorem is
  a theorem outside the data structure.

accepted edit:
  preserve the current routeCertificate/finalExitPackage-only package shape and
  keep final accepted theorems reading the route certificate, not a stored RH
  field.

blocked if:
  any accepted final theorem reads `pkg.mathlibRH` or a stored
  `_root_.RiemannHypothesis` field.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems

---

declaration:
  unconditional_rh_skeleton
  unconditional_rh_contract_skeleton

old dependency:
  indirect old roots through the route certificate or stored RH package fields.

required new dependency:
  final_connes_weil_rh routeCertificateFromTheorems, or
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh applied to
  cc20_source_rh_of_route_certificate with no stored RH field.

accepted edit:
  keep theorem bodies certificate-derived and make their `#print axioms`
  output contain no `sorryAx`.

blocked if:
  either theorem audits with `sorryAx`, reaches Root 1 / Root 2, or reads a
  stored RH field.

audit target:
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
```

### Phase 1: validate the fixed-test triple-vanishing path

After plan 05 supplies the accepted CC20 RH-exit package, inspect:

```text
normalizedFixedSTestTripleVanishingInputFromTheorems
normalizedFixedSTestSourceInputFromTheorems
normalizedFixedTestFromTheorems
normalizedFixedDataFromTheorems
normalizedSourceBackedFixedSTestFromTheorems
```

The accepted path is:

```text
accepted SourceFiniteVanishingCriterionPackage
  -> triple_vanishing_statement_of_source_package
  -> FixedSTestObligationData.tripleVanishingSourceHolds
  -> SourceBackedTripleVanishingRouteRows
  -> route fixed-test triple vanishing
```

If this path still carries `sorryAx`, do not add a new triple-vanishing root.
Move the proof source back into plan 05's source finite-vanishing package.

### Phase 2: prove Root 1 / Root 2 are inactive

Run the static scans:

```text
rg -n "normalizedCoreSourceWeilFormDataFromTheorems|normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems|SourceWeilFormData\\.toCCM25SourceModel|CommonFinitePrimeArithmeticSourceData|normalizedSourceObjectCoreFinitePrimeExactFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"

rg -n "route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff|normalizedRouteCertificateFromTheorems|normalizedTraceDataFromTheorems|normalizedConcreteCommonFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"
```

Then read the proof bodies. The route certificate may mention
`normalizedBaseFromTheorems` as data, but it must not use old Root 1 / Root 2 as
the source for finite-prime/QW_lambda proof rows. Those rows must come from the
accepted certificate-boundary route cut.

Also inspect the package construction path:

```text
normalizedSourceObjectCoreFinitePrimeExactFromTheorems
normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems
normalizedSourceObjectCoreTheoremBaseDataFromTheorems
normalizedSourceObjectTheoremBaseInputFromTheorems
normalizedSourceObjectPackageFromTheorems
```

The final theorem fails this plan if that path still carries Root 1 or Root 2
into the no-argument target, even when the local route proof rows use the
certificate-boundary route cut.

Concrete current blocker path:

```text
normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
  -> normalizedSourceObjectCoreFinitePrimeExactFromTheorems
  -> normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems.finitePrimeExact
  -> normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact
  -> normalizedSourceObjectTheoremBaseConstructorInputFromTheorems.core
  -> normalizedSourceObjectTheoremBaseInputFromTheorems.finitePrimeExact
  -> normalizedBaseFromTheorems / normalizedCommonFromTheorems / normalizedTraceDataFromTheorems
  -> normalizedRouteCertificateFromTheorems
  -> unconditional_rh_skeleton
```

The accepted Plan 06 implementation must break this path before the final
audit.  Merely showing that
`route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff`
uses certificate-boundary proof rows does not break this path.

If the final axiom audit still reaches Root 1 or Root 2, perform one of these
actions:

```text
1. Rewire the exact declaration named in Phase 0A to a selected route-facing
   owner and record the old expression and new expression.
2. If the required type still asks for all-test SourceWeilFormData or
   CommonFinitePrimeArithmeticSourceData, perform the selected final-route API
   migration in Phase 2A of this plan.  Do not backfill old Root 1 / Root 2.
```

### Phase 2A: selected final-route API migration

This phase is mandatory when the current package route still forces the old
all-test theorem-base package.  It is not a separate future plan.

Why this is needed:

```text
Proof rows can be clean while the type still carries an old root.

That happens when:

  route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
    uses selected certificate-boundary rows

but:

  RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems
    still requires
      Source.sourceObjectPackageOfNormalizedCC20Trace
        <- NormalizedSourceObjectTheoremBaseInput.finitePrimeExact
        <- normalizedSourceObjectCoreFinitePrimeExactFromTheorems
        <- Root 2

The selected API must cut below the package layer, not only below one theorem
body.
```

Introduce a selected final-route input whose fields are the semantic owners
already accepted by plans 03, 04, and 05 plus the certificate-boundary
finite-prime route cut:

```lean
structure NormalizedSelectedFinalRouteInput where
  rhDefinitionBridge :
    Source.RHDefinitionBridge

  cc20Exit :
    Source.SourceObject.CC20RHExitObjectPackage

  fixedTest :
    FixedSTestObligationData
      -- selected fixed source/test data from plan 05

  traceFrontEnd :
    TraceFrontEndData
      -- selected read-off / bridge data from plan 04

  s2b1Scalar :
    -- accepted source-order S2B1 / scalar owner from plan 03
    Sort _

  certificateBoundary :
    SourceObjectConcreteCommonData.CommonFinitePrimeCertificateBoundary
      -- accepted finite-prime route cut owner

  noExtraBulk :
    -- accepted no-bulk / ledger evidence from plan 03
    Sort _

  ledgers :
    RouteLedgerClearingInputData

  restrictedToFull :
    -- accepted current-cutoff / restricted-to-full semantic owner
    Sort _
```

The exact field types should use the real names available after plans 03, 04,
and 05 land.  The important invariant is negative:

```text
NormalizedSelectedFinalRouteInput must not contain:

  SourceWeilFormData
  CommonFinitePrimeArithmeticSourceData
  normalizedSourceObjectCoreFinitePrimeExactFromTheorems
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
  normalizedCoreSourceWeilFormDataFromTheorems
  Source.sourceObjectPackageOfNormalizedCC20Trace as an active dependency
  RouteInputs.ofExpandedSourcePackage as an active dependency if it unfolds to
    the all-test package
```

Then add a route constructor over that selected input:

```lean
noncomputable def route_certificate_of_selected_final_route_input
    (input : NormalizedSelectedFinalRouteInput) :
    RouteCertificate (RouteInputs.ofSelectedFinalInput input) := by
  -- use the same semantic ingredients as the accepted certificate-boundary
  -- route cut, but read them from `input` instead of from the all-test
  -- source-object package.
  exact
    route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
      -- selected base/common/fixed/trace/ledger arguments from `input`
```

If `RouteInputs.ofSelectedFinalInput` does not exist, Plan 06 must introduce it
or an equivalent constructor.  It should expose only the route fields actually
used by `RouteCertificate`, `cc20_source_rh_of_route_certificate`, and
`final_connes_weil_rh`.  It must not be a wrapper around
`RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems`
unless that package has already been repaired to remove all-test
`finitePrimeExact`.

Rewire these consumers:

```text
normalizedSelectedFinalRouteInputFromTheorems:
  new producer assembled from accepted Plan 03 / 04 / 05 outputs and the
  certificate-boundary finite-prime owner.

normalizedRouteCertificateFromTheorems:
  old:
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)

  new:
    RouteCertificate
      (RouteInputs.ofSelectedFinalInput normalizedSelectedFinalRouteInputFromTheorems)

normalizedFinalExitPackageFromTheorems:
  old:
    RouteFinalExitPackage
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)

  new:
    RouteFinalExitPackage
      (RouteInputs.ofSelectedFinalInput normalizedSelectedFinalRouteInputFromTheorems)

routeCertificateFromTheorems:
  alias the selected-route certificate, not the all-test package certificate.

unconditional_rh_skeleton / unconditional_rh_contract_skeleton:
  derive Mathlib RH from the selected-route certificate through:
    cc20_source_rh_of_route_certificate
    Source.RHDefinitionBridge.source_rh_to_mathlib_rh
```

Demote these declarations to compatibility-only for final D1 acceptance unless
their own axiom audits are clean and they no longer unfold to Root 1 / Root 2:

```text
normalizedCoreSourceWeilFormDataFromTheorems
normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems
normalizedSourceObjectCoreFinitePrimeExactFromTheorems
normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems
normalizedSourceObjectCoreTheoremBaseDataFromTheorems
normalizedSourceObjectTheoremBaseInputFromTheorems
normalizedSourceObjectPackageFromTheorems
Source.sourceObjectPackageOfNormalizedCC20Trace
```

Rejected selected-API shapes:

```text
NormalizedSelectedFinalRouteInput.sourceObjectPackage :
  Source.SourceObject.SourceObjectPackage

NormalizedSelectedFinalRouteInput.baseInput :
  Source.NormalizedSourceObjectTheoremBaseInput

NormalizedSelectedFinalRouteInput.finitePrimeExact :
  CommonFinitePrimeArithmeticSourceData ...

route_certificate_of_selected_final_route_input input :=
  normalizedRouteCertificateFromTheorems

RouteInputs.ofSelectedFinalInput input :=
  RouteInputs.ofExpandedSourcePackage input.sourceObjectPackage
```

Accepted selected-API shape:

```text
selected Plan 03 owner
selected Plan 04 owner
accepted Plan 05 CC20 exit / finite-vanishing owner
accepted certificate-boundary finite-prime owner
accepted ledger / restricted-to-full owners
  -> selected RouteInputs
  -> route certificate
  -> SourceRH
  -> Mathlib RH
```

Final Phase 2A gate:

```text
If the final route cannot be typed without `RouteInputs.ofExpandedSourcePackage`
or `Source.sourceObjectPackageOfNormalizedCC20Trace`, and those still import
`finitePrimeExact`, Plan 06 is rejected as not closed.  The implementation must
not claim Root 1 / Root 2 were bypassed.
```

### Phase 3: remove compatibility outlets from the final path

Compatibility declarations may remain, but the no-argument theorem must use the
accepted route path:

```text
routeCertificateFromTheorems := normalizedRouteCertificateFromTheorems
unconditional_rh_skeleton := final_connes_weil_rh routeCertificateFromTheorems
```

Reject any final theorem that instead reads:

```text
mathlibRH field
SourceRH field
old package projection
Root 1 / Root 2 projection
```

If `NormalizedNoArgumentRouteCertificatePackage` remains, remove the active
`mathlibRH : _root_.RiemannHypothesis` field or document it as
compatibility-only and exclude it from every solved-target audit.  A package
that stores final RH is not final closure evidence.

Apply the same rule to `RouteFinalExitPackage`.  The accepted route-level shape
is:

```lean
structure RouteFinalExitPackage
    (inputs : RouteInputs) where
  certificate : RouteCertificate inputs
  exitInput :
    RouteBackedCC20ExitInputData inputs
      certificate.sourceBackedTest certificate.ledgers certificate.bridge
  sourceRH : inputs.cc20.rhDefinitionBridge.SourceRH
  sourceRHMatchesC1 :
    sourceRH =
      inputs.cc20.cc20RHExitObjectPackage.propositionC1SourceCriterion
        exitInput.input exitInput.propositionC1InputData

def mathlib_rh_of_route_final_exit_package
    {inputs : RouteInputs} (h : RouteFinalExitPackage inputs) :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    inputs.cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_final_exit_package h)
```

Rejected route-level shape:

```lean
mathlibRH : _root_.RiemannHypothesis
mathlibRHMatchesSourceBridge : ...
```

Concrete preferred edit:

```lean
structure NormalizedNoArgumentRouteCertificatePackage where
  routeCertificate :
    RouteCertificate
      (RouteInputs.ofSelectedFinalInput
        normalizedSelectedFinalRouteInputFromTheorems)
  finalExitPackage :
    RouteFinalExitPackage
      (RouteInputs.ofSelectedFinalInput
        normalizedSelectedFinalRouteInputFromTheorems)

noncomputable def normalizedNoArgumentRouteCertificatePackageFromTheorems :
    NormalizedNoArgumentRouteCertificatePackage where
  routeCertificate := normalizedRouteCertificateFromTheorems
  finalExitPackage := normalizedFinalExitPackageFromTheorems

def mathlib_rh_of_normalized_no_argument_route_certificate_package
    (pkg : NormalizedNoArgumentRouteCertificatePackage) :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    (RouteInputs.ofSelectedFinalInput
      normalizedSelectedFinalRouteInputFromTheorems).cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_certificate pkg.routeCertificate)
```

Rejected edit:

```lean
mathlibRH : _root_.RiemannHypothesis
```

inside any final no-argument data structure that counts as closure evidence.

### Phase 4: run the final build

Use WSL:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Route.FixedTestFrontEnd ConnesWeilRH.Route.RouteTheorem'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Dev.UnconditionalSkeleton'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH'
```

Build success is required. It is not sufficient.

### Phase 5: run the final focused axiom audit

Create a temporary scratch file outside the repo:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedSTestTripleVanishingInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedSTestSourceInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedTestFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedFixedDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceBackedFixedSTestFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedTraceDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.routeCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
```

Run:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake env lean /tmp/d1_final_rh_audit.lean'
```

Accepted output for final targets:

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
```


## 7. Static Rejection Scans

Run before acceptance:

```text
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Source ConnesWeilRH/Route -g "*.lean"

rg -n "normalizedCoreSourceWeilFormDataFromTheorems|normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems|normalizedCoreSourceModelConstructorCoreFromTheorems|normalizedCoreCCM25SourceModelFromTheorems|SourceWeilFormData\.toCCM25SourceModel|CommonFinitePrimeArithmeticSourceData|normalizedSourceObjectCoreFinitePrimeExactFromTheorems|NormalizedSourceObjectTheoremBaseInput|sourceObjectPackageOfNormalizedCC20Trace|RouteInputs\.ofExpandedSourcePackage|finitePrimeExact\s*:=" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"

rg -n "NormalizedSelectedFinalRouteInput|normalizedSelectedFinalRouteInputFromTheorems|route_certificate_of_selected_final_route_input|RouteInputs\.ofSelectedFinalInput|final_connes_weil_rh_of_selected_final_route_input" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"

rg -n "normalizedFixedSTestTripleVanishingInputFromTheorems|normalizedScalarFixedSTestTripleVanishingInputFromTheorems|TripleVanishingStatement\s*:=|sourceTripleVanishing\s*:=|routeTripleVanishingBridge\s*:=" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"

rg -n "mathlibRH\s*:|\.mathlibRH|SourceRH\s*:=|RiemannHypothesis\s*:=|Set\.univ|\bTrue\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route ConnesWeilRH/Source -g "*.lean"

rg -n "unconditional_rh_skeleton|unconditional_rh_contract_skeleton|routeCertificateFromTheorems|normalizedRouteCertificateFromTheorems|final_connes_weil_rh|cc20_source_rh_of_route_certificate" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"
```

The scans do not decide acceptance. They tell the reviewer where to inspect.


## 8. WSL Build Gate

Run in WSL:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Route.FixedTestFrontEnd ConnesWeilRH.Route.RouteTheorem'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Dev.UnconditionalSkeleton'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH'
```


## 9. Focused Axiom Audit

Use the scratch file from Phase 5.

Acceptance requires:

```text
normalizedRouteCertificateFromTheorems:
  no sorryAx

unconditional_rh_skeleton:
  no sorryAx

unconditional_rh_contract_skeleton:
  no sorryAx
```

Root 1 / Root 2 interpretation:

```text
If the old declarations themselves still print `sorryAx`, that is acceptable
only when the final target audit no longer reaches them.

If any final target reaches either old root, this plan fails.
```

Mandatory package/type audit:

```lean
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreFinitePrimeExactFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectTheoremBaseInputFromTheorems
```

Accepted only if these declarations are absent from the final no-argument
dependency path or their axiom output no longer contains `sorryAx`.


## 10. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Prerequisite plans:
  Plan 03:
    accepted / not accepted

  Plan 04:
    accepted / not accepted

  Plan 05:
    accepted / not accepted

Old Root 1 / Root 2 status:
  normalizedCoreSourceWeilFormDataFromTheorems:
    compatibility-only / inactive / still active

  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems:
    compatibility-only / inactive / still active

Package/type dependency status:
  NormalizedSelectedFinalRouteInput:
    introduced / not needed because package repaired / missing

  route_certificate_of_selected_final_route_input:
    active / not needed because package repaired / missing

  RouteInputs.ofSelectedFinalInput:
    active / not needed because package repaired / missing

  Source.sourceObjectPackageOfNormalizedCC20Trace:
    compatibility-only / inactive / still active

  RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems:
    compatibility-only / inactive / still active

  normalizedSourceObjectCoreFinitePrimeExactFromTheorems:
    compatibility-only / inactive / still active

  normalizedCoreCCM25SourceModelFromTheorems:
    compatibility-only / inactive / still active

  normalizedCoreSourceModelConstructorCoreFromTheorems:
    compatibility-only / inactive / still active

No-argument RH payload:
  NormalizedNoArgumentRouteCertificatePackage.mathlibRH:
    removed / compatibility-only / still active

Route final-exit RH payload:
  RouteFinalExitPackage.mathlibRH:
    removed / compatibility-only / still active

Fixed-test triple vanishing:
  producer:
    <exact declaration>

  route bridge:
    <exact declaration>

Final route:
  route certificate:
    normalizedRouteCertificateFromTheorems

  RH theorem:
    unconditional_rh_skeleton
    unconditional_rh_contract_skeleton

Build:
  Route.FixedTestFrontEnd + Route.RouteTheorem:
    pass / fail

  Dev.UnconditionalSkeleton:
    pass / fail

  ConnesWeilRH:
    pass / fail

Focused axiom audit:
  normalizedRouteCertificateFromTheorems:
    <exact output>

  unconditional_rh_skeleton:
    <exact output>

  unconditional_rh_contract_skeleton:
    <exact output>

Remaining black box:
  None, if final audits are clean.

  Otherwise:
    first non-Mathlib black box:
      <exact declaration/type>

    why the current proof path stops there:
      <specific reason>

    concrete lower definition or theorem needed next:
      <specific declaration shape>
```
