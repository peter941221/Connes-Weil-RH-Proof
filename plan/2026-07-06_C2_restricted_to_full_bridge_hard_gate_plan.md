# C2 Restricted-To-Full Bridge Hard Gate Plan

## 1. Result First

Result:
  Planning only.  No Lean proof progress.

Plan source:
  This plan follows `plan/README.md`.

Parent map:
  `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lists C2 under
  `[C] route / ledger / final bridge`:

```text
C2. restricted-to-full bridge
  -> current cutoff binding
  -> threshold bridge package
  -> lower-bound evidence
```

Evidence from current code:

```text
ConnesWeilRH/Route/Bridge.lean:2277
  structure RestrictedToFullCurrentCutoffBinding

ConnesWeilRH/Route/Bridge.lean:2359
  structure RestrictedToFullQWBridgeData

ConnesWeilRH/Route/Bridge.lean:2519
  structure RestrictedToFullThresholdBridgePackage

ConnesWeilRH/Route/Bridge.lean:3205
  source_qw_lambda_eq_qw_of_restricted_to_full_contract

ConnesWeilRH/Route/Bridge.lean:3234
  lower_bound_evidence_of_route_ledger_semantics

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4316
  normalizedRestrictedToFullLargeLambdaThresholdFromTheorems

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4331
  normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
```

Current status:
  C2 has the correct high-level components: large-lambda threshold, current
  cutoff binding, scalar restriction, exact finite-prime support, and lower
  bound evidence.  The hard gate is not closed while the active normalized path
  can assemble the bridge through a threshold package and raw current cutoff
  without proving the semantic threshold/current relation from lower source
  rows.

  The final route theorem layer is also still package-shaped: the normalized
  route certificate constructor and final RH theorem accept
  `RestrictedToFullThresholdBridgePackage`.  A C2 implementation cannot count
  as complete if it only builds that package earlier and leaves the route
  theorem path unable to see the semantic current-cutoff owner.


## 2. What Counts As Solved

Hard completion gate:
  C2 is solved only if all of these hold:

```text
1. old weak path:
     normalizedRestrictedToFullThresholdRowsInputFromTheorems
       -> currentAboveThreshold := le_rfl
       -> normalizedRestrictedToFullThresholdBridgePackageFromTheorems
       -> normalizedRestrictedToFullQWFromTheorems
       -> normalizedRouteCertificateFromTheorems
       -> route_certificate_of_normalized_comparison_ledger_restricted_package

   is deleted from the active route certificate path or demoted to
   compatibility-only.

2. new semantic owner/API:
     a current-cutoff semantic owner that binds the full lower row set:
        large-lambda threshold data,
        current lambda,
        source common tuple,
        fixed-test support at the current lambda,
        prime-power atom stabilization,
        finite-prime stabilization,
        exact finite-prime support,
        restricted form is restriction of full QW,
        archimedean pole stability,
        archimedean contribution matching,
        no-spectral-convergence import boundary,
        scalar restriction witness,
        C1 lower-bound evidence.

   Existing `RestrictedToFullCurrentCutoffBinding` can serve if its active
   construction is fed by those lower source rows.  Existing
   `RestrictedToFullAllowedInputRows` is the minimum semantic row shape if the
   implementation needs a single owner for all restricted-to-full inputs.
   Otherwise introduce a normalized owner that stores only the missing lower
   evidence, then converts to `RestrictedToFullCurrentCutoffBinding` and
   `RestrictedToFullQWBridgeContract`.

3. semantic theorem:
     the active theorem proves:

       current lambda is above the lower threshold
       + restricted finite-prime support stabilizes at current lambda
       + scalar restricted form equals full QW
       + archimedean pole and contribution rows match the restriction
       + no-spectral-convergence import boundary is explicit
       + C1 lower-bound evidence
       -> RestrictedToFullQWBridgeContract

4. consumer declarations:
      normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
      normalizedRestrictedToFullThresholdBridgePackageFromTheorems
      normalizedRestrictedToFullQWFromTheorems
      normalizedRouteCertificateFromTheorems
      route_certificate_of_normalized_comparison_ledger_restricted_package
      final_rh_of_normalized_comparison_ledger_restricted_package, only if C2
        keeps this theorem in the hard gate rather than treating it as a
        downstream audit target

    use the new owner/API.

5. same-object alias / wrapper rejection scan passes.

6. WSL build passes:
     lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem

7. focused axiom audit passes for the exact C2 targets listed below.

8. semantic sufficiency for next route/RH step:
     C3 and C4 receive a restricted-to-full bridge whose statement explains why
     the current cutoff is legitimately large and why QW_lambda is the full QW
     value needed by the CC20 exit.
```

Complete resolution means the active route certificate no longer relies on a
package that merely stores `currentAboveThreshold` and `bridgeContract`.  It
must expose the source rows that justify both the threshold and the scalar
restriction at the current lambda.

Final-theorem scope rule:
  If `final_rh_of_normalized_comparison_ledger_restricted_package` remains in
  the C2 completion gate, the route theorem or an adjacent constructor must
  accept the semantic current-cutoff owner before package conversion.  If that
  signature is not changed, the final theorem is audit-only for C2 and cannot
  be cited as the consumer rewire.


## 3. What Does Not Count

Rejected as not solved:

```text
- adding another theorem that projects `h.bridgeContract`;
- proving only `bridgeContractMatchesCurrentCutoff`;
- keeping `currentAboveThreshold := le_rfl` as the active reason the current
  cutoff is above threshold;
- constructing `RestrictedToFullThresholdBridgePackage` from the same old
  fields and renaming it;
- using C1 lower-bound evidence from raw `L.cdefExhausts`;
- treating exact finite-prime package data as proof that restricted support
  equals full support;
- adding a no-spectral-convergence import alias without source rows;
- hiding finite-prime stabilization, archimedean stability, or no-spectral
  import inside the old scalar restriction witness without naming the rows;
- leaving `route_certificate_of_normalized_comparison_ledger_restricted_package`
  and `final_rh_of_normalized_comparison_ledger_restricted_package` as the only
  route-facing consumers when they still take a threshold bridge package;
- counting a clean audit for a wrapper that still hides the current cutoff.
```

Allowed compatibility:
  `RestrictedToFullThresholdBridgePackage` may stay as a transport package if
  `normalizedRouteCertificateFromTheorems` consumes a semantic current-cutoff
  owner first and the package is only a conversion layer.


## 4. Current Evidence

Code facts:

```text
RestrictedToFullCurrentCutoffBinding stores:
  commonTuple
  currentThresholdData
  scalarRestrictionWitness
  lowerBoundEvidence
  currentUsesCommonTuple
  witnessUsesCommonTuple

Source:
  ConnesWeilRH/Route/Bridge.lean:2277

RestrictedToFullQWBridgeData stores:
  largeLambdaThreshold
  currentAboveThreshold
  currentThresholdData
  scalarRestrictionWitness
  scalarRestrictionEquality
  exactFinitePrimeSupport
  lowerBoundEvidence

Source:
  ConnesWeilRH/Route/Bridge.lean:2359

RestrictedToFullThresholdBridgePackage stores:
  currentCutoff
  bridgeContract
  bridgeContractMatchesCurrentCutoff

Source:
  ConnesWeilRH/Route/Bridge.lean:2519

Current route-facing bridge theorem:
  source_qw_lambda_eq_qw_of_restricted_to_full_contract
  ConnesWeilRH/Route/Bridge.lean:3205

C1 evidence enters through:
  lower_bound_evidence_of_route_ledger_semantics
  ConnesWeilRH/Route/Bridge.lean:3234

The richer lower-row owner already exists:
  RestrictedToFullAllowedInputRows
  ConnesWeilRH/Route/Bridge.lean:2416

It carries commonTuple, fixedTestSupport, primePowerAtomStabilization,
finitePrimeStabilization, exactFinitePrimeSupport, restrictedFormIsRestriction,
archimedeanPoleStability, archimedeanContributionMatches,
noSpectralConvergenceImport, and lowerBoundEvidence.

The current route certificate constructor is package-shaped:
  ConnesWeilRH/Route/RouteTheorem.lean:2965
    route_certificate_of_normalized_comparison_ledger_restricted_package

  ConnesWeilRH/Route/RouteTheorem.lean:3002
    ledgerPackage : LedgerSignDefectPackage

  ConnesWeilRH/Route/RouteTheorem.lean:3011
    restrictedToFullPackage : RestrictedToFullThresholdBridgePackage

The current normalized Dev path feeds those packages directly:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4597
    route_certificate_of_normalized_comparison_ledger_restricted_package

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4604
    normalizedRouteLedgerClearingInputDataFromTheorems

  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4605
    normalizedRestrictedToFullThresholdBridgePackageFromTheorems
```

Interpretation:
  The data layout can express C2, but the normalized route must stop treating
  threshold/current/package assembly as the proof.  The proof needs named lower
  row owners for threshold-at-large, current cutoff, finite-prime stabilization,
  scalar restriction, archimedean stability, no-spectral import boundary, and
  C1 lower-bound evidence.


## 5. First-Principles Dependency Chain

The bridge must justify moving from a restricted lambda expression to the full
QW expression at the current cutoff.

```text
large-lambda threshold exists
  |
  v
current lambda is above threshold
  |
  v
support and finite-prime atoms stabilize
  |
  v
restricted scalar formula equals full QW
  |
  v
C1 lower-bound evidence controls the defect side
  |
  v
RestrictedToFullQWBridgeContract
  |
  v
RouteBridgeCertificate
```

The weak chain stores the result:

```text
threshold package
  |
  +-- currentCutoff
  +-- bridgeContract
  +-- proof they match by rfl
```

That chain is useful transport, but it is not the proof of the restricted-to-
full theorem.


## 6. Implementation Route

Step 1. Pin current local types.

```lean
#check RestrictedToFullCurrentCutoffBinding
#check RestrictedToFullQWBridgeContract
#check RestrictedToFullThresholdBridgePackage
#check restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
#check restricted_to_full_bridge_contract_of_current_cutoff_binding
#check source_qw_lambda_eq_qw_of_restricted_to_full_contract
#check lower_bound_evidence_of_route_ledger_semantics
```

Step 2. Name the current-cutoff semantic input.

Preferred normalized owner:

```lean
structure NormalizedRestrictedToFullCurrentCutoffSemanticInput where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold ... sourceConvolutionSquare
  currentAboveThreshold :
    threshold.lambda0 <= normalizedTraceFrontEndFromTheorems.lambda
  currentTuple :
    SourceCommonTestTupleContract ... normalizedTraceFrontEndFromTheorems.lambda ...
  fixedTestSupport :
    FixedTestSupportThresholdAtLarge ...
  primePowerAtomStabilization :
    PrimePowerAtomStabilizationAtLarge ...
  finitePrimeStabilization :
    RestrictedFinitePrimeSupportStabilizes ...
  finitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda ...
  restrictedFormIsRestriction :
    SourceQWLambdaIsRestrictionOfQW ...
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction ...
  archimedeanContributionMatches :
    SourceArchimedeanContributionMatchesForRestriction ...
  noSpectralConvergenceImport :
    RestrictedToFullNoSpectralConvergenceImport ...
  scalarRestriction :
    RestrictedToFullQWScalarRestrictionWitness ...
  lowerBound :
    RestrictedToFullQWLowerBoundEvidence ...
```

If existing records already contain all fields after C1, use them.  Prefer
`RestrictedToFullAllowedInputRows` when it matches the needed surface.  Do not
add an owner that only repackages `RestrictedToFullThresholdBridgePackage` or
stores the old scalar witness while hiding the row proofs.

Step 3. Prove the semantic conversion.

Target theorem shape:

```lean
noncomputable def normalized_restricted_to_full_bridge_contract_of_semantic_input
    (h : NormalizedRestrictedToFullCurrentCutoffSemanticInput) :
    RestrictedToFullQWBridgeContract ... := ...
```

The proof must use the semantic input fields, not reconstruct the old package
and project `bridgeContract`.

Step 4. Rewire active consumers.

Target declarations:

```text
normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
normalizedRestrictedToFullQWFromTheorems
normalizedRestrictedToFullThresholdBridgePackageFromTheorems
normalizedRouteCertificateFromTheorems
route_certificate_of_normalized_comparison_ledger_restricted_package
```

Expected direction:

```text
semantic current-cutoff input
  -> RestrictedToFullCurrentCutoffBinding
  -> RestrictedToFullQWBridgeContract
  -> semantic route certificate constructor
  -> RouteCertificate
```

Step 5. Demote old package paths.

The following may remain as compatibility readbacks:

```text
large_lambda_threshold_of_restricted_to_full_threshold_package
current_above_threshold_of_restricted_to_full_threshold_package
restricted_to_full_bridge_contract_of_threshold_package
bridge_contract_matches_current_cutoff_of_threshold_package
```

They must not be the active proof path into `normalizedRouteCertificateFromTheorems`.

If RouteTheorem signatures are not changed in this C2 batch, record that the
final theorem layer is audit-only and that the accepted C2 consumer is the Dev
normalized route certificate path.  Do not claim final route theorem rewire in
that case.


## 7. Static Rejection Scans

Run these scans after implementation.

Old package path scan:

```text
rg -n "normalizedRestrictedToFullThresholdPackageInputFromTheorems|normalizedRestrictedToFullCurrentCutoffInputFromTheorems|normalizedRestrictedToFullCurrentCutoffRowsInputFromTheorems|currentAboveThreshold := le_rfl|restricted_to_full_bridge_contract_of_threshold_package" ConnesWeilRH/Dev ConnesWeilRH/Route -g "*.lean"
```

Same-object alias / wrapper scan:

```text
rg -n "bridgeContractMatchesCurrentCutoff := rfl|restricted_to_full_.*:=.*restricted_to_full_|ThresholdBridgePackage.*bridgeContract|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"
```

Semantic row coverage scan:

```text
rg -n "RestrictedToFullAllowedInputRows|RestrictedToFullQWScalarRestrictionWitness|RestrictedFinitePrimeSupportStabilizes|PackageExactFinitePrimeSupportAtLambda|SourceQWLambdaIsRestrictionOfQW|SourceArchimedeanPoleStabilityForRestriction|SourceArchimedeanContributionMatchesForRestriction|RestrictedToFullNoSpectralConvergenceImport|RestrictedToFullQWLowerBoundEvidence|currentAboveThreshold|source_qw_lambda_eq_qw_of_restricted_to_full_contract" ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"
```

Expected result:
  The active normalized route certificate should show a visible chain from the
  semantic current-cutoff owner into `RestrictedToFullQWBridgeContract`.

Route theorem package-entry scan:

```text
rg -n "route_certificate_of_normalized_comparison_ledger_restricted_package|final_rh_of_normalized_comparison_ledger_restricted_package|RestrictedToFullThresholdBridgePackage|normalizedRestrictedToFullThresholdBridgePackageFromTheorems" ConnesWeilRH/Route/RouteTheorem.lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

Expected result:
  If these declarations remain package-shaped, they are downstream audit
  targets only.  If C2 claims a final route theorem consumer rewire, the scan
  must show a semantic current-cutoff owner entering before threshold-package
  conversion.


## 8. WSL Build Gate

Use the main WSL mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem'
```

If normalized Dev wiring changes:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'
```


## 9. Focused Axiom Audit

Create one scratch file in the WSL mirror with:

```lean
import ConnesWeilRH.Route.RouteTheorem
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check Route.RestrictedToFullCurrentCutoffBinding
#check Route.RestrictedToFullQWBridgeContract

#check Route.restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
#print axioms Route.restricted_to_full_current_cutoff_binding_of_route_ledger_semantics

#check Route.restricted_to_full_bridge_contract_of_current_cutoff_binding
#print axioms Route.restricted_to_full_bridge_contract_of_current_cutoff_binding

#check Route.source_qw_lambda_eq_qw_of_restricted_to_full_contract
#print axioms Route.source_qw_lambda_eq_qw_of_restricted_to_full_contract

#check Route.lower_bound_transfer_of_restricted_to_full_contract
#print axioms Route.lower_bound_transfer_of_restricted_to_full_contract

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullQWFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullQWFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullCurrentCutoffBindingFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullThresholdBridgePackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRestrictedToFullThresholdBridgePackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteCertificateFromTheorems

#check Route.route_certificate_of_normalized_comparison_ledger_restricted_package
#print axioms Route.route_certificate_of_normalized_comparison_ledger_restricted_package

#check Route.final_rh_of_normalized_comparison_ledger_restricted_package
#print axioms Route.final_rh_of_normalized_comparison_ledger_restricted_package
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
threshold package field used as semantic proof
raw C1 ledger prop used as lower-bound proof
semantic rows hidden behind a scalar witness or threshold package
final theorem still package-shaped while claimed as the rewired consumer
```


## 10. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  normalized threshold/current package assembly no longer feeds the active
  restricted-to-full bridge without lower semantic current-cutoff evidence.

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem deriving RestrictedToFullQWBridgeContract>

Consumer rewires:
  normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
  normalizedRestrictedToFullThresholdBridgePackageFromTheorems
  normalizedRestrictedToFullQWFromTheorems
  normalizedRouteCertificateFromTheorems
  route_certificate_of_normalized_comparison_ledger_restricted_package, if
  route theorem signature is changed
  final_rh_of_normalized_comparison_ledger_restricted_package, audit-only unless
  the final theorem path accepts the semantic owner before package conversion

Semantic sufficiency:
  The bridge proves the current restricted expression is the full QW expression
  needed by the CC20 exit, with C1 lower-bound evidence preserved.

Build:
  <exact WSL command and result>

Focused axiom audit:
  <target list and axiom output>

Remaining black box:
  <first threshold / finite-prime / scalar restriction row still not drilled>
```
