# C1 Route Ledger Semantic Data Hard Gate Plan

## 1. Result First

Result:
  Planning only.  No Lean proof progress.

Plan source:
  This plan follows `plan/README.md`.

Parent map:
  `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lists C1 under
  `[C] route / ledger / final bridge`:

```text
C1. route ledger semantic data
  -> RouteLedgerSemanticData
  -> rank/pole ledger rows
  -> RouteLedgers.cdefExhausts
```

Evidence from current code:

```text
ConnesWeilRH/Route/Definitions.lean:28
  structure RouteLedgers where
    rankKilled : Prop
    poleKilled : Prop
    cdefExhausts : Prop

ConnesWeilRH/Route/SignDefect.lean:466
  structure RouteLedgerSemanticData

ConnesWeilRH/Route/SignDefect.lean:553
  structure S2B1RouteLedgerSemanticInput

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3932
  structure NormalizedRouteLedgerRowsInput where

ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3971
  def normalizedRouteLedgerClearingInputDataFromTheorems
```

Current status:
  C1 has a useful route semantic data surface, but the active normalized path
  still builds the ledger package from raw `RouteLedgers` propositions stored
  in `NormalizedRouteLedgerSourceInput`.  That is project-bottom or API-boundary
  progress, not complete C1 resolution.

  There is also a wrapper risk: existing route helpers can construct
  `RouteLedgerSemanticData` from the same raw `L.rankKilled`, `L.poleKilled`,
  and `L.cdefExhausts` proofs.  A future implementation does not solve C1
  merely by routing those raw proofs through the semantic-data name.


## 2. What Counts As Solved

Hard completion gate:
  C1 is solved only if all of these hold:

```text
1. old weak path:
     NormalizedRouteLedgerRowsInput
       -> NormalizedRouteLedgerSourceInput
       -> normalizedRouteLedgerInputFromTheorems
       -> normalizedRouteLedgersClearedInputFromTheorems
       -> ledger_sign_defect_package_of_ledgers_cleared

   is deleted from the active normalized proof path or demoted to
   compatibility-only.

2. new semantic owner/API:
     RouteLedgerSemanticData
       or a strictly lower route/source owner feeding it

   supplies the active ledger proof object through named lower row owners.
   `RouteLedgerSemanticData` counts only when its active construction does not
   pass through raw `L.rankKilled`, `L.poleKilled`, or `L.cdefExhausts` fields.

3. semantic theorem:
     the active theorem proves the chain:

       sourcePositiveTraceRemainderOwnership
       + SourceRankPoleLedgerIdentification
       + SourceEndpointStripRemainderCdefDomination
       -> RouteLedgerSemanticData
       -> LedgersCleared

   without reading bare `L.rankKilled`, `L.poleKilled`, or `L.cdefExhausts`
   from an unrelated input record or from a compatibility wrapper around those
   three proofs.

4. consumer declarations:
      normalizedRouteLedgerClearingInputDataFromTheorems
      normalizedSignDefectClassificationFromTheorems
      normalizedSourceBackedLedgersFromTheorems
      normalizedRestrictedToFullThresholdBridgePackageFromTheorems
      normalizedRouteCertificateFromTheorems

   use the semantic owner, not the raw three-Prop ledger package.

5. same-object alias / wrapper rejection scan passes.

6. WSL build passes:
     lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem

7. focused axiom audit passes for the exact C1 semantic targets listed below.

8. semantic sufficiency for next route/RH step:
     C2 receives lower-bound evidence from the C1 semantic owner, so the
     restricted-to-full bridge no longer depends on a raw ledger bundle.
```

Complete resolution means the active proof path has no step that says, in
effect, "rank/pole/Cdef are cleared because three independent Prop fields say
so."  The proof path must explain why the rank, pole, and Cdef rows arise from
the source remainder partition and endpoint-strip Cdef domination.

Compatibility warning:
  These existing helpers are not accepted C1 sources unless they are rewritten
  so their active construction comes from lower row owners:

```text
route_ledger_semantic_data_of_source_backed_ledgers
S2B1RouteLedgerSemanticInput.rankKilled
S2B1RouteLedgerSemanticInput.poleKilled
S2B1RouteLedgerSemanticInput.cdefExhausts
```


## 3. What Does Not Count

Rejected as not solved:

```text
- adding more projections from RouteLedgerSemanticData;
- proving `h.rankPoleLedgerIdentification.rankKilled` only;
- wrapping `LedgersCleared` in another package;
- changing theorem names while keeping the three raw RouteLedgers fields active;
- constructing `SourceSignDefectClassification` directly from
  `hrank hpole hcdef`;
- constructing `RouteLedgerSemanticData` through
  `route_ledger_semantic_data_of_source_backed_ledgers`;
- using `S2B1RouteLedgerSemanticInput` as the accepted source while it still
  stores primitive `rankKilled`, `poleKilled`, or `cdefExhausts` proofs;
- making `RouteLedgers.rankKilled`, `RouteLedgers.poleKilled`, or
  `RouteLedgers.cdefExhausts` equal to `True`;
- filling S2-B1 row facts from endpoint package aliases;
- counting a clean axiom audit for a wrapper that still depends on raw Props.
```

Allowed compatibility:
  `RouteLedgers` may stay as the compact final ledger carrier if the active
  constructor fills it only through the new semantic owner and route consumers
  no longer use raw ledger-field input as evidence.


## 4. Current Evidence

Code facts:

```text
RouteLedgers is still three independent Props:
  ConnesWeilRH/Route/Definitions.lean:28

RouteLedgerSemanticData already splits the source-side content:
  ConnesWeilRH/Route/SignDefect.lean:466

It carries:
  oneLtLambda
  sourcePositiveTraceRemainderOwnership
  rankPoleLedgerIdentification
  endpointStripCdefDomination

It derives the old facts:
  ConnesWeilRH/Route/SignDefect.lean:515
    rankKilled
  ConnesWeilRH/Route/SignDefect.lean:522
    poleKilled
  ConnesWeilRH/Route/SignDefect.lean:529
    cdefExhausts
  ConnesWeilRH/Route/SignDefect.lean:531
    RouteLedgerSemanticData.ledgersCleared

The normalized active path still starts from raw rows:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3932
    NormalizedRouteLedgerRowsInput
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3940
    NormalizedRouteLedgerSourceInput
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:3971
    normalizedRouteLedgerClearingInputDataFromTheorems

The current semantic-data surface still has raw-proof compatibility entries:
  ConnesWeilRH/Route/SignDefect.lean:538
    route_ledger_semantic_data_of_source_backed_ledgers
      (hrank : L.rankKilled) (hpole : L.poleKilled)
      (hcdef : L.cdefExhausts)

  ConnesWeilRH/Route/SignDefect.lean:553
    structure S2B1RouteLedgerSemanticInput

  ConnesWeilRH/Route/SignDefect.lean:569
    rankKilled : L.rankKilled
    poleKilled : L.poleKilled
    cdefExhausts : L.cdefExhausts
```

Interpretation:
  C1 already has part of the right semantic shape in `Route/SignDefect.lean`.
  The hard work is to make the lower-row shape the active normalized route input
  and remove the raw three-Prop source as an accepted path.  Merely wrapping the
  raw proofs in `RouteLedgerSemanticData` remains a weak path.


## 5. First-Principles Dependency Chain

The route wants a lower-bound input for restricted-to-full and a cleared ledger
input for full positivity.

```text
source remainder after Q
  |
  v
no-strip projection split
  |
  +-- rank ledger identified
  |
  +-- pole ledger identified
  |
  v
endpoint-strip normal form
  |
  v
Cdef domination / exhaustion
  |
  v
RouteLedgerSemanticData
  |
  +-- LedgersCleared
  |
  +-- RestrictedToFullQWLowerBoundEvidence
  |
  v
RouteBridgeCertificate
  |
  v
final RH route
```

The weak chain skips the middle:

```text
raw rankKilled Prop
raw poleKilled Prop
raw cdefExhausts Prop
  |
  v
LedgersCleared
```

That weak chain can typecheck while proving no route semantics.


## 6. Implementation Route

Step 1. Pin current local types.

```lean
#check RouteLedgerSemanticData
#check RouteLedgerSemanticData.ledgersCleared
#check S2B1RouteLedgerSemanticInput
#check S2B1RouteLedgerSemanticInput.toRouteLedgerSemanticData
#check lower_bound_evidence_of_route_ledger_semantics
#check restricted_to_full_threshold_bridge_package_of_route_ledger_semantics
```

Step 2. Add or expose a normalized C1 semantic input.

Preferred owner name:

```lean
structure NormalizedRouteLedgerSemanticInput where
  lambda : Real
  oneLtLambda : 1 < lambda
  sourcePositiveTraceRemainderOwnership :
    SourcePositiveTraceRemainderOwnership ... lambda
  rankPoleLedgerIdentification :
    SourceRankPoleLedgerIdentification ... lambda normalizedRouteLedgersFromTheorems
  endpointStripCdefDomination :
    SourceEndpointStripRemainderCdefDomination ... lambda normalizedRouteLedgersFromTheorems
```

Use existing `RouteLedgerSemanticData` directly if Lean can express the
normalized parameters without a separate wrapper.  A new wrapper must exist
only to bind normalized parameters, not to rename the same raw Prop bundle.

Do not use the existing raw-proof compatibility theorem as the accepted source:

```lean
#check route_ledger_semantic_data_of_source_backed_ledgers
```

If `S2B1RouteLedgerSemanticInput` is used, first split or demote its primitive
ledger fields so the accepted path receives named lower row owners instead of
standalone `L.rankKilled`, `L.poleKilled`, and `L.cdefExhausts` proofs.

Step 3. Rewire the active normalized sign-defect path.

Target consumers:

```text
normalizedRouteLedgerClearingInputDataFromTheorems
normalizedSignDefectClassificationFromTheorems
normalizedSourceBackedLedgersFromTheorems
```

Expected direction:

```text
NormalizedRouteLedgerSemanticInput
  -> RouteLedgerSemanticData
  -> SourceSignDefectClassification
  -> SourceBackedLedgers
  -> LedgerSignDefectPackage
```

Step 4. Rewire C2-facing lower-bound evidence.

Target consumers:

```text
normalizedRestrictedToFullThresholdBridgePackageFromTheorems
normalizedRestrictedToFullQWFromTheorems
```

They must receive:

```text
lower_bound_evidence_of_route_ledger_semantics h
```

or the equivalent projection from the normalized semantic owner.

Step 5. Demote old raw rows.

Acceptable demotion:

```text
NormalizedRouteLedgerRowsInput
NormalizedRouteLedgerSourceInput
normalizedRouteLedgerInputFromTheorems
normalizedRouteLedgersClearedInputFromTheorems
```

may remain only as compatibility evidence, diagnostics, or source theorem
inputs that are not used by `normalizedRouteCertificateFromTheorems`.


## 7. Static Rejection Scans

Run these scans after implementation.

Old raw path scan:

```text
rg -n "normalizedRouteLedgerSourceInputFromTheorems|normalizedRouteLedgersClearedInputFromTheorems|ledger_sign_defect_package_of_ledgers_cleared|source_sign_defect_classification_of_source_backed_ledgers" ConnesWeilRH/Dev ConnesWeilRH/Route -g "*.lean"
```

The active normalized route certificate path must not use these as the
accepted C1 source.

Same-object alias / wrapper scan:

```text
rg -n "RouteLedgerSemanticData.*:=.*RouteLedgerSemanticData|toRouteLedgerSemanticData.*:= rfl|route_ledger_semantic_data_of_source_backed_ledgers|S2B1RouteLedgerSemanticInput|ledgersCleared.*:=.*ledgersCleared|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"
```

Bare ledger-field proof scan:

```text
rg -n "rankKilledHolds|poleKilledHolds|cdefExhaustsHolds|\\.rankKilled|\\.poleKilled|\\.cdefExhausts" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route -g "*.lean"
```

Expected result:
  Hits may remain for declarations, compatibility projections, and semantic
  readbacks.  They must not remain on the active normalized certificate route
  except as projections from the C1 semantic owner.

Active constructor scan:

```text
rg -n "normalizedRouteLedgerClearingInputDataFromTheorems|normalizedRouteCertificateFromTheorems|route_certificate_of_normalized_comparison_ledger_restricted_package" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route/RouteTheorem.lean
```

Expected result:
  The route certificate path must show the semantic owner entering before the
  ledger package is built.  A path that first builds `LedgerSignDefectPackage`
  from raw rows and only later projects semantic facts is rejected.


## 8. WSL Build Gate

Use the main WSL mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem'
```

If the implementation touches `Dev/UnconditionalSkeleton.lean`, also run:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean'
```


## 9. Focused Axiom Audit

Create one scratch file in the WSL mirror with:

```lean
import ConnesWeilRH.Route.RouteTheorem
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check Route.RouteLedgerSemanticData
#check Route.RouteLedgerSemanticData.ledgersCleared
#print axioms Route.RouteLedgerSemanticData.ledgersCleared

#check Route.lower_bound_evidence_of_route_ledger_semantics
#print axioms Route.lower_bound_evidence_of_route_ledger_semantics

#check Route.restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
#print axioms Route.restricted_to_full_current_cutoff_binding_of_route_ledger_semantics

#check Route.restricted_to_full_threshold_bridge_package_of_route_ledger_semantics
#print axioms Route.restricted_to_full_threshold_bridge_package_of_route_ledger_semantics

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedSignDefectClassificationFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedSignDefectClassificationFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteLedgerClearingInputDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteLedgerClearingInputDataFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.NormalizedContractBackedLane.normalizedRouteCertificateFromTheorems
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
free Prop field that states rank/pole/Cdef directly
endpoint package theorem standing in for row proof
raw-proof compatibility constructor standing in for C1 semantic data
```


## 10. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  NormalizedRouteLedgerRowsInput -> NormalizedRouteLedgerSourceInput ->
  normalizedRouteLedgersClearedInputFromTheorems no longer feeds the active
  normalized route certificate.

New semantic owner:
  <exact declaration>

Semantic theorem:
  <exact theorem deriving RouteLedgerSemanticData / SourceSignDefectClassification>

Consumer rewires:
  normalizedRouteLedgerClearingInputDataFromTheorems
  normalizedSignDefectClassificationFromTheorems
  normalizedSourceBackedLedgersFromTheorems
  normalizedRestrictedToFullThresholdBridgePackageFromTheorems
  normalizedRouteCertificateFromTheorems

Semantic sufficiency:
  C2 receives lower-bound evidence from C1 semantic data, so the
  restricted-to-full bridge no longer trusts an unstructured ledger bundle.

Build:
  <exact WSL command and result>

Focused axiom audit:
  <target list and axiom output>

Remaining black box:
  <first source row still not drilled to Mathlib, if any>
```
