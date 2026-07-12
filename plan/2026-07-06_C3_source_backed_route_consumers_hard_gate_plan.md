# C3 Source-Backed Route Consumers Hard Gate Plan

## 1. Hard Completion Gate

C3 is solved only when every active source-backed route consumer in the table
below gets its route predicate from a named lower source owner, not from a
compact `SourceBackedFixedSTest` field projection.

```text
old weak path:
  SourceBackedFixedSTest.<field>
    -> *_of_source_backed theorem
    -> RouteBridgeCertificate / RouteCertificate / RouteBackedCC20ExitInputData

new semantic owner/API:
  SourceBackedRouteConsumerRows or direct row-owner arguments that name:
    fixed-S CCM24 support/window/scaling/Fourier/comparison owners
    CCM25 finite-prime source owners
    S2-B1 trace-scale/source-term owners
    C1 RouteLedgerSemanticData
    C2 RestrictedToFullQWBridgeContract

real consumer rewired:
  finite_prime_visibility_statement_of_source_backed
  triple_vanishing_statement_of_source_backed
  canonical_model_compatibility_of_source_backed
  support_transport_of_source_backed
  bounded_comparison_of_source_backed
  sonin_exhaustion_of_source_backed
  window_support_containment_of_source_backed
  post_q_series_tail_bounded_comparison_of_source_backed
  route_backed_cc20_exit_input_data_of_route_bridge_certificate

same-object alias / wrapper rejection scan:
  rg -n "g\\.(supportInWindow|fourierSupportInWindow|supportTransported|convolutionSupportTransported|boundedComparisonMap|boundedComparisonInverse|fixedWindowExhaustionCompatible|finitePrimeVisibilityBridge|tripleVanishingSourceHolds|windowContainedInLambda|lambdaCompatible)|of_source_backed.*:=.*g\\.|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Route -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Route.RouteTheorem

focused axiom audit targets:
  ConnesWeilRH.Route.finite_prime_visibility_statement_of_source_backed
  ConnesWeilRH.Route.triple_vanishing_statement_of_source_backed
  ConnesWeilRH.Route.triple_vanishing_of_source_backed
  ConnesWeilRH.Route.canonical_model_compatibility_of_source_backed
  ConnesWeilRH.Route.support_transport_of_source_backed
  ConnesWeilRH.Route.bounded_comparison_of_source_backed
  ConnesWeilRH.Route.sonin_exhaustion_of_source_backed
  ConnesWeilRH.Route.window_support_containment_of_source_backed
  ConnesWeilRH.Route.post_q_series_tail_bounded_comparison_of_source_backed
  ConnesWeilRH.Route.route_backed_cc20_exit_input_data_of_route_bridge_certificate
  ConnesWeilRH.Route.final_connes_weil_rh

semantic sufficiency for next route/RH step:
  C4 receives a route certificate whose inputs are source-backed semantic rows.
  It must not depend on compact fixed-test fields as the proof source for rows
  that already have lower source data.
```

Per-consumer closure table:

```text
consumer theorem:
  finite_prime_visibility_statement_of_source_backed
exact old field path:
  g.finitePrimeSourceDataOwner is acceptable as the lower CCM25 owner;
  g.finitePrimeVisibilityBridge is not acceptable as the proof source.
new owner/API:
  Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
route dependency:
  finite_primes_visible_of_source_backed -> AdmissibleForTheorem1

consumer theorem:
  triple_vanishing_statement_of_source_backed / triple_vanishing_of_source_backed
exact old field path:
  g.tripleVanishingSourceHolds and g.tripleVanishingBridge
new owner/API:
  named source triple-vanishing owner, or mark this row as first remaining
  non-source-backed black box if no lower owner exists
route dependency:
  RouteBackedCC20TripleVanishingInputData

consumer theorem:
  canonical_model_compatibility_of_source_backed
exact old field path:
  g.scalingActionImplemented and g.fourierGradingCompatible
new owner/API:
  CCM24 scaling/Fourier semantic owners from the source package chain
route dependency:
  route certificate construction and CC20 exit input

consumer theorem:
  support_transport_of_source_backed
exact old field path:
  g.supportTransported and g.convolutionSupportTransported
new owner/API:
  CCM24 support/window transport owner from the source package chain
route dependency:
  RouteBridgeCertificate support transport rows

consumer theorem:
  bounded_comparison_of_source_backed
exact old field path:
  g.boundedComparisonMap and g.boundedComparisonInverse
new owner/API:
  CCM24 bounded comparison semantic owner
route dependency:
  post-Q tail and sign-defect bridge

consumer theorem:
  sonin_exhaustion_of_source_backed
exact old field path:
  g.fixedWindowExhaustionCompatible
new owner/API:
  CCM24 fixed-window exhaustion semantic owner
route dependency:
  route bridge / exhaustion rows

consumer theorem:
  window_support_containment_of_source_backed
exact old field path:
  g.supportInWindow, g.fourierSupportInWindow,
  g.convolutionSupportTransported, g.windowContainedInLambda
new owner/API:
  CCM24 support carrier, Fourier support carrier, and lambda-window owners
route dependency:
  WindowSupportContainment and Theorem1 input

consumer theorem:
  post_q_series_tail_bounded_comparison_of_source_backed
exact old field path:
  g.boundedComparisonMap and g.boundedComparisonInverse
new owner/API:
  same bounded comparison owner used by bounded_comparison_of_source_backed
route dependency:
  SignDefect post-Q tail bridge

consumer theorem:
  route_backed_cc20_exit_input_data_of_route_bridge_certificate
exact old field path:
  indirect calls to route consumer wrappers that still project g.<field>
new owner/API:
  RouteBridgeCertificate built from the lower row-owner proofs above
route dependency:
  final_connes_weil_rh
```

Partial C3 batches may close one row at a time, but a final C3 acceptance block
must show every row in this table either rewired or named as the first remaining
black box with its exact owner gap.


## 2. Result First

Result:
  Planning only. No Lean proof progress.

Plan source:
  This plan follows `plan/README.md`.

Parent map:
  `01_TOP_DOWN_TRACE_SCALE_SOURCE_TERM_LEDGER.md` lists C3 under
  `[C] route / ledger / final bridge`:

```text
C3. source-backed route consumers
  -> fixed-S CCM24 facts
  -> CCM25 finite-prime source facts
  -> S2-B1 source facts
  -> route theorem consumers
```

Evidence from current code:

```text
ConnesWeilRH/Route/Definitions.lean:125
  structure SourceBackedFixedSTest

ConnesWeilRH/Route/AdmissibleWindow.lean:43
  finite_prime_visibility_statement_of_source_backed

ConnesWeilRH/Route/AdmissibleWindow.lean:96
  canonical_model_compatibility_of_source_backed

ConnesWeilRH/Route/AdmissibleWindow.lean:102
  support_transport_of_source_backed

ConnesWeilRH/Route/AdmissibleWindow.lean:110
  bounded_comparison_of_source_backed

ConnesWeilRH/Route/SignDefect.lean:274
  post_q_series_tail_bounded_comparison_of_source_backed

ConnesWeilRH/Route/RouteTheorem.lean:1362
  route_backed_cc20_exit_input_data_of_route_bridge_certificate
```

Current status:
  Several source-backed route consumers now expose source-facing theorem names,
  but C3 is not closed while route consumers can still read compact
  `SourceBackedFixedSTest` fields as if they were lower source facts.  The hard
  gate requires each active route consumer to name the lower owner it needs.


## 3. What Counts As Solved

All items below must hold for full C3 closure.  A smaller batch may claim
partial C3 progress only for the rows it rewires.

```text
1. Each closed row names its exact old `g.<field>` path.

2. Each closed row names the lower semantic owner it consumes.

3. Each closed row rewires a route consumer that feeds
   `RouteBridgeCertificate`, `RouteBackedCC20ExitInputData`, or
   `RouteCertificate`.

4. The theorem proving the row does more than return a field from `g`.

5. Same-object alias / wrapper rejection scan passes.

6. WSL build passes:
     lake build ConnesWeilRH.Route.RouteTheorem

7. focused axiom audit passes for the exact C3 consumer targets listed below.

8. semantic sufficiency for next route/RH step:
     C4 receives a route certificate whose inputs are source-backed semantic
     facts, not compact field projections or package endpoints.
```

Complete resolution means the route layer no longer treats
`SourceBackedFixedSTest` as a bag of proved route facts.  The route layer must
show which source owner proves each route predicate that the CC20 exit uses.


## 4. What Does Not Count

Rejected as not solved:

```text
- adding source-backed theorem names that still return `g.someField`;
- moving fields from one route structure to another with the same proof path;
- narrowing only one consumer while final RouteCertificate uses the old one;
- proving fixed-S CCM24 facts from package endpoint aliases;
- proving CCM25 finite-prime facts from certificate atoms without source data;
- proving S2-B1 rows from raw RouteLedgers props;
- adding route wrappers around C1 or C2 without using them in RouteCertificate;
- counting `Route.RouteTheorem` build success while the final route certificate
  still reads compact fields.
```

Allowed compatibility:
  `SourceBackedFixedSTest` may remain the route-facing parameter that bundles a
  fixed test, but its fields should not be the accepted semantic owners for rows
  that already have lower source data.


## 5. Current Evidence

Code facts:

```text
SourceBackedFixedSTest currently stores fixed-S facts:
  ConnesWeilRH/Route/Definitions.lean:125

Route consumer projections exist:
  finite_prime_visibility_statement_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:43

  triple_vanishing_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:85

  canonical_model_compatibility_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:96

  support_transport_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:102

  bounded_comparison_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:110

  sonin_exhaustion_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:116

  window_support_containment_of_source_backed
    ConnesWeilRH/Route/AdmissibleWindow.lean:127

  post_q_series_tail_bounded_comparison_of_source_backed
    ConnesWeilRH/Route/SignDefect.lean:274

RouteBackedCC20ExitInputData is the route theorem consumer boundary:
  ConnesWeilRH/Route/RouteTheorem.lean:54
  ConnesWeilRH/Route/RouteTheorem.lean:1362
```

Interpretation:
  C3 is the integration lane.  It does not need another wrapper theorem.  It
  needs consumer rewires so every source-backed route fact has a visible lower
  source owner and the final route certificate consumes that stronger statement.


## 6. First-Principles Dependency Chain

The route theorem needs four kinds of evidence.

```text
fixed-S test data
  |
  +-- CCM24 support/window/scaling/Fourier/comparison
  |
  +-- CCM25 finite-prime visibility/exact support
  |
  +-- S2-B1 trace-scale and ledger rows
  |
  +-- C1 and C2 bridge facts
  |
  v
RouteBridgeCertificate
  |
  v
RouteBackedCC20ExitInputData
  |
  v
CC20 source RH
```

The weak chain collapses those owners:

```text
SourceBackedFixedSTest g
  |
  v
g.supportInWindow
g.boundedComparisonMap
g.finitePrimeVisibilityBridge
g.tripleVanishingSourceHolds
  |
  v
route consumer theorem
```

That chain can typecheck while hiding which source theorem proves the row.


## 7. Implementation Route

Step 1. Pin current local types.

```lean
#check SourceBackedFixedSTest
#check finite_prime_visibility_statement_of_source_backed
#check support_transport_of_source_backed
#check bounded_comparison_of_source_backed
#check post_q_series_tail_bounded_comparison_of_source_backed
#check RouteBackedCC20ExitInputData
#check route_backed_cc20_exit_input_data_of_route_bridge_certificate
```

Step 2. Classify active C3 consumers.

Use this table before editing:

```text
consumer theorem:
exact old field path:
lower owner already available:
owner missing:
route certificate dependency:
```

Start with consumers that directly feed `RouteBackedCC20ExitInputData` and
`RouteBridgeCertificate`.  Do not spend the first batch on a helper theorem
that no final route consumer uses.

Step 3. Add source-backed row owner records only where the current code lacks
one.

Preferred shape:

```lean
structure SourceBackedRouteConsumerRows (inputs : RouteInputs)
    (g : SourceBackedFixedSTest inputs) where
  fixedSCcm24Rows : ...
  finitePrimeRows : ...
  s2b1Rows : ...
  ledgerRows : RouteLedgerSemanticData ...
  restrictedToFullRows : RestrictedToFullQWBridgeContract ...
```

If existing source rows are already sufficient, use them directly.  Do not add
one large record merely to hide the same old field projections.

Step 4. Rewire route consumers.

Target declarations:

```text
finite_prime_visibility_statement_of_source_backed
triple_vanishing_of_source_backed
support_transport_of_source_backed
bounded_comparison_of_source_backed
sonin_exhaustion_of_source_backed
window_support_containment_of_source_backed
post_q_series_tail_bounded_comparison_of_source_backed
route_backed_cc20_exit_input_data_of_route_bridge_certificate
```

Expected direction:

```text
lower source row owner
  -> route-facing predicate
  -> RouteBridgeCertificate
  -> RouteBackedCC20ExitInputData
```

Step 5. Preserve route API boundaries.

Do not change public final theorem signatures in the first C3 batch unless the
consumer rewire proves a real semantic strengthening and the blast radius stays
inside `Route`.


## 8. Static Rejection Scans

Run these scans after implementation.

Compact field projection scan:

```text
rg -n "g\\.(supportInWindow|fourierSupportInWindow|supportTransported|convolutionSupportTransported|boundedComparisonMap|boundedComparisonInverse|fixedWindowExhaustionCompatible|finitePrimeVisibilityBridge|tripleVanishingSourceHolds)" ConnesWeilRH/Route -g "*.lean"
```

Expected result:
  Remaining hits must be compatibility readbacks or local construction of the
  fixed test.  They must not feed the active route certificate when a lower
  semantic owner exists.

Route certificate consumer scan:

```text
rg -n "RouteBackedCC20ExitInputData|RouteBridgeCertificate|RouteCertificate|sourceBackedFullPositivity|finalSignNonpositive|restrictedToFullQWBridge" ConnesWeilRH/Route -g "*.lean"
```

Same-object alias / wrapper scan:

```text
rg -n "of_source_backed.*:=.*g\\.|source_backed.*:=.*source_backed|\\bTrue\\b|Set\\.univ|sorry|admit|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"
```

C1/C2 integration scan:

```text
rg -n "RouteLedgerSemanticData|RestrictedToFullQWBridgeContract|lower_bound_evidence_of_route_ledger_semantics|source_qw_lambda_eq_qw_of_restricted_to_full_contract" ConnesWeilRH/Route/RouteTheorem.lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```


## 9. WSL Build Gate

Use the main WSL mirror.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'mkdir -p ~/projects/Connes-Weil-RH-Proof && rsync -a --delete --exclude .git --exclude .lake /mnt/c/Projects/Connes-Weil-RH-Proof/ ~/projects/Connes-Weil-RH-Proof/'

wsl -d Ubuntu-24.04 -- bash -lc 'cd ~/projects/Connes-Weil-RH-Proof && flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build ConnesWeilRH.Route.RouteTheorem'
```

If the implementation touches source owners, add the smallest source target
before the route build.  Examples:

```text
lake build ConnesWeilRH.Source.CCM24SourceModel
lake build ConnesWeilRH.Source.ObjectExpandedRows
lake build ConnesWeilRH.Source.S2B1TraceScale
```


## 10. Focused Axiom Audit

Create one scratch file in the WSL mirror with:

```lean
import ConnesWeilRH.Route.RouteTheorem

#check ConnesWeilRH.Route.support_transport_of_source_backed
#print axioms ConnesWeilRH.Route.support_transport_of_source_backed

#check ConnesWeilRH.Route.finite_prime_visibility_statement_of_source_backed
#print axioms ConnesWeilRH.Route.finite_prime_visibility_statement_of_source_backed

#check ConnesWeilRH.Route.triple_vanishing_statement_of_source_backed
#print axioms ConnesWeilRH.Route.triple_vanishing_statement_of_source_backed

#check ConnesWeilRH.Route.triple_vanishing_of_source_backed
#print axioms ConnesWeilRH.Route.triple_vanishing_of_source_backed

#check ConnesWeilRH.Route.canonical_model_compatibility_of_source_backed
#print axioms ConnesWeilRH.Route.canonical_model_compatibility_of_source_backed

#check ConnesWeilRH.Route.bounded_comparison_of_source_backed
#print axioms ConnesWeilRH.Route.bounded_comparison_of_source_backed

#check ConnesWeilRH.Route.sonin_exhaustion_of_source_backed
#print axioms ConnesWeilRH.Route.sonin_exhaustion_of_source_backed

#check ConnesWeilRH.Route.window_support_containment_of_source_backed
#print axioms ConnesWeilRH.Route.window_support_containment_of_source_backed

#check ConnesWeilRH.Route.post_q_series_tail_bounded_comparison_of_source_backed
#print axioms ConnesWeilRH.Route.post_q_series_tail_bounded_comparison_of_source_backed

#check ConnesWeilRH.Route.route_backed_cc20_exit_input_data_of_route_bridge_certificate
#print axioms ConnesWeilRH.Route.route_backed_cc20_exit_input_data_of_route_bridge_certificate

#check ConnesWeilRH.Route.final_connes_weil_rh
#print axioms ConnesWeilRH.Route.final_connes_weil_rh
```

Add any newly introduced C3 semantic theorem to the same scratch file.

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
bare SourceBackedFixedSTest field used as theorem source
package endpoint alias used as row proof
```


## 11. Final Acceptance Text

Use this exact shape after implementation:

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  <exact SourceBackedFixedSTest field projection path no longer active>

New semantic owner:
  <exact source-backed row owner>

Semantic theorem:
  <exact theorem deriving the route-facing predicate from the lower owner>

Consumer rewires:
  <exact Route theorem declarations>

Semantic sufficiency:
  The route certificate now receives the source-backed fact needed by the CC20
  exit from a named lower source owner, so C4 no longer depends on a compact
  fixed-test field for this row.

Build:
  <exact WSL command and result>

Focused axiom audit:
  <target list and axiom output>

Remaining black box:
  <first source row still not drilled to Mathlib, if any>
```
