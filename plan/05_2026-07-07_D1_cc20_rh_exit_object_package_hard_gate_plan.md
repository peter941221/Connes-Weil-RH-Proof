# D1 CC20 RH Exit Object Package Hard Gate Plan

Date: 2026-07-07

Status: planning only. This document does not prove RH, does not remove
`sorryAx`, and does not count as accepted Lean progress.

Execution correction, 2026-07-07:
  The earlier Phase 2C wording treated detector existence for an arbitrary
  `C : CC20TestSpace` as a theorem target.  That statement is false: choose a
  test space with `Test = Empty`, and no detector can exist.  The executable
  route must use a concrete CC20 test-space owner, or keep detector existence
  as an explicit remaining lower theorem.

Current no-black-box infrastructure modules:

```text
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
  RiemannZetaHalfNonvanishing
  cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero

ConnesWeilRH/Source/CC20TestSpace.lean
  CC20TestSpace
  CC20VanishesOn
  CC20FiniteVanishingWeilCriterion
  CC20RouteInputRealizesFiniteVanishingCriterion

ConnesWeilRH/Source/CC20YoshidaCriterion.lean
  YoshidaDetector
  CC20YoshidaDetectorExists
  cc20_proposition_c1_from_yoshida_detector

ConnesWeilRH/Source/CC20PropositionC1.lean
  cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors
```

These modules contain no `sorry`, `axiom`, `constant`, `opaque`, `unsafe`, or
stored SourceRH field.  They also do not close Plan 05: `ζ(1/2) ≠ 0` and
concrete Yoshida detector existence remain lower proof obligations.

Parallel execution split:

```text
05A:
  plan/05A_2026-07-07_D1_cc20_zeta_half_disjointness_plan.md
  owns:
    ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
    ConnesWeilRH/Source/DirichletEta.lean
    ConnesWeilRH/Source/CC20RHExit.lean
  target:
    cc20_triple_disjoint_from_standard_source_nontrivial_zeros

05B:
  plan/05B_2026-07-07_D1_cc20_test_space_owner_plan.md
  owns:
    ConnesWeilRH/Source/CC20TestSpace.lean
    ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
    ConnesWeilRH/Source/CC20Concrete.lean
  target:
    concrete CC20TestSpace owner

05C:
  plan/05C_2026-07-07_D1_cc20_yoshida_detector_plan.md
  owns:
    ConnesWeilRH/Source/CC20YoshidaCriterion.lean
    ConnesWeilRH/Source/CC20YoshidaConstruction.lean
  target:
    CC20YoshidaDetectorExists for the concrete owner

05D:
  plan/05D_2026-07-07_D1_cc20_proposition_c1_route_realization_plan.md
  owns:
    ConnesWeilRH/Source/CC20PropositionC1.lean
    ConnesWeilRH/Route/CC20RouteRealization.lean
  target:
    cc20_proposition_c1_standard_source_criterion

05E:
  plan/05E_2026-07-07_D1_cc20_rh_exit_dev_integration_plan.md
  owns:
    ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  target:
    normalizedCoreCC20RHExitObjectPackageFromTheorems
  start condition:
    05A and 05D are Good.
```

Snapshot note:
  Line ranges below cite the accepted baseline used by this plan.  If the main
  worktree is dirty, declaration names are authoritative for review, and no
  dirty Lean diff counts as accepted progress until it passes the stated build
  and focused axiom gates.

Scope:
  Eliminate or precisely bottom out the hard CC20 exit root:

```text
ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
```


## 1. Result First

Expected result:

```text
Good:
  normalizedCoreCC20RHExitObjectPackageFromTheorems is no longer a `sorry`;
  it is built from lower source facts that construct the CC20 finite set,
  disjointness from source nontrivial zeros, and the Proposition C.1 source
  criterion for RHDefinitionBridge.standard.

Partial but useful:
  The current proof path reaches a named first non-Mathlib black box, with the
  exact disjointness theorem, source criterion theorem, or finite-vanishing
  owner that must be supplied next.  This is a blocker report, not accepted
  closure for this lane.

No-black-box execution mode:
  Peter's 2026-07-07 follow-up requests a complete plan for proving the two
  Phase 2C hard theorems, not a blocker report.  In this mode the lane cannot
  stop at an accepted-source import, an axiom boundary, an opaque wrapper, or a
  field that restates Proposition C.1.  The eta side condition, a concrete
  CC20 test-space owner, the Mellin vanishing predicate, the CC20 Weil sum, the
  final sign inequality, and the Yoshida / Proposition C.1 argument must all be
  expressed as Lean declarations with clean proof terms.

Rejected:
  The root is filled by a stored `_root_.RiemannHypothesis`, raw SourceRH field,
  raw Proposition C.1 criterion field, `True`, `Set.univ`, or a generic final
  root wrapper.  A structure that stores
  `sourcePackage : SourceFiniteVanishingCriterionPackage B` is also rejected
  unless the stored package is constructed from lower accepted facts in the
  same proof path.
```

Current status:

```text
MEMORY.md records this as one of the hard D1 black boxes.  The final
no-argument skeleton still shows `sorryAx` through this root.
```

Current bottom after source scan:

```text
first non-Mathlib black boxes:
  1. Source.SourceFiniteSetDisjointFromNontrivialZeros
       Source.RHDefinitionBridge.standard
       Source.cc20TripleFiniteVanishingSet

  2. ∀ input : Source.WeilPositivityInput,
       Source.CC20PropositionC1InputData
         Source.RHDefinitionBridge.standard
         Source.cc20TripleFiniteVanishingSet
         input ->
       Source.RHDefinitionBridge.standard.SourceRH

why:
  The tree supplies the finite CC20 triple and its admissibility proof, but no
  no-argument theorem proves disjointness from standard source nontrivial zeros
  or the Proposition C.1 source criterion.  Existing CC20 witness/data records
  store a SourceFiniteVanishingCriterionPackage or convert from a
  CC20RHExitObjectPackage; they do not produce those two fields from lower
  facts.
```


## 2. What Counts As Solved

Hard completion gate:

```text
old weak path:
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1472-1475
    normalizedCoreCC20RHExitObjectPackageFromTheorems :
      Source.CC20RHExitObjectPackage normalizedCoreRHDefinitionBridgeFromTheorems
    := by
      sorry

new semantic owner/API:
  Source.SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard
    only if its fields are supplied by lower non-free declarations:
      finiteVanishingSet
      finiteSetAdmissibleData
      finiteSetDisjointFromNontrivialZeros
      sourceCriterionData

  The accepted lower path must name the producer for each field.  For the
  current file, `finiteSetAdmissibleData` may use the existing CC20 triple
  proof.  The disjointness and source criterion fields need named lower
  producers or must be reported as the first non-Mathlib black boxes.

  Concrete accepted constructor shape:
    finiteVanishingSet :=
      Source.cc20TripleFiniteVanishingSet

    finiteSetAdmissibleData :=
      Source.cc20_triple_finite_set_admissibility

    finiteSetDisjointFromNontrivialZeros :=
      <new or existing lower theorem with exact type:
        Source.SourceFiniteSetDisjointFromNontrivialZeros
          Source.RHDefinitionBridge.standard
          Source.cc20TripleFiniteVanishingSet>

    sourceCriterionData :=
      <new or existing lower theorem with exact type:
        ∀ input : Source.WeilPositivityInput,
          Source.CC20PropositionC1InputData
            Source.RHDefinitionBridge.standard
            Source.cc20TripleFiniteVanishingSet
            input ->
          Source.RHDefinitionBridge.standard.SourceRH>

  The accepted path may use:
    SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage

  The accepted path may not use:
    a raw free `B.SourceRH`
    a stored `_root_.RiemannHypothesis`
    a no-argument wrapper whose field states the target theorem
    SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage as the
      producer for the same core package
    a record whose only semantic field is
      `sourcePackage : SourceFiniteVanishingCriterionPackage B`

real consumer rewired:
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  normalizedSourceObjectCoreBasePackageFromTheorems
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  normalizedSourceObjectRHExitObjectFromTheorems
  normalizedRhExitFromTheorems
  normalizedSourceObjectPackageFromTheorems
  normalizedRouteCertificateFromTheorems
  normalizedNoArgumentRouteCertificatePackageFromTheorems
  routeCertificateFromTheorems
  cc20FiniteVanishingExitFromTheorems
  rhDefinitionBridgeToMathlibFromTheorems
  unconditional_rh_skeleton
  unconditional_rh_contract_skeleton

same-object alias / wrapper rejection scan:
  rg -n "normalizedCoreCC20RHExitObjectPackageFromTheorems|CC20RHExitObjectPackage|SourceFiniteVanishingCriterionPackage|sourceCriterionData|propositionC1SourceCriterion|finiteSetDisjointFromNontrivialZeros|sourcePackage\\s*:\\s*SourceFiniteVanishingCriterionPackage|SourceRH\\s*:=|mathlibRH\\s*:|RiemannHypothesis\\s*:=|Set\\.univ|\\bTrue\\b" ConnesWeilRH -g "*.lean"

smallest WSL build:
  lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Source.CC20
  lake build ConnesWeilRH.Route.RouteTheorem
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton

focused axiom audit targets:
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectRHExitObjectFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRhExitFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectPackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.routeCertificateFromTheorems
  ConnesWeilRH.Route.cc20_source_rh_of_route_certificate
  ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
  ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton

semantic sufficiency for next route/RH step:
  The route needs a source RH exit criterion that converts the route's
  finite-vanishing and positivity data into SourceRH for the same
  RHDefinitionBridge.standard later transported to Mathlib RH.  A theorem that
  only stores the conclusion as a field does not strengthen the RH route.
```

The lane is solved only if:

```text
1. The `sorry` at Dev/UnconditionalSkeleton.lean:1475 disappears.
2. The replacement constructs a real CC20RHExitObjectPackage.
3. The disjointness and Proposition C.1 source criterion fields come from lower
   owners or are reported as the exact remaining black boxes.
4. The package uses RHDefinitionBridge.standard, not a custom bridge that
   weakens the source zero predicate.
5. The Dev path no longer turns the same core CC20RHExitObjectPackage into a
   SourceFiniteVanishingCriterionPackage with `ofCC20RHExitObjectPackage` and
   calls that the producer.
6. Focused axiom audit for the producer and all listed consumers contains no
   `sorryAx` attributable to this root.
7. The final no-argument skeleton has one fewer upstream D1 hard root.
```

Partial status is not solved:

```text
If the implementation only reports the first non-Mathlib black box, record the
result as partial / blocked.  Do not mark
normalizedCoreCC20RHExitObjectPackageFromTheorems as closed, and do not let
Plan 06 count Plan 05 as an accepted prerequisite.
```

If no lower source criterion exists, the acceptable result is a black-box
report:

```text
first non-Mathlib black box:
  SourceFiniteVanishingCriterionPackage RHDefinitionBridge.standard

exact declaration/type:
  SourceFiniteSetDisjointFromNontrivialZeros :
    ∀ p : CriticalVanishingPoint,
      p ∈ finiteVanishingSet ->
        ¬RHDefinitionBridge.standard.sourceNontrivialZero
          (criticalVanishingPointValue p)

  SourceFiniteVanishingCriterionPackage.sourceCriterionData :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData B finiteVanishingSet input -> B.SourceRH

why the current proof path stops there:
  Route composition can consume a CC20RHExitObjectPackage, but the Dev skeleton
  has no no-argument producer for the source disjointness row and the
  Proposition C.1 source criterion.

concrete lower definition or Mathlib theorem needed next:
  Lean theorems proving:
    1. the CC20 finite set is disjoint from source nontrivial zeros for
       RHDefinitionBridge.standard;
    2. the CC20 Proposition C.1 input data imply
       RHDefinitionBridge.standard.SourceRH.

acceptance status:
  partial / blocked only, not Good.
```

Concrete candidate classification from the current tree:

```text
real lower producers already present:
  Source.cc20TripleFiniteVanishingSet
    file: ConnesWeilRH/Source/CC20RHExit.lean
    line: 21
    role: finiteVanishingSet

  Source.cc20_triple_finite_set_admissibility
    file: ConnesWeilRH/Source/CC20RHExit.lean
    line: 57
    role: finiteSetAdmissibleData

adapters / derived projections:
  Source.SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
    file: ConnesWeilRH/Source/CC20RHExit.lean
    line: 298
    verdict: adapter only; it reads a CC20RHExitObjectPackage and repackages it.

  Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
    file: ConnesWeilRH/Source/CC20RHExit.lean
    line: 609
    verdict: allowed only after a lower source package exists.

  Source.CC20FiniteVanishingRhExitData
    file: ConnesWeilRH/Source/CC20.lean
    line: 80
    verdict: wrapper-only unless its sourceFiniteVanishingCriterionPackage field
      is built in the same proof path from lower disjointness and source
      criterion theorems.

  Source.CC20FiniteVanishingRhExitWitness.ofSourcePackage
    file: ConnesWeilRH/Source/CC20.lean
    line: 102
    verdict: wrapper-only; accepts the package as input.

rejected as producers for this root:
  Source.CC20Interface.sourceFiniteVanishingRhExit
    file: ConnesWeilRH/Source/CC20.lean
    line: 266
    reason: calls ofCC20RHExitObjectPackage on an existing CC20 package.

  Source.CC20Interface.finite_vanishing_source_rh
  Source.CC20Interface.finite_vanishing_rh
    file: ConnesWeilRH/Source/CC20.lean
    lines: 276, 360
    reason: depend on sourceFiniteVanishingRhExit, which is adapter-derived
      from the CC20 package.

  Source.SourceObjectBackedCC20Interface.*
    file: ConnesWeilRH/Source/CC20.lean
    lines: 168-242
    reason: starts from a SourceObjectPackage that already contains cc20RHExit.

current missing declarations:
  normalizedCoreCC20FiniteSetDisjointFromNontrivialZerosFromTheorems :
    Source.SourceFiniteSetDisjointFromNontrivialZeros
      Source.RHDefinitionBridge.standard
      Source.cc20TripleFiniteVanishingSet

  normalizedCoreCC20PropositionC1SourceCriterionFromTheorems :
    ∀ input : Source.WeilPositivityInput,
      Source.CC20PropositionC1InputData
        Source.RHDefinitionBridge.standard
        Source.cc20TripleFiniteVanishingSet
        input ->
      Source.RHDefinitionBridge.standard.SourceRH
```


## 3. What Does Not Count

Rejected as not solved:

```text
- replacing the root with `axiom`, `constant`, `opaque`, or `unsafe`;
- using a field whose type is `_root_.RiemannHypothesis`;
- using a field whose type is `RHDefinitionBridge.standard.SourceRH` unless a
  lower source criterion constructs it;
- changing `SourceRH`, `WeilPositivityInput`, or `CC20PropositionC1SourceCriterion`
  to `True`;
- choosing a fake finiteVanishingSet with fake admissibility or disjointness;
- proving Proposition C.1 by ignoring the input data;
- converting an already supplied CC20RHExitObjectPackage back into itself and
  calling that progress;
- using the source-object RH exit wrapper as the source of the core CC20 exit.
- using `SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage` on
  the same core package as the lower source criterion;
- using `CC20FiniteVanishingRhExitData`, `CC20FiniteVanishingRhExitWitness`, or
  a new record with `sourcePackage : SourceFiniteVanishingCriterionPackage B`
  as the owner unless the stored package is built from lower accepted facts;
- relying on `standard_criterion_output_iff_mathlib`,
  `criterion_to_mathlib_rh`, or `source_rh_to_mathlib_rh` as the producer for
  SourceRH.  These are bridge theorems after SourceRH exists, not the CC20
  source criterion itself.
```

Allowed compatibility:

```text
SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
```

may remain as adapters.  They do not count as the new owner unless the input
package is built from a lower accepted source criterion.

The current Dev path must be audited explicitly because it contains this
adapter shape:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1515-1540
  normalizedSourceObjectRHExitObjectFromTheorems builds
  sourceFiniteVanishingCriterionPackage by calling
  SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage on
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.cc20RHExitObjectPackage.
```

That adapter may remain only as compatibility after the core package has been
constructed from lower accepted source facts.


## 4. Current Evidence

Root placeholder:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1472-1475
  noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
      Source.CC20RHExitObjectPackage
        normalizedCoreRHDefinitionBridgeFromTheorems := by
    sorry
```

The root feeds the source-object theorem-base package:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1477-1491
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems where
    rhDefinitionBridge := normalizedCoreRHDefinitionBridgeFromTheorems
    cc20RHExitObjectPackage :=
      normalizedCoreCC20RHExitObjectPackageFromTheorems
```

The root reaches the route certificate:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:4807-4821
  normalizedRouteCertificateFromTheorems consumes normalizedRhExitFromTheorems
  and normalizedSourceObjectPackageFromTheorems.
```

The CC20 exit package fields are strong:

```text
ConnesWeilRH/Source/CC20RHExit.lean:94-102
  structure CC20RHExitObjectPackage (B : RHDefinitionBridge) where
    finiteVanishingSet : Finset CriticalVanishingPoint
    finiteSetAdmissible : SourceFiniteSetAdmissibility finiteVanishingSet
    finiteSetDisjointFromNontrivialZeros :
      SourceFiniteSetDisjointFromNontrivialZeros B finiteVanishingSet
    propositionC1SourceCriterion :
      ∀ input : WeilPositivityInput,
        CC20PropositionC1SourceCriterion B finiteVanishingSet input
```

The lower source package has the same real criterion boundary:

```text
ConnesWeilRH/Source/CC20RHExit.lean:285-294
  SourceFiniteVanishingCriterionPackage stores:
    finiteVanishingSet
    finiteSetAdmissibleData
    finiteSetDisjointFromNontrivialZeros
    sourceCriterionData
```

The finite-set admissibility row has an existing concrete CC20 triple proof:

```text
ConnesWeilRH/Source/CC20RHExit.lean:35-60
  SourceFiniteSetAdmissibility stores zero/half/one membership and
  RouteFiniteVanishingSetIsCC20Triple.

  cc20_triple_finite_set_admissibility proves the row for
  cc20TripleFiniteVanishingSet.
```

The source disjointness row is a real Prop boundary:

```text
ConnesWeilRH/Source/CC20RHExit.lean:42-45
  SourceFiniteSetDisjointFromNontrivialZeros B F :=
    ∀ p : CriticalVanishingPoint,
      p ∈ F -> ¬B.sourceNontrivialZero (criticalVanishingPointValue p)
```

The source package can produce triple vanishing once it exists:

```text
ConnesWeilRH/Source/CC20RHExit.lean:435-444
  triple_vanishing_statement_of_source_package
```

The source package can produce a CC20 exit object:

```text
ConnesWeilRH/Source/CC20RHExit.lean:609-619
  SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
```

The existing CC20 source-model witness is wrapper-only for this root:

```text
ConnesWeilRH/Source/CC20.lean:80-112
  CC20FiniteVanishingRhExitData stores:
    sourceFiniteVanishingCriterionPackage :
      SourceFiniteVanishingCriterionPackage rhDefinitionBridge

  CC20FiniteVanishingRhExitWitness.ofSourcePackage accepts the whole source
  package as input and proves only the conversion equality by rfl.
```

The final route uses the CC20 exit to get SourceRH:

```text
ConnesWeilRH/Route/RouteTheorem.lean:3543-3557
  cc20_source_rh_of_route_certificate
  final_connes_weil_rh
```


## 5. First-Principles Dependency Chain

The route-level proof already has this shape:

```text
RouteCertificate
  -> CC20 source RH
  -> RHDefinitionBridge.source_rh_to_mathlib_rh
  -> _root_.RiemannHypothesis
```

The hard missing producer has this shape:

```text
finite-vanishing admissible set
  + disjointness from source nontrivial zeros
  + Proposition C.1 source criterion
  -> CC20RHExitObjectPackage
  -> source-object package
  -> RouteCertificate
```

The independent generators are:

```text
finiteVanishingSet:
  a concrete Finset CriticalVanishingPoint, expected to be the CC20 triple.

finiteSetAdmissible:
  proof that the set is the accepted triple.

finiteSetDisjointFromNontrivialZeros:
  source-side exclusion of those points.

sourceCriterionData:
  the real CC20 Proposition C.1 exit:
    CC20PropositionC1InputData -> SourceRH.
```

The last two generators are the hard ones.  Neither can be a projection theorem
from the package that this root is trying to construct.

Direct closure theorem chain:

```text
Source.cc20TripleFiniteVanishingSet
  + Source.cc20_triple_finite_set_admissibility
  + normalizedCoreCC20TripleDisjointFromStandardSourceNontrivialZeros
  + normalizedCoreCC20PropositionC1StandardSourceCriterion
  -> normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
  -> Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
  -> normalizedCoreCC20RHExitObjectPackageFromTheorems
```

The two new hard theorems have exact target types:

```lean
theorem normalizedCoreCC20TripleDisjointFromStandardSourceNontrivialZeros :
    Source.SourceFiniteSetDisjointFromNontrivialZeros
      Source.RHDefinitionBridge.standard
      Source.cc20TripleFiniteVanishingSet := by
  ...

theorem normalizedCoreCC20PropositionC1StandardSourceCriterion :
    ∀ input : WeilPositivityInput,
      Source.CC20PropositionC1InputData
        Source.RHDefinitionBridge.standard
        Source.cc20TripleFiniteVanishingSet
        input ->
      Source.RHDefinitionBridge.standard.SourceRH := by
  ...
```

These theorem names are preferred because they state the mathematical boundary
directly:

```text
CC20TripleDisjointFromStandardSourceNontrivialZeros
  says the three CC20 exceptional points are not standard source nontrivial
  zeros.

CC20PropositionC1StandardSourceCriterion
  says the CC20 Proposition C.1 input data imply standard SourceRH.
```

The second theorem is the real RH exit.  It may use CC20 positivity,
triple-vanishing, and finite-set disjointness data from the input.  It may not
read a stored SourceRH, stored Mathlib RH, or the package being constructed.


## 6. Implementation Route

### Phase 1: search for an existing lower source criterion

Run:

```text
rg -n "SourceFiniteVanishingCriterionPackage|sourceCriterionData|propositionC1SourceCriterion|toCC20RHExitObjectPackage|finiteVanishingSet|SourceRH" ConnesWeilRH/Source ConnesWeilRH/Dev -g "*.lean"
```

Classify each candidate:

```text
real lower owner:
  constructs the package fields from lower facts, including:
    finiteSetDisjointFromNontrivialZeros
    sourceCriterionData

adapter:
  converts CC20RHExitObjectPackage <-> SourceFiniteVanishingCriterionPackage

rejected:
  stores SourceRH or Mathlib RH as an input field
  stores SourceFiniteVanishingCriterionPackage as a field without constructing
  its disjointness and criterion fields from lower facts
```

Expected result on the current tree:

```text
No existing no-argument lower source criterion is expected.

If the search result matches only the candidate classification table above,
stop direct closure and write the blocker report unless Peter explicitly
approves adding the two missing mathematical declarations as new source-layer
obligations.
```

### Phase 2A: direct completion if a lower source package exists

If a no-argument lower source package exists and its fields are built from
lower accepted facts:

```lean
noncomputable def normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems :
    Source.SourceFiniteVanishingCriterionPackage
      normalizedCoreRHDefinitionBridgeFromTheorems :=
  <lower accepted source criterion owner>

noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems :=
  Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
    normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
```

Before accepting this route, inspect the definition of
`normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems`.  If it uses
`SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
normalizedCoreCC20RHExitObjectPackageFromTheorems` or stores a source package
field supplied by another wrapper, reject it as a loop.

Concrete direct-completion edit if the two missing lower theorems already
exist:

```lean
noncomputable def normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems :
    Source.SourceFiniteVanishingCriterionPackage
      normalizedCoreRHDefinitionBridgeFromTheorems where
  finiteVanishingSet := Source.cc20TripleFiniteVanishingSet
  finiteSetAdmissibleData :=
    Source.cc20_triple_finite_set_admissibility
  finiteSetDisjointFromNontrivialZeros :=
    normalizedCoreCC20FiniteSetDisjointFromNontrivialZerosFromTheorems
  sourceCriterionData :=
    normalizedCoreCC20PropositionC1SourceCriterionFromTheorems

noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems :=
  Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
    normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
```

The edit is rejected if either
`normalizedCoreCC20FiniteSetDisjointFromNontrivialZerosFromTheorems` or
`normalizedCoreCC20PropositionC1SourceCriterionFromTheorems` is introduced with
`sorry`, `axiom`, `constant`, `opaque`, `unsafe`, a raw SourceRH field, or a
stored Mathlib RH field.

### Phase 2C: direct closure by proving the two hard CC20 theorems

This is the complete route that solves Plan 05.

Add the two theorem producers in the lowest module that owns the mathematics.
Preferred owner:

```text
ConnesWeilRH/Source/CC20RHExit.lean
```

If the proof needs source-object or route data, do not put a no-argument theorem
in `Dev/UnconditionalSkeleton.lean`.  Introduce a parameterized source theorem
in the owning source/route module, then instantiate it in Dev with the normalized
objects.

Required declarations:

```lean
theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet := by
  ...

theorem cc20_proposition_c1_standard_source_criterion :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData
        RHDefinitionBridge.standard
        cc20TripleFiniteVanishingSet
        input ->
      RHDefinitionBridge.standard.SourceRH := by
  ...
```

Then instantiate Dev:

```lean
theorem normalizedCoreCC20TripleDisjointFromStandardSourceNontrivialZeros :
    Source.SourceFiniteSetDisjointFromNontrivialZeros
      Source.RHDefinitionBridge.standard
      Source.cc20TripleFiniteVanishingSet :=
  Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros

theorem normalizedCoreCC20PropositionC1StandardSourceCriterion :
    ∀ input : WeilPositivityInput,
      Source.CC20PropositionC1InputData
        Source.RHDefinitionBridge.standard
        Source.cc20TripleFiniteVanishingSet
        input ->
      Source.RHDefinitionBridge.standard.SourceRH :=
  Source.cc20_proposition_c1_standard_source_criterion
```

Build the source package:

```lean
noncomputable def normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems :
    Source.SourceFiniteVanishingCriterionPackage
      normalizedCoreRHDefinitionBridgeFromTheorems where
  finiteVanishingSet := Source.cc20TripleFiniteVanishingSet
  finiteSetAdmissibleData :=
    Source.cc20_triple_finite_set_admissibility
  finiteSetDisjointFromNontrivialZeros :=
    normalizedCoreCC20TripleDisjointFromStandardSourceNontrivialZeros
  sourceCriterionData :=
    normalizedCoreCC20PropositionC1StandardSourceCriterion
```

Replace the old root:

```lean
noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems :=
  Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
    normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
```

This closes Plan 05 only if `#print axioms` for both hard theorems is clean.
The package and conversion proofs are not enough by themselves.

Proof obligations for the two hard theorems:

```text
cc20_triple_disjoint_from_standard_source_nontrivial_zeros:
  For p in {0, 1/2, 1}, prove that
  RHDefinitionBridge.standard.sourceNontrivialZero
    (criticalVanishingPointValue p)
  is false.

  Expected proof inputs:
    p = zero:
      standard source nontrivial zero includes zeta zero, no negative even,
      and no pole.  Show the value 0 cannot satisfy the standard nontrivial
      zero predicate.

    p = half:
      show the standard source predicate excludes the point 1/2 as a
      nontrivial zero unless the zeta-zero component is available.  If the
      current standard predicate allows any zeta zero on the critical line,
      this branch needs a real theorem about zeta(1/2), or the finite set is
      mis-specified.

    p = one:
      use the `not_pole` component of standard source nontrivial zero because
      criticalVanishingPointValue one = 1.

cc20_proposition_c1_standard_source_criterion:
  Given CC20PropositionC1InputData for the CC20 triple and a Weil positivity
  input, prove standard SourceRH:
    ∀ s, standard.sourceNontrivialZero s -> standard.sourceCriticalLine s.

  The proof must use the CC20 Proposition C.1 mathematical argument:
    finite-set disjointness
    triple-vanishing match
    full Weil positivity
    exclusion of off-critical-line nontrivial zeros

  If the current Lean tree has no theorem converting those four inputs into
  standard SourceRH, this theorem is the first non-Mathlib black box.
```

### Phase 2C no-black-box formalization route

This subsection replaces the earlier blocker-only route for Peter's
2026-07-07 request.  It gives the complete implementation shape for the two
hard theorem producers.  It does not allow a theorem import, accepted-source
packet, `axiom`, `constant`, `opaque`, `unsafe`, `sorry`, or a new record whose
field is proposition C.1.

Current code facts this route must preserve:

```text
Source.cc20TripleFiniteVanishingSet
  file: ConnesWeilRH/Source/CC20RHExit.lean
  lines: 21-29
  fact:
    the route finite set is exactly {zero, half, one}, with values
    0, 1/2, and 1.

Source.SourceFiniteSetDisjointFromNontrivialZeros
  file: ConnesWeilRH/Source/CC20RHExit.lean
  lines: 42-45
  fact:
    disjointness means every point in the finite set is not a
    B.sourceNontrivialZero at its criticalVanishingPointValue.

Source.CC20PropositionC1InputData
  file: ConnesWeilRH/Source/CC20RHExit.lean
  lines: 66-75
  fact:
    the current input stores finite-set equality, finite-set disjointness,
    route triple vanishing, and input.fullWeilPositivity.  It does not contain
    a theorem that arbitrary standard nontrivial zeros lie on the critical
    line.

Source.CC20PropositionC1SourceCriterion
  file: ConnesWeilRH/Source/CC20RHExit.lean
  lines: 89-92
  fact:
    the desired theorem has type
      CC20PropositionC1InputData B F input -> B.SourceRH.

Source.RHDefinitionBridge.standard
  file: ConnesWeilRH/Source/RHDefinition.lean
  lines: 367-395
  fact:
    standard.sourceNontrivialZero is MathlibNontrivialZero, and
    standard.sourceCriticalLine is s.re = 1 / 2.

Source.MathlibNontrivialZero
  file: ConnesWeilRH/Source/RHDefinition.lean
  lines: 46-49
  fact:
    a standard nontrivial zero is a zeta zero, not a negative even trivial
    zero, and not the pole point 1.
```

#### Phase 2C-A: prove the eta side condition, then the finite-set disjointness theorem

Owner module:

```text
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
```

Current clean declaration:

```lean
namespace ConnesWeilRH
namespace Source

def RiemannZetaHalfNonvanishing : Prop :=
  riemannZeta (1 / 2 : ℂ) ≠ 0

theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
    (hhalf : RiemannZetaHalfNonvanishing) :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet

end Source
end ConnesWeilRH
```

This theorem is not Plan 05 closure.  It proves that the only missing
disjointness side condition is `riemannZeta (1 / 2 : ℂ) ≠ 0`.

Missing lower declarations:

```lean
noncomputable def dirichletEtaReal (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n) / ((n + 1 : ℝ) ^ x)

noncomputable def dirichletEtaRealHalfOrdered : ℝ :=
  Classical.choose etaHalfTerm_alternating_tendsto

theorem dirichletEtaRealHalfOrdered_pos :
    0 < dirichletEtaRealHalfOrdered

theorem dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half :
    (dirichletEtaRealHalfOrdered : ℂ) =
      ((1 : ℂ) - (2 : ℂ) ^ (1 - (1 / 2 : ℂ))) *
        riemannZeta (1 / 2 : ℂ)

theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : ℂ) ≠ 0
```

The proof of `dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half` must be
expanded.  It cannot be introduced as a source fact.  Required submodules and
theorem families:

```text
ConnesWeilRH/Source/DirichletEta.lean
  Defines the real and complex Dirichlet eta series.

  Required theorem:
    dirichletEtaRealHalfOrdered_tendsto
      The ordered half-point alternating eta partial sums converge to
      `dirichletEtaRealHalfOrdered`.

  Required theorem:
    dirichletEta_complex_eq_one_sub_two_cpow_mul_riemannZeta_of_one_lt_re
      For 1 < s.re,
        eta(s) = (1 - 2^(1-s)) * riemannZeta s.

  Required theorem:
    analyticOn_dirichletEta_complex_re_pos
      eta is analytic on {s : ℂ | 0 < s.re}.

  Required theorem:
    analyticOn_one_sub_two_cpow_mul_riemannZeta_re_pos
      (1 - 2^(1-s)) * riemannZeta s is analytic on {s : ℂ | 0 < s.re}.
      The pole of zeta at 1 must be canceled by the zero of 1 - 2^(1-s).

  Required theorem:
    dirichletEta_eq_factor_mul_riemannZeta_of_re_pos
      Identity theorem extension from 1 < s.re to 0 < s.re.

  Rejected theorem:
    dirichletEta_half_eq_dirichletEtaReal_half
      This cannot be used while the half-point value is represented by
      unordered `tsum`.
```

The positivity proof for `dirichletEtaRealHalfOrdered_pos` must use the alternating
series bounds already available in Mathlib:

```text
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean
  alternating-series convergence and partial-sum bounds.
```

The proof shape is:

```text
a_n = (n + 1)^(-1/2)
  |
  +-- a_n is positive
  +-- a_n is antitone
  +-- a_n tends to 0
  v
alternating-series bound:
  1 - etaHalfTerm 1 <= dirichletEtaRealHalfOrdered
  |
  +-- 0 < 1 - 1 / sqrt(2)
  v
0 < dirichletEtaRealHalfOrdered
```

Once `riemannZeta_half_ne_zero` exists, add the unconditional finite-set theorem:

```lean
theorem cc20_triple_disjoint_from_standard_source_nontrivial_zeros :
    SourceFiniteSetDisjointFromNontrivialZeros
      RHDefinitionBridge.standard
      cc20TripleFiniteVanishingSet := by
  exact
    cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
      riemannZeta_half_ne_zero
```

The current project has no proof of `riemannZeta_half_ne_zero`.  Mathlib gives
`riemannZeta_ne_zero_of_one_le_re`, which does not apply at `s = 1/2`.

Do not weaken the finite set.  The README and manuscript fix
`F = {0, 1/2, 1}` because the CC20 convention maps the three route vanishings to
those points:

```text
README.md:345-369
docs/manuscripts/connes-weil-rh-proof-draft.md:1231-1260
docs/manuscripts/connes-weil-rh-proof-draft.md:1273-1291
```

#### Phase 2C-B: formalize Proposition C.1 rather than storing it

The current `WeilPositivityInput.fullWeilPositivity : Sort 1` in
`ConnesWeilRH/Basic.lean:421-429` is too abstract to prove Proposition C.1.
The no-black-box implementation must expose the analytic CC20 predicates that
Proposition C.1 consumes.

Owner modules:

```text
ConnesWeilRH/Source/CC20TestSpace.lean
ConnesWeilRH/Source/CC20WeilInequality.lean
ConnesWeilRH/Source/CC20YoshidaCriterion.lean
ConnesWeilRH/Source/CC20PropositionC1.lean
```

Required source-level data definitions:

```lean
namespace ConnesWeilRH
namespace Source

structure CC20TestSpace where
  Test : Type
  toRouteTest : Test -> TestFunction
  mellinAt : Test -> ℂ -> ℂ
  starConvolution : Test -> Test
  weilLocalSum : Test -> ℝ
  compactSupportSmooth : Test -> Prop

def CC20VanishesOn
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (g : C.Test) : Prop :=
  ∀ p : CriticalVanishingPoint,
    p ∈ F -> C.mellinAt g (criticalVanishingPointValue p) = 0

def CC20WeilNonpositive
    (C : CC20TestSpace)
    (g : C.Test) : Prop :=
  C.weilLocalSum (C.starConvolution g) <= 0

def CC20FiniteVanishingWeilCriterion
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ g : C.Test,
    C.compactSupportSmooth g ->
      CC20VanishesOn C F g ->
        CC20WeilNonpositive C g

end Source
end ConnesWeilRH
```

Required bridge from the route input to the CC20 predicate:

```lean
structure CC20RouteInputRealizesFiniteVanishingCriterion
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) where
  routeInputIsCC20Criterion :
    input.fullWeilPositivity ->
      CC20FiniteVanishingWeilCriterion C F
  routeTripleVanishingIsMellinVanishing :
    input.tripleVanishing ->
      ∀ g : C.Test,
        C.compactSupportSmooth g ->
          CC20VanishesOn C F g
```

This record is not a proof of C.1.  It only connects current route predicates to
the explicit CC20 predicates.  It must be supplied by existing route sign and
Mellin bridge theorems, including the final sign equality:

```text
QW(g,g) = - sum_v W_v(F_g)
```

Real code anchors for that bridge:

```text
ConnesWeilRH/Route/Exhaustion.lean:19-31
  FullWeilPositivity and toWeilPositivityInput.

ConnesWeilRH/Route/Bridge.lean
  SourceQWEqualsNegCC20WeilSum and restricted-to-full / final sign bridge data.

ConnesWeilRH/Source/Objects.lean:263-279
  sourceMellinVanishing, sourceQWNonnegative, sourceCC20WeilNonpositivity,
  and sourceCC20PropositionC1 fields.
```

Current Yoshida / Proposition C.1 theorem stack:

```lean
structure YoshidaDetector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (rho : ℂ) where
  test : C.Test
  compactSupportSmooth : C.compactSupportSmooth test
  vanishesOnF : CC20VanishesOn C F test
  detectsRho : C.mellinAt test rho ≠ 0
  weilSumPositiveIfOffLine :
    RHDefinitionBridge.standard.sourceNontrivialZero rho ->
      rho.re ≠ 1 / 2 ->
        0 < C.weilLocalSum (C.starConvolution test)

def CC20YoshidaDetectorExists
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ {rho : ℂ},
    RHDefinitionBridge.standard.sourceNontrivialZero rho ->
      rho.re ≠ 1 / 2 ->
        Nonempty (YoshidaDetector C F rho)

theorem cc20_proposition_c1_from_yoshida_detector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (hfinite : SourceFiniteSetAdmissibility F)
    (hdisjoint :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard F)
    (hexists : CC20YoshidaDetectorExists C F)
    (hcriterion :
      CC20FiniteVanishingWeilCriterion C F) :
    RHDefinitionBridge.standard.SourceRH := by
  ...
```

This theorem is conditional infrastructure.  It does not close Plan 05 because
`CC20YoshidaDetectorExists` still needs a concrete proof.

Rejected detector theorem shape:

```lean
theorem yoshida_detector_exists
    (C : CC20TestSpace)
    ...
    Nonempty (YoshidaDetector C F rho)
```

Reason: the statement is false for arbitrary `C`; take `C.Test = Empty`.

The record `YoshidaDetector` may not be accepted as an input field.  A concrete
detector theorem must be proved from definitions of the CC20 test space and
must include these proof components:

```text
1. finite interpolation:
     construct a compactly supported smooth multiplicative test with Mellin
     zeros on F and a nonzero Mellin value at rho.

2. finite-set preservation:
     multiplying by the vanishing polynomial for F does not destroy compact
     support or smoothness.

3. off-line sign:
     for a standard nontrivial zero rho with rho.re ≠ 1/2, the Yoshida
     detecting test gives a positive local Weil sum.

4. compatibility with Mathlib zeta:
     standard.sourceNontrivialZero rho is exactly MathlibNontrivialZero rho,
     by ConnesWeilRH/Source/RHDefinition.lean:367-427.
```

Then add the source criterion theorem:

```lean
theorem cc20_proposition_c1_standard_source_criterion
    (C : CC20TestSpace)
    (hexists :
      CC20YoshidaDetectorExists C cc20TripleFiniteVanishingSet)
    (hrealize :
      ∀ input : WeilPositivityInput,
        CC20RouteInputRealizesFiniteVanishingCriterion
          C cc20TripleFiniteVanishingSet input) :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData
        RHDefinitionBridge.standard
        cc20TripleFiniteVanishingSet
        input ->
      RHDefinitionBridge.standard.SourceRH := by
  intro input hdata
  exact
    cc20_proposition_c1_from_yoshida_detector
      C
      cc20TripleFiniteVanishingSet
      cc20_triple_finite_set_admissibility
      hdata.finiteSetDisjointFromNontrivialZeros
      hexists
      ((hrealize input).routeInputIsCC20Criterion
        hdata.fullWeilPositivity)
```

The final no-argument Dev theorem may instantiate `C` only after the route has a
concrete CC20 test-space owner:

```lean
noncomputable def normalizedCoreCC20TestSpaceFromTheorems :
    Source.CC20TestSpace := ...

theorem normalizedCoreCC20PropositionC1StandardSourceCriterion :
    ∀ input : WeilPositivityInput,
      Source.CC20PropositionC1InputData
        Source.RHDefinitionBridge.standard
        Source.cc20TripleFiniteVanishingSet
        input ->
      Source.RHDefinitionBridge.standard.SourceRH :=
  Source.cc20_proposition_c1_standard_source_criterion
    normalizedCoreCC20TestSpaceFromTheorems
    normalizedCoreCC20RouteInputRealizesFiniteVanishingCriterionFromTheorems
```

Do not introduce:

```lean
theorem cc20_proposition_c1_standard_source_criterion :
    ... := by
  exact Source.RHDefinitionBridge.mathlib_rh_to_source_rh ...
```

Do not introduce:

```lean
structure CC20PropositionC1Accepted where
  c1 : ∀ input, ... -> RHDefinitionBridge.standard.SourceRH
```

Both shapes only rename the old missing theorem.

#### Phase 2C-C: connect the no-black-box source theorem back to the existing package

After Phase 2C-A and Phase 2C-B build, add this declaration in
`ConnesWeilRH/Dev/UnconditionalSkeleton.lean`:

```lean
noncomputable def normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems :
    Source.SourceFiniteVanishingCriterionPackage
      normalizedCoreRHDefinitionBridgeFromTheorems where
  finiteVanishingSet := Source.cc20TripleFiniteVanishingSet
  finiteSetAdmissibleData :=
    Source.cc20_triple_finite_set_admissibility
  finiteSetDisjointFromNontrivialZeros :=
    Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  sourceCriterionData :=
    normalizedCoreCC20PropositionC1StandardSourceCriterion

noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems :=
  Source.SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage
    normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
```

This is the first point where `toCC20RHExitObjectPackage` may appear in the
producer path.  It is only an adapter after the finite-set disjointness theorem
and the CC20 C.1 source theorem exist with clean axiom output.

#### Phase 2C-D: no-black-box build and audit list

Run in this order:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Source.DirichletEta'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Source.ZetaHalfNonvanishing'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Source.CC20TestSpace ConnesWeilRH.Source.CC20WeilInequality ConnesWeilRH.Source.CC20YoshidaCriterion ConnesWeilRH.Source.CC20PropositionC1'

wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Route.RouteTheorem ConnesWeilRH.Dev.UnconditionalSkeleton'
```

Focused axiom audit must include:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

/- Missing final targets.  These may be audited only after they exist. -/
#check ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_pos
#print axioms ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_pos

#check ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half
#print axioms ConnesWeilRH.Source.dirichletEtaRealHalfOrdered_eq_factor_mul_riemannZeta_half

#check ConnesWeilRH.Source.riemannZeta_half_ne_zero
#print axioms ConnesWeilRH.Source.riemannZeta_half_ne_zero

#check ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
#print axioms ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros

/- Current clean infrastructure targets. -/
#check ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero
#print axioms ConnesWeilRH.Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros_of_zeta_half_ne_zero

#check ConnesWeilRH.Source.CC20YoshidaDetectorExists

#check ConnesWeilRH.Source.cc20_proposition_c1_from_yoshida_detector
#print axioms ConnesWeilRH.Source.cc20_proposition_c1_from_yoshida_detector

#check ConnesWeilRH.Source.cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors
#print axioms ConnesWeilRH.Source.cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
```

Accepted output for the new source theorems may contain only Mathlib / Lean
foundational axioms already present in adjacent analytic theorems.  Rejected
output:

```text
sorryAx
cc20 source theorem axiom
accepted-source theorem import
opaque constant
unsafe
project-local axiom
```

Rejected proof shapes:

```text
sourceCriterionData := fun _ _ => <stored SourceRH>
sourceCriterionData := fun _ _ =>
  Source.RHDefinitionBridge.mathlib_rh_to_source_rh ...
axiom cc20_proposition_c1_standard_source_criterion
opaque cc20_proposition_c1_standard_source_criterion
constant cc20_proposition_c1_standard_source_criterion
by
  intro input h
  exact False.elim ...
by
  intro input h
  exact trivial
True / Set.univ / empty finite set
SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
```

Acceptance for Phase 2C:

```text
Good:
  both hard theorems exist;
  both hard theorems have clean focused axiom output;
  normalizedCoreCC20RHExitObjectPackageFromTheorems is a conversion from the
  source package built from those theorems;
  downstream consumers no longer receive sorryAx from this root.

Partial / blocked:
  either hard theorem cannot be proved from existing Lean facts.
  Report the exact missing theorem and do not fill the root.
```

### Phase 2B: new lower owner if none exists

If the search finds only adapters, add a new source-layer owner first.  Do not
patch Dev directly.

Candidate shape:

```lean
structure CC20FiniteVanishingExitData
    (B : RHDefinitionBridge) where
  finiteVanishingSet : Finset CriticalVanishingPoint
  finiteSetAdmissibleData :
    SourceFiniteSetAdmissibility finiteVanishingSet
  finiteSetDisjointFromNontrivialZeros :
    SourceFiniteSetDisjointFromNontrivialZeros B finiteVanishingSet
  sourceCriterionData :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData B finiteVanishingSet input -> B.SourceRH

def CC20FiniteVanishingExitData.toSourcePackage
    (D : CC20FiniteVanishingExitData B) :
    SourceFiniteVanishingCriterionPackage B := ...
```

This shape still counts only if the two hard fields are proved from lower
accepted facts.  If those theorems do not exist, stop with a black-box report.

Do not add `CC20FiniteVanishingExitData` only to store the two missing fields
under new names.  That record is useful only after lower theorems exist.  If the
record constructor still asks the caller for:

```text
finiteSetDisjointFromNontrivialZeros
sourceCriterionData
```

then the implementation remains a specification boundary, not solved progress.

### Phase 3: keep the bridge standard

Check:

```text
normalizedCoreRHDefinitionBridgeFromTheorems =
  Source.RHDefinitionBridge.standard
```

Evidence:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1468-1470
```

Do not introduce a custom bridge to make the source predicate easier.

### Phase 4: route-facing verification

After replacement, inspect:

```text
rg -n "normalizedCoreCC20RHExitObjectPackageFromTheorems|normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems|normalizedSourceObjectCoreTheoremBaseDataFromTheorems|normalizedSourceObjectRHExitObjectFromTheorems|normalizedRhExitFromTheorems|normalizedSourceObjectPackageFromTheorems|normalizedRouteCertificateFromTheorems|normalizedNoArgumentRouteCertificatePackageFromTheorems|routeCertificateFromTheorems|cc20FiniteVanishingExitFromTheorems|rhDefinitionBridgeToMathlibFromTheorems" ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

The path must show the new package feeds the route.  A local source package
that no consumer uses is prep-only.

Declaration-level expected route after direct completion:

```text
normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems
  -> normalizedCoreCC20RHExitObjectPackageFromTheorems
  -> normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems.cc20RHExitObjectPackage
  -> normalizedSourceObjectCoreBasePackageFromTheorems
  -> normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.cc20RHExitObjectPackage
  -> normalizedSourceObjectRHExitObjectFromTheorems.sourceFiniteVanishingCriterionPackage
  -> normalizedRhExitFromTheorems
  -> normalizedRouteCertificateFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
  -> unconditional_rh_skeleton / unconditional_rh_contract_skeleton
```


## 7. Static Rejection Scans

Run before acceptance:

```text
rg -n "\\bsorry\\b|\\badmit\\b|^\\s*(axiom|constant|opaque|unsafe)\\b" ConnesWeilRH/Source/CC20RHExit.lean ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "mathlibRH\\s*:|\\.mathlibRH|SourceRH\\s*:=|RiemannHypothesis\\s*:=|sourceCriterionData\\s*:=\\s*by\\s*intro.*exact|propositionC1SourceCriterion\\s*:=\\s*by\\s*intro.*exact|Set\\.univ|\\bTrue\\b" ConnesWeilRH/Source ConnesWeilRH/Dev/UnconditionalSkeleton.lean -g "*.lean"

rg -n "normalizedCoreCC20RHExitObjectPackageFromTheorems|SourceFiniteVanishingCriterionPackage\\.ofCC20RHExitObjectPackage|SourceFiniteVanishingCriterionPackage\\.toCC20RHExitObjectPackage" ConnesWeilRH -g "*.lean"

rg -n "CC20FiniteVanishingRhExitData|CC20FiniteVanishingRhExitWitness|sourcePackage\\s*:\\s*SourceFiniteVanishingCriterionPackage|sourceFiniteVanishingCriterionPackage\\s*:" ConnesWeilRH/Source ConnesWeilRH/Dev/UnconditionalSkeleton.lean -g "*.lean"
```

The final scan must show that adapters consume a lower owner.  An adapter loop
or source-package storage record does not solve the root.


## 8. WSL Build Gate

Source build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Source.CC20'
```

Owning Dev build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Dev.UnconditionalSkeleton'
```

Route build:

```text
wsl -d Ubuntu-24.04 -- bash -lc 'cd /mnt/c/Projects/Connes-Weil-RH-Proof && lake build ConnesWeilRH.Route.RouteTheorem'
```

This route build is mandatory because the hard gate audits
`ConnesWeilRH.Route.cc20_source_rh_of_route_certificate` and the final route
exit path.


## 9. Focused Axiom Audit

Use a temporary scratch file outside the repo:

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseDataFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectRHExitObjectFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectRHExitObjectFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRhExitFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRhExitFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectPackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.routeCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.routeCertificateFromTheorems

#check ConnesWeilRH.Route.cc20_source_rh_of_route_certificate
#print axioms ConnesWeilRH.Route.cc20_source_rh_of_route_certificate

#check ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_skeleton

#check ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.unconditional_rh_contract_skeleton
```

Accepted producer output:

```text
[propext, Classical.choice, Quot.sound]
```

The final skeleton may still show `sorryAx` from other D1 roots.  This lane is
accepted only if this CC20 exit producer no longer contributes `sorryAx`.


## 10. Final Acceptance Text

Use this shape:

```text
Result:
  Good / partial / rejected.

Solved status:
  closed only if Result is Good.

  If Result is partial, this lane identified the first non-Mathlib black box
  but did not solve normalizedCoreCC20RHExitObjectPackageFromTheorems.

Old weak path removed:
  normalizedCoreCC20RHExitObjectPackageFromTheorems no longer uses `sorry`.

New semantic owner:
  <exact lower CC20 exit owner, or exact SourceFiniteVanishingCriterionPackage
  whose fields are supplied by lower accepted facts>

Semantic theorem:
  <exact theorem proving finiteSetDisjointFromNontrivialZeros>
  <exact theorem proving sourceCriterionData>

Concrete accepted names, if this plan is completed directly:
  normalizedCoreCC20FiniteSetDisjointFromNontrivialZerosFromTheorems
  normalizedCoreCC20PropositionC1SourceCriterionFromTheorems

Consumer rewires:
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  normalizedSourceObjectRHExitObjectFromTheorems
  normalizedRhExitFromTheorems
  normalizedSourceObjectPackageFromTheorems
  normalizedRouteCertificateFromTheorems
  normalizedNoArgumentRouteCertificatePackageFromTheorems
  routeCertificateFromTheorems

Semantic sufficiency:
  Explain why the disjointness row and source criterion prove
  RHDefinitionBridge.standard.SourceRH for the route's finite-vanishing and
  positivity input.

Build:
  <exact WSL commands and result>

Focused axiom audit:
  <target list and output>

Remaining black box:
  <exact declaration/type, if any>
```
