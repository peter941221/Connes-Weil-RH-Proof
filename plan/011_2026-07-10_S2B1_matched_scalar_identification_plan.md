# 011 S2-B1 Matched Scalar Diagnostic and Route-Cut Plan

Date: 2026-07-10

Status:
  Implemented and verified. The false universal scalar family is rejected and
  removed. The matched trace-front owner supplies the B2 scalar row, while the
  local-Weil consumer still requires a B3-equivalent global QW/pole row.

Verified outcome, 2026-07-10:

```text
universal scalar family       rejected by a concrete bump/zero counterexample
old no-argument scalar root   absent
selected scalar provenance    same SourceTraceReadOffData object
route B2 projection           proved from TraceFrontComparisonSplitB2Rows
current route cut             B2-only; QW/pole component remains B3/RH-level
Phase D bottom                concrete CC20 operator/kernel API is missing
unified WSL build             5 targets passed
focused import/axiom audit    passed; no sorryAx or replacement scalar root
```

The active `unconditional_rh_skeleton` still has six project-specific axioms:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The C1 criterion root and detector-criterion coverage root are already
RH-level outlets, not lower analytic producers.

AI session start:
  owner: root Codex session started 2026-07-10
  cwd: C:\Projects\Connes-Weil-RH-Proof
  lane: 011 S2-B1 universal-family rejection and matched B2 preservation
  old weak path: normalizedCoreS2B1ActualScalarIdentificationRoot
  files allowed:
    plan/011_2026-07-10_S2B1_matched_scalar_identification_plan.md
    ConnesWeilRH/Source/ObjectTheoremBasePackage.lean
    ConnesWeilRH/Source/S2B1TraceScale.lean
    ConnesWeilRH/Route/TraceFrontEnd.lean
    ConnesWeilRH/Route/CC20RouteRealization.lean
    ConnesWeilRH/Dev/UnconditionalSkeleton.lean
  files forbidden:
    ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean
    ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean
  smallest WSL build:
    lake build ConnesWeilRH.Source.ObjectTheoremBasePackage
      ConnesWeilRH.Source.S2B1TraceScale
      ConnesWeilRH.Route.TraceFrontEnd
      ConnesWeilRH.Route.CC20RouteRealization
      ConnesWeilRH.Dev.UnconditionalSkeleton
  focused axiom audit:
    import-facing #check and #print axioms for the declarations in section 15
  expected output:
    the false family has a concrete negation theorem; the old root and all
    no-argument producers derived from it are absent; selected matched scalar
    APIs take an explicit fixed-tuple witness; current route-cut guards retain
    their named B3 dependency.

Scope:
  Reject the false over-quantified S2-B1 scalar family, preserve the exact
  selected route tuple, and decide whether a matched support-square/QW-lambda
  theorem can bypass the rejected finite-prime B3 layer.


## 1. Result First

Current route judgment:

```text
selected finite-prime root
  restricted/global E-mass on one concrete canonical witness
    <-> filtered term-mass
    <-> unfiltered term-mass
    <-> selected scoped balance + psi=pole
    -> SourceRH

classification
  rejected as a lower finite-prime producer
```

S2-B1 has a separate status:

```text
S2-B1 support-square/QW-lambda equality
  = a B2 trace-front scalar obligation
  != a proved replacement for the rejected B3 root
```

No current Lean theorem sends any declaration named
`SupportSquareQWLambda`, `QWLambdaScalarIdentification`,
`ActualScalarIdentification`, or `TraceAmplitudeSquare` directly to
`SourceRH`. The current square-route proof still combines the scalar row with
finite-prime cancellation or an equivalent QW/psi-pole row.

The first accepted milestone must classify the old universal scalar family.
The second accepted milestone must classify the route cut. Consumer rewiring
comes after those two judgments.


## 2. Proven Source State

### 2.1 The verified final outlet remains RH-level

Current final outlet after the verified migration:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:7890

normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
  consumes:
    normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The consumer theorem is:

```text
selected_final_route_detector_criterion_coverage_sourceRH_from_08A
```

It combines detector criterion coverage with the proved Yoshida detector
existence theorem and returns `SourceRH`. This root is therefore already the
decisive sign criterion. It must not be renamed or repackaged as a lower
producer.

### 2.2 The old S2-B1 root is over-quantified

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1049

normalizedCoreS2B1ActualScalarIdentificationRoot :
  forall lambda > 1,
  forall archimedeanTest,
  forall weilTest,
    traceAmplitude(archimedeanTest)^2 = QW_lambda(lambda, weilTest, weilTest)
```

The three inputs vary independently. The family forces:

```text
traceAmplitude(g1)^2 = traceAmplitude(g2)^2

QW_lambda(lambda, f1, f1) = QW_lambda(lambda, f2, f2)

QW_lambda(lambda1, f, f) = QW_lambda(lambda2, f, f)
```

These consequences follow by transitivity through one fixed value on the
other side. They require no facts about CCM25 formulas.

### 2.3 The current concrete source model is a placeholder model

The current normalized core uses:

```text
SourceTestAlgebra.Test = TestFunction
legacy.encode = id
convolutionStar f g = f + g
convolutionSquare g = g + g

traceAmplitude g = norm (g 0)
```

Evidence:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean:3094-3140
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:53-55
ConnesWeilRH/Dev/UnconditionalSkeleton.lean:146-149
```

`normalizedCoreSourceWeilFormDataFromTheorems` also comes from the independent
axiom `normalizedCoreSourceWeilFormDataRoot`.

The repository therefore has no current basis for calling the encoded-value
scalar an actual Hilbert-Schmidt operator norm or for calling `f + g` the
manuscript convolution. 011 must use the phrase `current encoded-evaluation
scalar` until an operator model supplies the missing provenance.

### 2.4 The source and route already have matched owners

Do not introduce a parallel generic carrier before auditing these owners:

```text
source fixed tuple:
  S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData

source theorem-base tuple:
  SourceObjectTheoremBasePackage
  s2b1NormalizedSeedSupportSquareQWLambdaReadOffSourceData

trace-front exact package tuple:
  NormalizedSupportSquareQWLambdaSourceComparison
  NormalizedTraceAmplitudeSquareScalarContract

route-indexed source tuple:
  NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows r

route-indexed B2 owner:
  NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSplitB2Rows r
  NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r

route scalar proposition:
  NormalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda r
```

The square route already records:

```text
normalizedCC20TestSpace.toRouteTest
    (normalizedCC20TestSpace.starConvolution r.test)
  = r.sourceBackedTest.weilTest
```

The route scalar target already uses the same `r`, route test, cutoff, and
trace read-off object. A new carrier is justified only if these owners cannot
state the analytic theorem without losing data.


## 3. Correct Dependency Cut

The current proof has this shape:

```text
S2-B1 matched scalar row
  supportSquareTrace = QW_lambda
                    |
                    v
  positiveTrace = QW_lambda
                    |
                    |  plus pole-pairing transport
                    |  plus finite-prime archimedean cancellation
                    v
  polePairing(square) = positiveTrace
                    |
                    v
  local Weil sum = -positiveTrace <= 0
                    |
                    v
  detector contradiction -> SourceRH
```

Production evidence:

```text
NormalizedRouteBackedCC20SquareRestrictedTraceCalibrationRows
  contains:
    positiveTraceQWLambda
    finitePrimeArchimedeanCancellation

normalizedRouteBackedCC20SquareRestrictedPolePairingTraceFormula_of_qwLambda_cancellation
  consumes both rows
```

The route cut for 011 is therefore:

```text
Can a real theorem derive local Weil nonpositivity from the matched scalar
and lower source/operator facts without consuming any condition equivalent to:

  restricted/global E-mass
  term-mass
  finite-prime archimedean cancellation
  QW=pole
  psi=pole
  SourceRH
  no-off-line source-zero
```

Until Lean answers this question, S2-B1 remains a B2 diagnostic lane.


## 4. Hard Invariants

Every accepted matched theorem must preserve one route object:

```text
public test:
  r.test

square test:
  normalizedCC20TestSpace.starConvolution r.test

route Weil test:
  r.sourceBackedTest.weilTest

archimedean test:
  r.bridge.sourceTraceReadOff.archimedeanTest

cutoff and package:
  r.bridge.sourceTraceReadOff.lambda
  r.bridge.sourceTraceReadOff.ccm25ArithmeticPackage

source symbols:
  r.inputs.cc20.archimedeanSymbols
  r.inputs.ccm25.weilSymbols
```

Required rules:

```text
- index route-facing targets by `r`;
- state the raw-test/square-test/route-test relation explicitly;
- tie lambda to the stored arithmetic package;
- keep the same sourceRows witness through support-square and QW alignments;
- do not use Classical.choose to recover a second source object;
- do not store the desired scalar equality as a field below its producer;
- do not call the current encoded-value scalar an operator norm;
- specialize to Yoshida detectors after the route theorem, unless the target
  is explicitly a detector-scoped diagnostic.
```


## 5. Completion Outcomes

011 closes only through one of these outcomes.

### Outcome A: Universal family rejected and removed

Lean proves that the universal family implies amplitude-square constancy and
constructs two concrete Schwartz tests with unequal values at zero. The same
accepted change removes `normalizedCoreS2B1ActualScalarIdentificationRoot`
from the imported production graph.

### Outcome B: B2-only classification

Lean rewires the selected trace-front B2 consumer to an exact matched owner,
but the route cut still requires a B3-equivalent premise. The plan records
S2-B1 as a B2 cleanup lane and makes no final-producer claim.

### Outcome C: Lower route cut proved

Lean proves a local Weil nonpositivity or detector-criterion theorem from the
matched scalar plus named lower premises. Focused axiom audit confirms that no
B3-equivalent or RH-level declaration enters the theorem.

### Outcome D: Analytic model bottom exposed

The current placeholder model is rejected or replaced. One named theorem
remains, and its statement contains the actual operator/kernel, the exact
route test, and the stored cutoff package.

These results do not close 011:

```text
- constancy helper theorems while the false universal axiom remains imported;
- a new matched scalar Root axiom;
- a generic carrier detached from `r`;
- common-scalar wrappers;
- scalar-normal-form wrappers that retain the original equality as a field;
- a synthetic trace amplitude chosen from QW_lambda;
- a proof that uses finite-prime mass, QW=pole, psi=pole, or SourceRH;
- nonnegativity without the scalar equality;
- a final-outlet rewire that leaves the old root in transitive axioms.
```


## 6. Phase A: Reject the Universal Family

### A1. Name the family type

Introduce a non-axiom definition for the current family type so rejection
theorems do not depend on the root declaration name.

Target shape:

```lean
def NormalizedCoreS2B1ActualScalarIdentificationFamily : Prop :=
  forall lambda : Real, 1 < lambda ->
    forall archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
    forall weilTest : TestFunction,
      Source.NormalizedSeedQWLambdaScalarIdentification
        normalizedCoreS2B1NormalizedSeedFromTheorems
        normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
        normalizedCoreS2B1TracePackageRemaindersFromTheorems
        lambda
        (cast
          (congrArg ArchimedeanTraceSymbols.Test
            normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems.symm)
          archimedeanTest)
        weilTest
```

### A2. Prove the constancy consequences

```lean
theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_traceAmplitudeSquare_const

theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_qwLambda_test_const

theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_qwLambda_cutoff_const
```

Each theorem takes the family as an argument. Do not invoke the root axiom in
the proof.

### A3. Construct a concrete amplitude counterexample

The current concrete test algebra makes this branch direct:

```text
g0 = 0
  norm (g0 0)^2 = 0

g1 = smooth compactly supported bump with g1 0 = 1
  norm (g1 0)^2 = 1
```

Construction source and fixed arguments:

```text
Source.CC20YoshidaMellin.exists_testFunction_supported_Icc_eq_one
  (a := -1) (b := 1) (x := 0)
SourceConcreteBaseLayer.ConcreteTest = TestFunction
SourceConcreteBaseLayer.concreteLegacyTestEquiv.encode = id
```

Use `g0 := 0` and the returned `g1`. Rewrite
`normalizedCoreTraceAmplitudeFromTheorems` and the normalized-seed test/
amplitude projections before `norm_num`; do not ask `simp` to discover the
dependent archimedean cast.

Required theorem:

```lean
theorem normalizedCoreTraceAmplitudeSquare_not_constant :
  exists g0 g1,
    normalizedCoreTraceAmplitudeFromTheorems g0 ^ 2 !=
      normalizedCoreTraceAmplitudeFromTheorems g1 ^ 2
```

### A4. Reject the family

```lean
theorem not_normalizedCoreS2B1ActualScalarIdentificationFamily :
  not NormalizedCoreS2B1ActualScalarIdentificationFamily
```

This proof uses A2 and A3. It must not use facts about `SourceWeilFormData`.

### A5. Atomic false-axiom removal and API split

Do not land A4 while the production module still imports:

```text
axiom normalizedCoreS2B1ActualScalarIdentificationRoot :
  NormalizedCoreS2B1ActualScalarIdentificationFamily
```

That combination proves `False` and makes every downstream theorem vacuous.

Use one migration boundary:

```text
Source/ObjectTheoremBasePackage.lean:
  introduce S2B1TraceScaleRemainingConstructorInput with only:
    rankZeroModeConstructorInput
    noStripRankPoleConstructorInput
    endpointStripCdefConstructorInput
    noExtraBulkConstructorInput
    finitePartSourceNormalFormData

  change SourceObjectTheoremBasePackage and its constructor input to store
  S2B1TraceScaleRemainingConstructorInput instead of the universal
  S2B1TraceScaleAnalyticExclusionConstructorInput.

  keep S2B1TraceScaleAnalyticExclusionConstructorInput only as a compatibility
  input that can project toRemainingConstructorInput. Production package
  construction must not consume it.

Source/S2B1TraceScale.lean and Route/TraceFrontEnd.lean:
  remove package-only scalar producers. A fixed-tuple scalar consumer must take
  S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData or
  NormalizedSeedQWLambdaScalarIdentification as an explicit argument.

Dev/UnconditionalSkeleton.lean:
  remove normalizedCoreS2B1ActualScalarIdentificationRoot and its no-argument
  derived family. Build normalizedBaseFromTheorems from the remaining rows.
  introduce the data-bearing class
  NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider with no global
  instance. Its `input` field is the selected fixed-tuple witness. Lean keeps
  `[NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider]` in every
  dependent declaration signature, so the old no-argument graph cannot rebuild
  the scalar row. Delete compatibility declarations that have no non-scalar
  consumer.
```

The same milestone must run a transitive axiom audit for the final SourceRH
outlets and scan for `False.elim` plus the removed root.


## 7. Phase B: Reuse the Matched Route Owner

### B1. Use the existing route proposition

Primary route target:

```lean
NormalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda r
```

Do not define `NormalizedSeedMatchedScalarCarrier` as proposed in the older
plan. The existing route carrier already stores the selected test, square
test, source-backed test, trace data, cutoff, package, and symbols.

### B2. Use the existing source owner

Preferred source boundary:

```text
NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows r
+
NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignment
+
NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignment
```

Bundled form:

```text
NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSplitB2Rows r
```

The existing owner expresses the matched theorem. Use this exact chain:

```text
NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSplitB2Rows.ofTraceFrontComparisonRows
NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows.ofSplitB2Rows
normalizedRouteBackedCC20SquareRestrictedTraceReadOffEquality_of_traceFrontComparisonRows
normalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda_of_traceReadOffEquality
```

Do not add a carrier for B2.

### B3. Guard the common-scalar wrapper

For one fixed tuple, prove the equivalence between:

```text
NormalizedSeedQWLambdaScalarIdentification

and

Nonempty S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
```

The result classifies the read-off object as provenance for the same equality.
It does not produce the equality.


## 8. Phase C: Route-Cut Classification

### C1. Audit the named final-sign bridge

`SourceQWEqualsNegCC20WeilSum` currently stores compatibility and sign rows,
but its structure has no field stating:

```text
QW_lambda = -CC20 local Weil sum
```

`SourceQWNonnegativeToCC20Nonpositive` is an abbreviation of that structure.
Do not treat either name as the missing equality theorem.

### C2. Record the current route cut

The current named consumer is:

```text
normalizedRouteBackedCC20SquareRestrictedLocalWeilCriterion_of_traceFrontComparisonQWPoleRows
```

Its input `NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleRows r`
contains all four visible fields:

```text
polePairingTransport
traceFrontComparisonRows
finitePrimeIndexDifference
globalQWPoleCollapse
```

`globalQWPoleCollapse` is a B3-equivalent row. The current API therefore gives
Outcome B. A future lower route-cut attempt must introduce a concrete operator
row type first; 011 does not use an unnamed lower-row placeholder.

### C3. Named classification evidence

Use these declarations:

```text
normalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse_iff_psiPoleCollapse
normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonQWPoleCalibrationCoverage_iff_no_offline_source_zero
normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitQWPoleCoverage_iff_no_offline_source_zero
```

The first guard identifies the B3 spelling. The two detector guards prove that
promoting the current QW/pole route family to detector coverage reaches the
no-off-line source-zero level.

### C4. Decision

```text
Current decision:
  classify S2-B1 as B2-only.
  stop final-outlet rewiring in this lane after the false universal path is
  removed and the selected scalar boundary is conditional.
```


## 9. Phase D: Analytic Model Bottom

The current model is now exposed by three definitional diagnostics:

```lean
normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm
normalizedCoreConvolutionStar_eq_add
normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal
```

They prove that the encoded model currently has no operator-theoretic content:

```text
trace amplitude     = norm of the encoded test at zero
source convolution  = addition of test functions
Hilbert-Schmidt gate= traceClass and cyclicLegal
```

The first real Phase D bottom is therefore a concrete CC20 operator/kernel API
on the selected route carrier. It must supply the Hilbert space, the operator
or integral kernel attached to the exact route test, a genuine
Hilbert-Schmidt/trace-class predicate and norm, composition matching the
manuscript convolution square, and a trace or kernel-diagonal theorem that
identifies the resulting scalar with the stored route cutoff `QW_lambda`.
An abstract record whose fields can be chosen to force that equality does not
meet this boundary.

Run this phase only after Phase A removes the false family and Phase C shows a
useful route cut, or when the goal is to expose the exact B2 analytic bottom.

### D1. Audit the current encoded-evaluation scalar

Test these statements separately:

```text
model identity:
  Does the current source formula reduce to norm (g 0)^2?

operator provenance:
  Does a concrete CC20 operator have Hilbert-Schmidt norm equal to norm (g 0)?

convolution provenance:
  Does the manuscript convolution agree with the current `f + g` model?
```

Expected current result:
  operator and convolution provenance are missing. Record the first named API
  bottom rather than fitting `SourceWeilFormData` to the placeholder scalar.

### D2. Preferred theorem shape

```text
concrete CC20 operator/kernel on the selected route test
  |
  +-- Hilbert-Schmidt / trace-class legality
  +-- kernel composition for the correct convolution square
  +-- trace equals kernel-diagonal integral
  +-- explicit formula for the same cutoff package
  |
  v
operator Hilbert-Schmidt norm square
  = QW_lambda(stored lambda, stored route test, stored route test)
```

The theorem must identify the operator scalar with the route's
`supportSquareTrace`; it must not redefine `traceAmplitude` to make the target
reflexive.

### D3. Rejection branch

Reject the current model if Lean proves any of:

```text
- the encoded-evaluation scalar disagrees with the proposed operator norm;
- `f + g` cannot represent the required convolution;
- the exact route tuple cannot transport into the operator model;
- every proof of the route cut requires a B3-equivalent premise.
```


## 10. Phase E: Consumer Rewire

Start this phase only after a matched producer exists, or after the code has an
explicit conditional API that does not claim a no-argument proof.

Rewire in this order:

```text
1. fixed-tuple S2-B1 source row
2. SourceObjectTheoremBasePackage selected scalar interface
3. TraceFrontEnd normalized comparison
4. square-route B2 owner
5. detector-selected route input, only if Phase C accepted the route cut
6. final SourceRH outlet, only if no rejected premise remains
```

The active path must stop consuming:

```text
normalizedCoreS2B1ActualScalarIdentificationRoot
normalizedCoreS2B1ActualScalarIdentificationFromTheorems
normalizedActualScalarIdentificationFromTheoremBasePackage
normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
```

Compatibility declarations may retain old type names. No accepted production
declaration may retain the false axiom or derive a result through `False.elim`.


## 11. Dependency Tree

```text
011 S2-B1 matched scalar diagnostic
|
+-- A. Reject old universal family
|   |
|   +-- A1. name family type
|   +-- A2. constancy guards
|   +-- A3. zero/bump amplitude counterexample
|   +-- A4. prove family is false
|   +-- A5. remove false axiom atomically
|
+-- B. Preserve exact matched tuple
|   |
|   +-- B1. reuse route-indexed scalar proposition
|   +-- B2. reuse trace-front source rows and alignments
|   +-- B3. guard common-scalar wrappers as equivalent
|
+-- C. Classify the route cut
|   |
|   +-- C1. audit final-sign bridge names versus fields
|   +-- C2. state local-Weil criterion theorem
|   +-- C3. classify every non-scalar premise
|   +-- C4. accept final producer or mark B2-only
|
+-- D. Expose analytic model bottom
|   |
|   +-- D1. audit encoded-value and addition models
|   +-- D2. identify concrete operator/kernel theorem
|   +-- D3. prove or reject model compatibility
|
+-- E. Rewire consumers
    |
    +-- E1. source fixed tuple
    +-- E2. theorem-base selected interface
    +-- E3. TraceFrontEnd
    +-- E4. square route B2
    +-- E5. final outlet only after route-cut acceptance
```


## 12. File Ownership

Primary files:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Source/ObjectTheoremBasePackage.lean
ConnesWeilRH/Source/S2B1TraceScale.lean
ConnesWeilRH/Route/TraceFrontEnd.lean
ConnesWeilRH/Route/CC20RouteRealization.lean
```

Concrete model evidence:

```text
ConnesWeilRH/Source/AnalyticCoreBase.lean
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/CC20YoshidaConstruction.lean
```

Read-only until Phase D identifies a real operator owner:

```text
ConnesWeilRH/Source/CC20Concrete/TraceScale.lean
ConnesWeilRH/Source/CC20TraceModel.lean
ConnesWeilRH/Source/CCM25Concrete/Package.lean
```

The worktree contains live edits in `UnconditionalSkeleton.lean`,
`CC20RouteRealization.lean`, `FinitePrimeSourceDataBridge.lean`, and
`PrimePowerArithmetic.lean`. Read each diff before editing. Do not revert or
overwrite unrelated changes.


## 13. Static Audit

Run during development:

```powershell
git diff --check

rg -n "normalizedCoreS2B1ActualScalarIdentificationRoot|normalizedCoreS2B1ActualScalarIdentificationFromTheorems|normalizedActualScalarIdentificationFromTheoremBasePackage|normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage" ConnesWeilRH -g "*.lean"

rg -n "FinitePrimeArchimedeanCancellation|RestrictedQWPoleCollapse|GlobalQWPoleCollapse|PsiPoleCollapse|SourceRH|False\.elim|sorry|axiom|opaque" ConnesWeilRH/Source ConnesWeilRH/Route ConnesWeilRH/Dev -g "*.lean"
```

Static review must verify:

```text
- the selected tuple stays indexed by one `r`;
- sourceRows, support alignment, and QW alignment share one witness;
- lambda comes from the same sourceTraceReadOff/package;
- the old universal root is absent after rejection;
- no theorem uses False.elim to exploit the rejected axiom;
- route-cut premises are visible and classified;
- current placeholder models are not described as analytic operator results.
```


## 14. Milestone Build Gate

Run a build only after one substantial event:

```text
M1. the false universal root is removed with its consumers repaired;
M2. one selected B2 consumer uses the matched owner;
M3. the route cut is proved or rejected by named Lean declarations;
M4. the analytic model bottom changes.
```

Smallest expected targets:

```text
lake build ConnesWeilRH.Source.ObjectTheoremBasePackage
lake build ConnesWeilRH.Route.TraceFrontEnd
lake build ConnesWeilRH.Route.CC20RouteRealization
lake build ConnesWeilRH.Dev.UnconditionalSkeleton
```

Use the persistent ext4 WSL verification workflow, verify the mirror git root,
preserve `.lake`, and hold `/tmp/connes-weil-rh-lake.lock`.


## 15. Focused Axiom Audit

Phase A:

```lean
#print axioms normalizedCoreS2B1ActualScalarIdentificationFamily_implies_traceAmplitudeSquare_const
#print axioms normalizedCoreTraceAmplitudeSquare_not_constant
#print axioms not_normalizedCoreS2B1ActualScalarIdentificationFamily
```

Phase B/C:

```lean
#print axioms normalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda_of_traceFrontComparisonSplitB2Rows
#print axioms normalizedSeedQWLambdaScalarIdentification_nonempty_iff_supportSquareQWLambdaReadOffSourceData
#check normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems
#print axioms normalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse_iff_psiPoleCollapse
#print axioms normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonQWPoleCalibrationCoverage_iff_no_offline_source_zero
#print axioms normalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonSplitQWPoleCoverage_iff_no_offline_source_zero
```

Final outlets:

```lean
#print axioms normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
#print axioms unconditional_rh_skeleton
#print axioms unconditional_rh_contract_skeleton
```

Accepted output rules:

```text
- standard logical dependencies such as propext, Classical.choice, Quot.sound
  are allowed;
- no sorryAx;
- no normalizedCoreS2B1ActualScalarIdentificationRoot;
- no replacement matched-scalar Root axiom;
- no False-elimination dependency from the rejected family;
- a route-cut producer may not contain any B3/RH-level root.
```


## 16. Decision Table

```text
+----------------------------------+-----------------------------------------+
| evidence                         | decision                                |
+----------------------------------+-----------------------------------------+
| concrete amplitude counterexample| reject and remove universal family     |
+----------------------------------+-----------------------------------------+
| existing route owner is sufficient| reuse it; do not add a carrier         |
+----------------------------------+-----------------------------------------+
| route cut needs B3-equivalent row | classify S2-B1 as B2-only              |
+----------------------------------+-----------------------------------------+
| route cut uses lower operator data| accept candidate final producer        |
+----------------------------------+-----------------------------------------+
| current scalar fails operator test| reject encoded-evaluation model        |
+----------------------------------+-----------------------------------------+
| only wrappers move               | mark partial; no proof milestone        |
+----------------------------------+-----------------------------------------+
```


## 17. Immediate Execution Order

```text
1. Define the universal family type without an axiom.

2. Prove the three constancy guards from a family argument.

3. Construct zero and bump Schwartz tests and prove amplitude-square
   nonconstancy.

4. Prove the family false and remove the old root in the same atomic milestone.

5. Add the named SplitB2Rows projection theorem by composing the existing
   conversion, trace-read-off, and support-square theorems.

6. Record the current QW/pole local-Weil consumer and its four visible fields.

7. Use the existing QW/pole and detector equivalence guards to classify the
   current cut as B2-only.

8. Rewire B2 consumers only after a matched producer exists. Rewire final
   SourceRH consumers only after the route cut passes.

9. Run the smallest WSL builds and focused final-outlet axiom audit at the
   first substantial milestone.
```

The first coding round must reach the atomic universal-family rejection or a
named, concrete blocker in the Schwartz bump construction. It must not stop
after adding constancy helper theorems while the false axiom remains active.


## 18. Handoff Template

```text
AI session handoff:
  status: accepted / partial / blocked / rejected / analysis-only
  lane: 011 S2-B1 matched scalar diagnostic and route cut
  files changed:
  declarations changed:
  universal family rejection:
  old root removed:
  matched owner reused:
  route-cut judgment:
  remaining analytic model bottom:
  final-outlet root set:
  WSL build:
  focused axiom audit:
  next safe action:
```
