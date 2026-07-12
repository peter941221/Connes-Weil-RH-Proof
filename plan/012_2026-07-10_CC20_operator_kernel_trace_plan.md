# 012 CC20 Operator, Kernel, And S2-B1 Trace Plan

Date: 2026-07-10

Status: rejected by a source-level counterexample. No Lean implementation is
authorized under this plan.

The mathematical verdict is:

```text
docs/proofs/cc20-012-mathematical-verdict.md
```

It proves the fixed-S Hilbert-Schmidt/operator-kernel layer by a direct
commutator construction. It also proves that the planned exact no-defect
consumer is false in the archimedean specialization. CC20 Theorem `thmqkey1`
gives

```text
D o Q(xi * xi^*) = inner(xi, (-2 Id + K_I) xi),
```

with `K_I` compact Hilbert-Schmidt. This quadratic form remains nonzero for
some compact smooth `xi` with zero integral, so the resulting test vanishes at
`0` and `+/- i/2` while its trace remainder is nonzero. Therefore
`supportSquareTrace = qwLambda` cannot hold for the genuine source model on
the route's full triple-vanishing class.

Phase 0 must first produce source certificates for the fixed-S kernel estimate
and the remainder transport. It must also compile the project-local L2 operator
and ordinary-trace foundations without route trace assumptions. Source-module
implementation may proceed after those gates pass. Route consumers, Dev roots,
and legacy remainder records remain read-only until the selected analytic owner
has passed Phases 1-6.

Current execution authorization after the Phase 0A source audit:

```text
Phase 0A  fixed-S operator/kernel mathematics            passed
Phase 0A  exact no-defect remainder target               rejected
Phase 0B-7 Lean implementation and root retirement       denied
```

The completed mathematical audit selected these bottoms:

```text
direct K_S-invariant scattering coordinate        [available]
commutator Hilbert-Schmidt estimate               [proved]
L2 kernel representation                           [proved]
exact no-defect equality                           [false]
```

Evidence:

```text
docs/proofs/cc20-fixed-s-kernel-source-certificate.md
docs/proofs/cc20-fixed-s-remainder-source-certificate.md
```

The two S2-B1 roots remain active. The plan outcome is `rejected`: a lower
source theorem proves that the intended final equality is false.

Fresh WSL ext4 verification on 2026-07-10:

```text
lake build ConnesWeilRH.Dev.UnconditionalSkeleton                  passed
#check / #print unconditional_rh_skeleton                          passed
#print axioms unconditional_rh_skeleton                            six project roots
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot                   present
normalizedCoreS2B1TracePackageRemaindersRoot                       present
sorryAx                                                             absent
```

The first build replayed a stale `ObjectTheoremBasePackage` artifact. Rebuilding
that owning module, then rebuilding Dev, produced the import-facing result
above.

Result at plan entry: the repository does not prove RH unconditionally.

## 1. Objective

This plan replaces these two active Dev roots with source-owned analytic data:

```text
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
```

The replacement must build one selected CC20 trace object from a pre-trace
owner that contains no Hilbert-Schmidt, trace, cyclicity, or read-off
conclusions:

```text
RouteInputs, the source-backed route test g, S, I, and lambda
  -> its half-density convolution square F_g
  -> the theta-smoothed compressed operator A
  -> a concrete kernel for A
  -> a square-integrability proof for that kernel
  -> the Hilbert-Schmidt norm of A
  -> the ordinary positive trace of A* A
  -> five named trace-rearrangement witnesses
  -> the support-square trace
  -> the no-defect source trace
  -> the rank, pole, and Cdef remainder ledger
  -> SourceTraceReadOffData as a downstream compatibility view
```

The plan succeeds when `unconditional_rh_skeleton` no longer depends on either
S2-B1 root and the replacement declarations have import-facing axiom audits
without `sorryAx` or new project axioms.

Expected root graph after success:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot          [RH-level]
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot      [013]
normalizedCoreSourceWeilFormDataRoot                        [013]
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot   [RH-level, 014]
```

This expected result is still conditional. Removing two analytic data roots
does not remove the two RH-level outlets.

## 2. Scope

Plan 012 owns:

```text
CC20 Hilbert coordinate needed by the selected route test
theta-smoothed compressed operator identity
concrete operator kernel
Hilbert-Schmidt square-integrability
adjoint/composition kernel for the positive square
ordinary positive trace and nonnegativity
five cyclic-move witnesses
support-square trace read-off after legality
no-defect trace read-off after support square
rank, pole, projection-defect, and Cdef remainder ownership
selected S2-B1 package construction
removal of the two Dev S2-B1 roots
```

Plan 012 does not own:

```text
construction of SourceWeilFormData
finite-prime canonical atoms or package certificates
restricted/global finite-prime mass cancellation
QW_lambda equals pole or psi equals pole
detector criterion coverage
CC20 Proposition C1 source criterion
SourceRH, no-off-line source-zero, or Mathlib RH
```

The support-square-to-`QW_lambda` scalar read-off proved in 011 may be attached
only after the analytic owner proves the ordinary trace, support-square, and
no-defect equalities. The existing `SourceTraceReadOffData` cannot serve as a
producer input because it already stores `hilbertSchmidtGate`,
`positiveTraceNonnegative`, `fullTraceReadOffBridge`, and
`restrictedTraceReadOffBridge`.

The lower input boundary is:

```text
RouteInputs
SourceBackedFixedSTest inputs
archimedeanTest
lambda and oneLtLambda
source window/admissibility rows
test and quotient identity rows that do not contain trace conclusions
```

The plan constructs `SourceTraceReadOffData inputs g` only after those inputs
produce the selected analytic trace owner.

## 3. Entry Evidence

### 3.1 Six active roots

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:1053-1069` declares the two roots
owned by this plan:

```lean
axiom normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot :
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk
    normalizedCoreS2B1NormalizedSeedFromTheorems

axiom normalizedCoreS2B1TracePackageRemaindersRoot :
  Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
    normalizedCoreS2B1NormalizedSeedFromTheorems
```

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:8034-8035` closes the public
skeleton only after the route built from those roots:

```lean
theorem unconditional_rh_skeleton : _root_.RiemannHypothesis := by
  exact rhDefinitionBridgeToMathlibFromTheorems
```

The 011 focused audit found all six project roots in the axiom graph. This plan
may claim success only when both S2-B1 names disappear from that graph.

### 3.2 Current trace model is scalar encoding

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:191-208` defines positive trace as
the current support-square scalar.

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:216-228` proves:

```lean
theorem normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm ... :
    normalizedCoreTraceAmplitudeFromTheorems g =
      ‖normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0‖ := by
  rfl

theorem normalizedCoreConvolutionStar_eq_add ... :
    ...convolutionStar f g = f + g := by
  rfl
```

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:249-255` proves:

```lean
theorem normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal ... :
    normalizedCoreSourceTraceScaleDataFromTheorems.hilbertSchmidtGate g ↔
      normalizedCoreTraceClassFromTheorems g ∧
        normalizedCoreCyclicLegalFromTheorems g := by
  rfl
```

These are rejection guards. They show that the present model has no operator or
kernel semantics. A theorem that only repackages these definitions does not
advance 012.

### 3.3 Current Hilbert structures stop before operator theory

`ConnesWeilRH/Source/AnalyticCore.lean:843-859` defines
`SourceCanonicalHilbertModelData`. Its fields are:

```text
hilbertCarrier
NormedAddCommGroup
InnerProductSpace R
CompleteSpace
continuous linear equivalence to the place carrier
```

`ConnesWeilRH/Source/AnalyticCore.lean:1239-1274` defines
`SourceScalingActionData`. It supplies continuous linear scaling maps and their
unit/multiplication laws.

Neither structure contains:

```text
a complex Hilbert coordinate
a measure-space realization
an integral operator
a Schwartz kernel
an adjoint kernel
a Hilbert-Schmidt predicate or norm
a trace-class positive square
an ordinary infinite-dimensional trace
```

Plan 012 may reuse these structures as route coordinate and scaling-action
inputs. It may not cite them as completion of the analytic trace gate.

### 3.4 The two old root records overstate and mix obligations

`ConnesWeilRH/Source/ObjectTheoremBasePackage.lean:30-69` defines
`S2B1NormalizedCC20RemainderRowsOutsideNoBulk`. One record combines:

```text
source test selection
operator identity : Prop
forall-test Hilbert-Schmidt gate
per-move cyclicity : Prop
two remainder orientations
remainder object and Q image
fixed-S Sonin transport
projection-defect normal form
rank/pole ledger
endpoint-strip Cdef domination
no hidden positive defect
bounded comparison trace-ideal transport
```

`ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:951-997` defines
`CC20TracePackageRemainderData`. It repeats those fields and adds universal
no-bulk and finite-part statements.

`ConnesWeilRH/Source/CC20Concrete/TraceScale.lean:1004-1067` copies the record
into `CC20TraceObjectPackage`. The constructor obtains trace-square and
nonnegativity from the normalized scalar seed, rather than from an operator.

The active route needs one selected test. Requiring an analytic theorem for all
tests repeats the over-quantification error rejected in 011. Plan 012 introduces
a selected, data-bearing analytic owner and rewires the active package to it.
The old universal record may remain as a compatibility API, but it cannot feed
the no-argument route.

## 4. Research Evidence

### 4.1 Primary CC20 source

Primary source:

```text
Alain Connes and Caterina Consani
"Weil positivity and Trace formula, the archimedean place"
arXiv:2006.13771
PDF:  https://arxiv.org/pdf/2006.13771
HTML: https://ar5iv.labs.arxiv.org/html/2006.13771
Published: Selecta Mathematica 27 (2021), Paper 77
```

The abstract identifies the source of positivity as the trace of the scaling
action compressed to the orthogonal complement of the cutoff ranges.

The introduction defines the Hilbert space as `L^2(R)^ev`, the scaling action
as `theta`, and the Sonin projection as `S`. For a convolution square, it writes
the positive functional as:

```text
Tr(theta(g) S theta(g)*)
```

Theorem 1, formula (4), states for the specified compact support and Fourier
vanishing conditions:

```text
W_infinity(g * g*)
  >= Tr(theta(g) S theta(g)*)
```

The introduction also explains two kernel facts used by the proof:

```text
trace of a kernel operator = integral of diagonal kernel values
trace of a product = integral over the full square
```

The paper warns that the bare scaling kernel has a singular diagonal at scaling
parameter `1`. Section 1 handles that singularity through quantized calculus.
Plan 012 must keep the regularized source trace separate from the ordinary
positive trace.

The paper proves the single archimedean case. Its introduction says the
ingredients make sense in the semilocal setting, but that statement does not
prove the fixed-S theorem used by this repository. Every fixed-S Euler
multiplier, comparison map, and support projection remains an explicit 012
obligation.

Phase 0A must locate or derive the exact fixed-S kernel formula and estimate.
The project manuscript is a route draft, not an external theorem that can
discharge this gate. If Phase 0A cannot provide the formula and bound, the lane
stops with the kernel source certificate at Fork B; later phases remain design
targets.

The Phase 0 source audit writes
`docs/proofs/cc20-fixed-s-kernel-source-certificate.md`. The certificate must
contain this completed record in plain text:

```text
fixed-S set and character:
source Hilbert coordinate:
target complex L2 coordinate:
source and target measures:
theta_S(g) action formula:
P and P_hat action formulas:
A = P_hat P theta_S(g):
K_A(x,y) literal formula:
pointwise or integral majorant:
majorant square-integrability theorem:
dependency on S, I, lambda, and g:
primary-source theorem, formula, and page:
transport maps and preserved structures:
unsupported step, if any:
decision: pass / Fork B / Fork E / Fork F
```

A citation to a paper section, an abstract smoothing statement, or the project
manuscript does not complete the certificate. The certificate passes only when
another contributor can reconstruct the proposed Lean theorem statement from
the displayed formula and bound without choosing a new operator, kernel, or
majorant.

### 4.2 Semilocal coordinate source

Secondary source:

```text
Alain Connes, Caterina Consani, Henri Moscovici
"Zeta zeros and prolate wave operators"
arXiv:2310.18423v2
https://arxiv.org/html/2310.18423
```

Sections 3.1-3.2 give the archimedean Hardy-Titchmarsh and canonical scaling
coordinates. Sections 4.2, 4.5, and 4.6 construct the semilocal transform and
Sonin spaces. Section 4.8 identifies their Hilbertian realization.

This source supports the choice of Hilbert coordinate and semilocal Sonin
space. It does not discharge the exact theta-smoothed operator,
Hilbert-Schmidt estimate, five route cyclic moves, or the CCM25 read-off. Its
coordinate results may be inputs to Phase 0A; they cannot populate a trace
witness.

Phase 0 also writes
`docs/proofs/cc20-fixed-s-remainder-source-certificate.md`. This second
certificate prevents a successful positive-trace construction from reaching an
unexamined remainder bottom in Phase 5. It must identify:

```text
regularized source trace and its domain
Sonin trace and its domain
delta and Q(delta)
zero-mode and two Tate evaluation formulas
each projection-defect commutator
endpoint-strip factor and Cdef norm bound
fixed-S Euler transport theorem
bounded comparison map and inverse
W_infinity = L - D and W_infinity = S - E sources
no-hidden-defect equation source
decision: pass / Fork G / Fork H
```

The archimedean formulas may fill the archimedean rows. Each fixed-S row needs
a primary-source theorem or a derivation whose hypotheses and target spaces are
written in the certificate.

### 4.3 Project manuscript

`docs/manuscripts/connes-weil-rh-proof-draft.md:548-659` states the intended
fixed-S legality lemma. It defines:

```text
A_(S,lambda,g)
  = P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g)
```

and claims:

```text
A in S_2
A* A is trace-class
PositiveTrace = Tr(A* A)
```

The same section names five source ingredients:

```text
ThetaSmoothingSchwartzKernel
FixedSEulerPhaseTraceClass
WeightedProjectionDefectTraceClass
CyclicMoveWithSupportProjection
TraceClassCyclicSupportSquareIdentity
```

`docs/manuscripts/connes-weil-rh-proof-draft.md:661-669` lists five route trace
moves and the required trace-ideal input for each.

`docs/manuscripts/connes-weil-rh-proof-draft.md:797-859` fixes the object
identity and read-off order:

```text
F_g = g* * g
positive support-square trace
  -> fixed-S source trace after defect accounting
  -> QW_lambda main term
```

`docs/manuscripts/connes-weil-rh-proof-draft.md:939-966` repeats the key proof
shape: prove `A in S_2`, define `Tr(A* A)`, then rewrite the support-square trace
into the quantized-differential term plus rank, pole, and `Cdef` remainders.

`docs/manuscripts/connes-weil-rh-proof-draft.md:1308-1345` separates four
Hilbert coordinates and records the trace-class ledger. This plan must not
identify those spaces by notation. Each move uses a named equivalence or
bounded comparison map.

### 4.4 Existing theorem contract

`docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:56-358` already
names the contract groups:

```text
SourceTraceOperatorIdentity
SourceHilbertSchmidtForThetaSmoothedOperator
SourceTraceClassForPositiveSquare
SourcePositiveTraceEqualsOrdinaryTrace
SourcePositiveTraceNonnegative
SourceCyclicMoveWitnessLedger
SourceSupportSquareTraceAfterLegality
SourceNoDefectTraceAfterSupportSquare
SourceBoundedComparisonTraceIdealTransport
```

Plan 012 keeps these semantic names. It replaces abstract `Prop` sockets with
data-bearing kernel and trace witnesses.

### 4.5 Mathlib capability audit

Toolchain at plan entry:

```text
Lean    v4.30.0
Mathlib v4.30.0
```

`Mathlib/Analysis/InnerProductSpace/Trace.lean:22-56` assumes a finite index or
`FiniteDimensional` and proves trace formulas for finite-dimensional linear
maps.

Repository-wide source search found no usable declarations named:

```text
IsHilbertSchmidt
HilbertSchmidtOperator
TraceClass
nuclear operator
```

The implementation must not promise a nonexistent Mathlib framework. Plan 012
uses a project-local kernel trace for the exact class of operators needed by
the route.

## 5. First-Principles Design

### 5.1 Exact kernel trace class and ordinary trace

The route needs this implication:

```text
K_A is square-integrable
  -> A belongs to the exact project-local Hilbert-Schmidt kernel class
  -> A* A belongs to the exact positive trace kernel class
  -> the orthonormal-basis diagonal series converges
  -> that series is independent of the chosen orthonormal basis
  -> ordinaryTrace(A* A) = (integral |K_A(x,y)|^2 : Complex)
  -> positiveTrace := re(ordinaryTrace(A* A)) >= 0
```

The project need not build a Banach ideal library for every bounded operator.
It must still define ordinary trace independently of the target kernel
integral. Defining `trace := integral |K|^2` and then proving the same equality
would be circular. The project-local layer must use an orthonormal-basis
diagonal series, a nuclear decomposition, or an equivalent independent
construction and prove agreement with the kernel integral.

The coordinate must carry the countability or separability assumptions needed
to obtain a countable orthonormal basis. If the selected concrete L2 coordinate
cannot supply those assumptions, Phase 0B stops at
`SourceCC20OrdinaryTraceFoundation`.

### 5.2 The diagonal trap

An `L^2` kernel is an almost-everywhere equivalence class. Its diagonal has
product measure zero and need not have a well-defined representative. Therefore
this implication is invalid without extra regularity:

```text
K in L^2(X x X)
  -> trace(T_K) = integral K(x,x)
```

For the positive square, the kernel scalar is:

```text
PositiveKernelMass(K)
  := integral_(X x X) norm(K(x,y))^2
```

Plan 012 then proves that the complex ordinary trace for the selected regular
representative equals this real scalar embedded in `ℂ`. It never reads a
diagonal from an arbitrary `L^2` equivalence class. The coordinate therefore
includes the topology and regularity data used to select that representative.

### 5.3 Complex versus real Hilbert data

The current `SourceCanonicalHilbertModelData` is an inner-product space over
`R`. The source operators use Fourier phases, adjoints, and complex kernels.
Plan 012 adds a complex kernel coordinate rather than pretending the real
carrier already contains that structure.

The route still consumes a real scalar. The positive kernel integral is real:

```text
integral norm(K(x,y))^2
```

The compatibility theorem must identify that scalar with the current real
support-square trace. No cast from a complex trace value may be hidden in
`simp`.

### 5.4 Selected route ownership

The old package asks for `sourceHilbertSchmidtGate` for every test. The active
route consumes one `sourceTraceTest`. Plan 012 starts from a selected pre-trace
owner:

```text
SourceCC20PreTraceInputData
  contains RouteInputs and SourceBackedFixedSTest inputs
  contains archimedeanTest, S, I, lambda, and admissibility
  contains no HS, trace, cyclicity, or read-off conclusion
  |
  v
SelectedTraceOwner
  contains g
  contains F_g
  contains A(g)
  contains K_A
  contains all legality and remainder data for that same g
```

This change follows the 011 correction: prove the statement the route needs and
do not introduce a false universal family.

## 6. Reuse And Replacement Matrix

```text
+---------------------------------------------+----------+---------------------------------------------+
| existing object                             | action   | reason                                      |
+---------------------------------------------+----------+---------------------------------------------+
| SourceCanonicalHilbertModelData             | reuse    | Hilbert carrier and route coordinate only   |
| SourceScalingActionData                     | reuse    | scaling maps and group laws                 |
| RouteInputs and SourceBackedFixedSTest      | reuse    | lower route/test identity inputs            |
| SourceTraceReadOffData                      | rebuild  | downstream view; already stores conclusions |
| 011 support-square/QW read-off              | attach   | only after no-defect analytic read-off      |
| CC20SelectedTraceLegalityData               | replace  | stores Props, no operator/kernel            |
| sourceOperatorIdentity : Prop               | replace  | must project from exact operator data       |
| sourceHilbertSchmidtGate                    | replace  | must project from square-integrable kernel  |
| sourcePerMoveCyclicityLedger : Prop         | replace  | needs five named witnesses                  |
| positiveTrace : Test -> R                   | bridge   | legacy projection from ordinary trace       |
| traceClass / cyclicLegal                    | bridge   | legacy projections from analytic owner      |
| CC20TracePackageRemainderData               | bypass   | universal mixed record is too strong        |
| S2B1...RemainderRowsOutsideNoBulk           | project  | derive selected fields after construction   |
+---------------------------------------------+----------+---------------------------------------------+
```

## 7. Module Boundaries

Create these modules:

```text
ConnesWeilRH/Source/CC20KernelCoordinate.lean
ConnesWeilRH/Source/CC20OperatorKernel.lean
ConnesWeilRH/Source/CC20KernelTraceIdeal.lean
ConnesWeilRH/Source/CC20HilbertSchmidt.lean
ConnesWeilRH/Source/CC20PositiveTrace.lean
ConnesWeilRH/Source/CC20TraceRemainder.lean
```

Phase 0 creates these evidence documents before the source modules:

```text
docs/proofs/cc20-fixed-s-kernel-source-certificate.md
docs/proofs/cc20-fixed-s-remainder-source-certificate.md
docs/proofs/cc20-phase-0-compiled-contracts.md
```

`cc20-phase-0-compiled-contracts.md` records the exact `#check` output for each
foundation declaration, its owning module, and its smallest build. It may quote
only declarations that compile in the WSL verification environment. Proposed
signatures belong in this plan; compiled signatures belong in the certificate.

Responsibilities:

```text
CC20KernelCoordinate
  measure-space coordinate
  complex Hilbert carrier and L2 equivalence
  countable orthonormal basis
  no RouteInputs, selected test, operator, trace, or read-off data

CC20OperatorKernel
  pre-trace owner
  selected route test and convolution square
  theta-smoothed compressed operator
  concrete kernel and kernel-action identity

CC20KernelTraceIdeal
  countable orthonormal-basis trace definition
  basis-independence for the exact positive kernel class
  Hilbert-Schmidt product trace theorem
  trace-class-times-bounded cyclicity theorem

CC20HilbertSchmidt
  square-integrable kernel data
  HS norm square
  bounded projection/kernel preservation
  theta-smoothed selected operator estimate

CC20PositiveTrace
  adjoint kernel
  composition kernel
  independent ordinary trace of the positive square
  kernel-mass equality for the selected regular representative
  nonnegativity
  five cyclic-move witnesses

CC20TraceRemainder
  source trace remainder function
  Q image
  rank and Tate/pole channels
  projection-defect normal form
  endpoint-strip Cdef bound
  no-bulk and finite-part consequences
```

Integrate those modules into:

```text
ConnesWeilRH/Source/AnalyticCore.lean
ConnesWeilRH/Source/CC20Concrete/TraceScale.lean
ConnesWeilRH/Source/ObjectTheoremBasePackage.lean
ConnesWeilRH/Source/S2B1TraceScale.lean
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

Do not put kernel integration theory in `Dev/UnconditionalSkeleton.lean`. Dev
constructs the selected owner and projects it into the route.

## 8. Target Data APIs

The names below are the target API. Implementation may adjust binder order and
namespace qualification for Lean elaboration. It must preserve the stated data
and same-object invariants.

### 8.1 Pre-trace input boundary

The first owner contains route identity and admissibility data only:

```lean
structure SourceCC20PreTraceInputData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  archimedeanTest : inputs.cc20.archimedeanSymbols.Test
  lambda : ℝ
  oneLtLambda : 1 < lambda
  windowSupportContainment : WindowSupportContainment inputs g lambda
  testHalfDensityCompatibility : TestHalfDensityCompatibility inputs g
  fixedSCoordinateRows : SourceCC20FixedSCoordinateRows inputs g lambda
```

`SourceCC20PreTraceInputData` must not contain or project any of these fields:

```text
hilbertSchmidtGate
traceClass
cyclicLegal
positiveTraceNonnegative
fullTraceReadOffBridge
restrictedTraceReadOffBridge
SourceTraceReadOffData
```

The source-backed test parameter `g` owns `g.weilTest`; the pre-trace owner does
not invent a second test field.

### 8.2 Kernel coordinate

```lean
structure SourceCC20KernelCoordinateData where
  Point : Type
  [topologicalSpace : TopologicalSpace Point]
  [measurableSpace : MeasurableSpace Point]
  [opensMeasurableSpace : OpensMeasurableSpace Point]
  [secondCountableTopology : SecondCountableTopology Point]
  measure : MeasureTheory.Measure Point
  [sigmaFinite : MeasureTheory.SigmaFinite measure]
  complexHilbertCarrier : Type
  [normedAddCommGroup : NormedAddCommGroup complexHilbertCarrier]
  [innerProductSpace : InnerProductSpace ℂ complexHilbertCarrier]
  [completeSpace : CompleteSpace complexHilbertCarrier]
  l2Equiv :
    complexHilbertCarrier ≃L[ℂ]
      MeasureTheory.Lp ℂ 2 measure
  BasisIndex : Type
  [countableBasisIndex : Countable BasisIndex]
  orthonormalBasis :
    OrthonormalBasis BasisIndex ℂ complexHilbertCarrier
```

Phase 0B fixes the exact Mathlib instance syntax before route structures change.
If the concrete coordinate supplies separability through a different theorem,
the implementation may derive `BasisIndex` and `orthonormalBasis` rather than
store them.

Required coordinate rows:

```text
fixed-S source coordinate -> complex kernel coordinate
scaling action compatibility
orthogonal support projection compatibility
orthogonal Fourier-support projection compatibility
bounded comparison map and inverse
regular kernel representative compatibility
```

### 8.3 Exact selected operator/kernel owner

Use a data-bearing projection object rather than an arbitrary continuous linear
map:

```lean
structure SourceCC20OrthogonalProjectionData
    (coordinate : SourceCC20KernelCoordinateData) where
  operator : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  idempotent : operator.comp operator = operator
  selfAdjoint :
    ∀ x y, inner ℂ (operator x) y = inner ℂ x (operator y)
```

The exact selected operator owner is:

```lean
structure SourceCC20ThetaSmoothedOperatorKernelData
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (preTrace : SourceCC20PreTraceInputData inputs g)
    (coordinate : SourceCC20KernelCoordinateData) where
  convolutionSquare : TestFunction
  convolutionSquare_eq :
    convolutionSquare =
      inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest
  thetaOperator : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  thetaStarOperator : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  thetaStar_is_adjoint :
    ∀ x y, inner ℂ (thetaOperator x) y = inner ℂ x (thetaStarOperator y)
  thetaConvolutionSquareOperator :
    coordinate.complexHilbertCarrier →L[ℂ]
      coordinate.complexHilbertCarrier
  thetaStar_comp_theta :
    thetaStarOperator.comp thetaOperator = thetaConvolutionSquareOperator
  supportProjection : SourceCC20OrthogonalProjectionData coordinate
  fourierSupportProjection : SourceCC20OrthogonalProjectionData coordinate
  compressedOperator : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  compressedOperator_eq :
    compressedOperator =
      fourierSupportProjection.operator.comp
        (supportProjection.operator.comp thetaOperator)
  positiveSquareOperator : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  positiveSquareOperator_eq :
    positiveSquareOperator =
      thetaStarOperator.comp
        (supportProjection.operator.comp
          (fourierSupportProjection.operator.comp
            (supportProjection.operator.comp thetaOperator)))
  kernel : coordinate.Point → coordinate.Point → ℂ
  kernelMeasurable : Measurable (Function.uncurry kernel)
  kernelRegular : SourceCC20RegularKernelRepresentative coordinate kernel
  kernelActsAsCompressedOperator :
    SourceCC20KernelActionStatement coordinate kernel compressedOperator
```

The implementation proves `positiveSquareOperator_eq` from the projection and
adjoint laws. It does not accept that equality as an unrelated source premise.
`SourceCC20KernelActionStatement` states equality in the `L²` coordinate, not
pointwise equality of arbitrary representatives.

### 8.4 Square-integrable kernel and ordinary-trace foundation

#### 8.4.1 Contract freeze and representation choice

The project-local trace layer uses an explicit nuclear decomposition. It does
not introduce an unconstrained predicate named `TraceClass`. The implementation
must preserve this contract, with binder order adjusted only when Lean requires
it:

```lean
structure SourceCC20NuclearDecompositionData
    (coordinate : SourceCC20KernelCoordinateData)
    (operator : coordinate.complexHilbertCarrier →L[ℂ]
      coordinate.complexHilbertCarrier) where
  Index : Type
  [indexCountable : Countable Index]
  left right : Index → coordinate.complexHilbertCarrier
  normProductSummable : Summable (fun n => ‖left n‖ * ‖right n‖)
  operator_eq_tsum_rankOne :
    ∀ x, operator x = ∑' n, inner ℂ (right n) x • left n

abbrev SourceCC20TraceClassData
    (coordinate : SourceCC20KernelCoordinateData)
    (operator : coordinate.complexHilbertCarrier →L[ℂ]
      coordinate.complexHilbertCarrier) :=
  SourceCC20NuclearDecompositionData coordinate operator
```

The foundation defines the complex trace from the nuclear series and proves
agreement with every countable orthonormal-basis diagonal series:

```text
SourceCC20OrdinaryTrace data
  := sum' n, inner C (data.right n) (data.left n)

SourceCC20OrdinaryTrace_eq_basisSeries:
  SourceCC20OrdinaryTrace data
    = sum' n, inner C (basis n) (operator (basis n))

SourceCC20OrdinaryTrace_basisIndependent:
  the basis series has the same value for any two countable ONBs
```

The equality with the basis series proves independence from the chosen nuclear
decomposition. No route theorem may define ordinary trace from kernel mass.

Phase 0B must freeze and compile these semantic contracts:

```text
SourceCC20SquareIntegrableKernelToContinuousLinearMap:
  a measurable kernel with integrable norm square
    -> one continuous L2 operator
    -> its L2 kernel-action equality
    -> its operator-norm bound from the kernel mass

SourceCC20OrdinaryTraceFoundation:
  one nuclear decomposition
    -> summability of every ONB diagonal series
    -> equality of the nuclear and ONB series

SourceCC20HilbertSchmidtProductTrace:
  two square-integrable kernel operators
    -> nuclear decompositions of both products
    -> equality of the two ordinary traces

SourceCC20TraceClassBoundedCyclicity:
  one nuclear decomposition and one bounded operator
    -> nuclear decompositions of both products
    -> equality of the two ordinary traces
```

Each compiled declaration must expose the operator, kernel, measures, basis,
and product order in its type. A declaration returning an unnamed `Prop`, an
existential operator without an action equality, or a trace equality without
both product witnesses fails Phase 0B.

`SourceCC20FixedSKernelEstimate` is absent from Phase 0B. Phase 0A freezes its
literal formula and bound; Phase 1 constructs the exact `operatorKernel`; Phase
2 then proves the estimate for that object. This order removes the former
dependency cycle.

After Phase 0A passes, Phase 1 transcribes the two certified literal
expressions as definitions. These definitions may depend only on the pre-trace
inputs and coordinate data named in the certificate:

```text
SourceCC20CertifiedKernelFormula preTrace coordinate
SourceCC20CertifiedKernelMajorant preTrace coordinate
```

They are definitions, not fields. Their bodies must display the certified
formula and every `S`, `I`, `lambda`, and `g` dependency. Phase 2 uses this
fixed proposition:

```lean
def SourceCC20FixedSKernelEstimate
    (preTrace : SourceCC20PreTraceInputData inputs g)
    (coordinate : SourceCC20KernelCoordinateData)
    (operatorKernel :
      SourceCC20ThetaSmoothedOperatorKernelData preTrace coordinate) : Prop :=
  operatorKernel.kernel =
      SourceCC20CertifiedKernelFormula preTrace coordinate ∧
    (∀ x y,
      ‖operatorKernel.kernel x y‖ ≤
        SourceCC20CertifiedKernelMajorant preTrace coordinate x y) ∧
    MeasureTheory.Integrable
      (fun p =>
        (SourceCC20CertifiedKernelMajorant preTrace coordinate p.1 p.2) ^ 2)
      (coordinate.measure.prod coordinate.measure)
```

The implementation may adjust namespaces and dependent binder order. It may
not replace either certified definition with a structure field, existential
function, or value chosen from `operatorKernel`.

```lean
def SourceCC20KernelNormSq
    (kernel : X → X → ℂ) : X × X → ℝ :=
  fun p => ‖kernel p.1 p.2‖ ^ 2

structure SourceCC20HilbertSchmidtKernelData
    (operatorKernel : SourceCC20ThetaSmoothedOperatorKernelData preTrace coordinate)
    where
  sourceEstimate :
    SourceCC20FixedSKernelEstimate preTrace coordinate operatorKernel
  normSqIntegrable :
    MeasureTheory.Integrable
      (SourceCC20KernelNormSq operatorKernel.kernel)
      (coordinate.measure.prod coordinate.measure)
```

Define the norm square; do not store a free scalar:

```lean
def SourceCC20HilbertSchmidtKernelData.hsNormSq
    (hs : SourceCC20HilbertSchmidtKernelData operatorKernel) : ℝ :=
  ∫ p, SourceCC20KernelNormSq operatorKernel.kernel p
    ∂(coordinate.measure.prod coordinate.measure)
```

The project-local trace layer defines ordinary trace independently:

```text
SourceCC20TraceClassData T
SourceCC20PositiveKernelClass T K
SourceCC20OrdinaryTrace (traceClass : SourceCC20TraceClassData T) : ℂ
SourceCC20OrdinaryTrace_eq_basisSeries
SourceCC20OrdinaryTrace_basisIndependent
SourceCC20PositiveSquare_traceClass
```

`SourceCC20OrdinaryTrace` uses the convergent diagonal series over the selected
countable orthonormal basis. The basis-independence theorem shows that the
result does not depend on that basis. It accepts a trace-class witness, so code
cannot request the trace of an arbitrary continuous operator. The kernel
theorem then proves that the complex trace of the positive square equals the
real `hsNormSq` embedded in `ℂ`.

Required constructor:

```text
SourceHilbertSchmidtForThetaSmoothedOperator:
  SourceCC20FixedSKernelEstimate preTrace coordinate A
  -> SourceCC20HilbertSchmidtKernelData A
```

The proof exposes the formula and bound that make the integral finite. A field
containing only `normSqIntegrable` does not discharge Phase 2.

### 8.5 Positive trace owner

```lean
structure SourceCC20PositiveTraceData
    (hs : SourceCC20HilbertSchmidtKernelData operatorKernel) where
  adjointKernel : coordinate.Point → coordinate.Point → ℂ
  adjointKernel_eq :
    ∀ x y, adjointKernel x y = starRingEnd ℂ (operatorKernel.kernel y x)
  positiveSquareKernel : coordinate.Point → coordinate.Point → ℂ
  positiveSquareKernel_eq_composition :
    SourceCC20KernelCompositionStatement
      coordinate adjointKernel operatorKernel.kernel positiveSquareKernel
  positiveKernelClass :
    SourceCC20PositiveKernelClass
      operatorKernel.positiveSquareOperator positiveSquareKernel
  ordinaryTrace_eq_hsNormSq :
    SourceCC20OrdinaryTrace positiveKernelClass.toTraceClass =
      (hs.hsNormSq : ℂ)
```

Define the route-facing real scalar from the independent complex ordinary
trace:

```lean
def SourceCC20PositiveTraceData.positiveTrace
    (positive : SourceCC20PositiveTraceData hs) : ℝ :=
  (SourceCC20OrdinaryTrace positive.positiveKernelClass.toTraceClass).re
```

Prove nonnegativity as a theorem from `ordinaryTrace_eq_hsNormSq` and the
nonnegative kernel integral. Do not store `positiveTrace_nonnegative` as an
independent field or hide the complex-to-real step in `simp`.

Required semantic theorems:

```text
SourceTraceClassForPositiveSquare
SourcePositiveTraceEqualsOrdinaryTrace
SourcePositiveTraceEqualsKernelMass
SourcePositiveTraceNonnegative
```

### 8.6 Five trace-move witnesses

The exact trace layer supports two legal cyclicity patterns:

```text
X and Y are Hilbert-Schmidt
  -> XY and YX are trace-class
  -> Tr(XY) = Tr(YX)

T is trace-class and B is bounded
  -> TB and BT are trace-class
  -> Tr(TB) = Tr(BT)
```

One bounded factor and one Hilbert-Schmidt factor do not suffice. Their product
is only known to be Hilbert-Schmidt.

Each C1-C4 witness stores the exact factors, product kernels, and one of the two
legal factorizations:

```lean
structure SourceCC20CyclicMoveWitness
    (coordinate : SourceCC20KernelCoordinateData) where
  leftFactor rightFactor : coordinate.complexHilbertCarrier →L[ℂ]
    coordinate.complexHilbertCarrier
  legality :
    SourceCC20HilbertSchmidtPair leftFactor rightFactor ⊕
      SourceCC20TraceClassBoundedPair leftFactor rightFactor
  leftProductTraceClass :
    SourceCC20TraceClassData (leftFactor.comp rightFactor)
  rightProductTraceClass :
    SourceCC20TraceClassData (rightFactor.comp leftFactor)
  trace_eq :
    SourceCC20OrdinaryTrace leftProductTraceClass =
      SourceCC20OrdinaryTrace rightProductTraceClass
```

```lean
structure SourceCC20CyclicMoveWitnessLedger
    (positive : SourceCC20PositiveTraceData hs) where
  c1PositiveSquare : SourceCC20PositiveSquareRewriteWitness positive
  c2SupportSquare : SourceCC20SupportSquareMoveWitness positive
  c3PhaseDerivative : SourceCC20PhaseDerivativeTraceWitness positive
  c4ProjectionDefect : SourceCC20ProjectionDefectTraceWitness positive
  c5NoStripExtraction : SourceCC20NoCyclicMoveAfterExtractionWitness positive
```

The five meanings come from
`docs/manuscripts/connes-weil-rh-proof-draft.md:661-669`:

```text
C1  rewrite the positive square
C2  move support projections through theta smoothing
C3  trace the theta-smoothed phase derivative
C4  route projection-order defects into Cdef
C5  extract rank/pole jets and perform no later cyclic move on them
```

C5 records the extraction order; it is not a generic cyclicity proposition.

### 8.7 Concrete remainder owner

The remainder owner stores source objects. All scalar terms are definitions of
those objects:

```lean
structure SourceCC20TraceRemainderObjects
    (base : SourceCC20SelectedAnalyticTraceBaseData inputs g) where
  regularizedSourceTrace : SourceCC20RegularizedSourceTraceData base
  soninTrace : SourceCC20SoninTraceData base
  zeroModeEvaluation : SourceCC20ZeroModeEvaluationData base.preTrace g.weilTest
  positiveTateEvaluation :
    SourceCC20PositiveTateEvaluationData base.preTrace g.weilTest
  negativeTateEvaluation :
    SourceCC20NegativeTateEvaluationData base.preTrace g.weilTest
  projectionDefects : SourceCC20ProjectionDefectFamily base
  endpointStrip : SourceCC20EndpointStripData base projectionDefects
  qImage : SourceCC20QImageData regularizedSourceTrace
```

Define, rather than choose, these scalars:

```text
sourceTrace            := regularizedSourceTrace.value
soninTrace             := soninTrace.value
rankTerm               := zeroModeEvaluation.weightedNormSq
positiveTatePoleTerm   := positiveTateEvaluation.weightedNormSq
negativeTatePoleTerm   := negativeTateEvaluation.weightedNormSq
projectionDefectTerm   := re(sum of ordinary traces of projectionDefects)
cdefRemainder          := endpointStrip.traceRemainder
traceRemainder         := soninTrace - sourceTrace
qTraceRemainder        := qImage.value
```

The theorem layer proves:

```text
W_infinity = L - D
W_infinity = S - E
the two orientations are equivalent
qTraceRemainder = rank + positive pole + negative pole
                  + projection defect + Cdef
the defect-trace sum has zero imaginary part or an explicit conjugate pairing
|cdefRemainder| <= endpointStrip.constant * endpointStrip.gauge
positiveTrace - sourceTrace = qTraceRemainder
```

The three evaluation objects must read the same source evaluation of
`g.weilTest` at `0`, `+i/2`, and `-i/2`. Each projection defect carries the
commutator or endpoint-strip factor that produces it. The remainder theorem
also proves that the complex defect traces combine to the displayed real
scalar. The API contains no free `rankTerm`, `poleTerm`,
`projectionDefectTerm`, or `cdefRemainder` field.

### 8.8 Non-recursive selected analytic package

```lean
structure SourceCC20SelectedAnalyticTraceBaseData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  preTrace : SourceCC20PreTraceInputData inputs g
  coordinate : SourceCC20KernelCoordinateData
  operatorKernel :
    SourceCC20ThetaSmoothedOperatorKernelData preTrace coordinate
  hilbertSchmidt : SourceCC20HilbertSchmidtKernelData operatorKernel
  positiveTrace : SourceCC20PositiveTraceData hilbertSchmidt
  cyclicLedger : SourceCC20CyclicMoveWitnessLedger positiveTrace
```

```lean
structure SourceCC20SelectedAnalyticTraceData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  base : SourceCC20SelectedAnalyticTraceBaseData inputs g
  remainderObjects : SourceCC20TraceRemainderObjects base
  remainderTheorems : SourceCC20TraceRemainderTheorems base remainderObjects
  supportSquareReadOff : SourceSupportSquareTraceAfterLegality base
  noDefectReadOff :
    SourceNoDefectTraceAfterSupportSquare base supportSquareReadOff
  boundedComparisonTransport :
    SourceBoundedComparisonTraceIdealTransport base
```

No structure refers to `self`, and no field mentions data declared later in
the same structure. A downstream constructor combines this completed analytic
owner with the existing CCM25 arithmetic/read-off inputs and produces
`SourceTraceReadOffData inputs g`. That constructor is the first point where
the 011 B2 bridge may enter.

## 9. Phase Plan

### Phase 0A. Freeze the external mathematics

Recorded result on 2026-07-10:

```text
kernel source certificate:    pass by direct commutator proof
remainder source certificate: exact no-defect target rejected
Phase 0A acceptance:          rejected theorem statement
M0:                           cancelled
```

The first source audit stopped at Connes 1999 Theorem 4 and the nonunitary
`eta_S` comparison. The superseding derivation works in CCM24's unitary
`K_S`-invariant scattering coordinate. Two cross-half-line commutators prove
the Hilbert-Schmidt estimate and produce an `L2` kernel.

The remainder gate fails for a stronger reason. CC20 Theorem `thmqkey1`
constructs triple-vanishing tests with nonzero trace remainder, by the compact
operator argument recorded in the mathematical verdict. No transport theorem
can turn that nonzero source term into the requested exact equality.

Purpose: decide whether primary sources or a written derivation support the
fixed-S kernel estimate and the fixed-S remainder transport before writing a
route-facing API.

Tasks:

```text
1. Complete cc20-fixed-s-kernel-source-certificate.md.
2. Complete cc20-fixed-s-remainder-source-certificate.md.
3. Record the exact fixed-S coordinate, measures, theta action, projections,
   literal K_A formula, and bound with all S, I, lambda, and g dependencies.
4. Record the exact remainder objects, commutators, Q action, endpoint strip,
   Cdef bound, and both trace-remainder orientations.
5. Give a primary-source theorem/formula/page for each imported claim.
6. Mark every uncited derivation as a Lean proof obligation with exact
   domain, codomain, hypotheses, conclusion, and a finite derivation chain from
   lower definitions or named Mathlib lemmas.
7. Select a feasibility fork when either certificate has an unsupported row.
```

Acceptance:

```text
both source certificates have decision: pass
no row cites only the project manuscript
K_A and its majorant are literal formulas, not names or existential objects
the remainder certificate names every fixed-S transport map
the proposed Lean statements contain no route trace conclusions
each uncited row has a finite lower derivation chain; the target statement
itself does not appear among its assumptions
```

Failure:

```text
missing fixed-S kernel formula or bound       -> Fork B
abstract smoothing operator without kernel   -> Fork E
archimedean-to-fixed-S transport missing      -> Fork F
remainder source equation missing             -> Fork G
remainder fixed-S transport missing           -> Fork H
```

Phase 0A is a source audit. It must not create
`SourceCC20FixedSKernelEstimate` as an axiom, opaque constant, structure field,
or unconstrained proposition.

### Phase 0B. Compile the generic Lean foundations

Purpose: build only the L2 operator and nuclear-trace infrastructure that does
not depend on the selected route operator.

Tasks:

```text
1. Confirm the concrete Lp type and exponent syntax in Mathlib v4.30.0.
2. Implement SourceCC20KernelCoordinateData in CC20KernelCoordinate.lean.
3. Construct or parameterize a countable orthonormal basis without assuming
   finite dimensionality.
4. Compile the measurable square-integrable-kernel-to-L2-operator theorem.
5. Include the L2 action equality and operator-norm estimate in its conclusion.
6. Implement SourceCC20NuclearDecompositionData.
7. Define ordinary trace from the absolutely summable nuclear series.
8. Prove agreement with every countable ONB diagonal series.
9. Compile HS-times-HS product trace and trace-class-times-bounded cyclicity.
10. Record exact #check output in cc20-phase-0-compiled-contracts.md.
```

Acceptance:

```text
all declarations compile without RouteInputs, SourceTraceReadOffData, or
legacy traceClass/cyclicLegal inputs:

SourceCC20SquareIntegrableKernelToContinuousLinearMap
SourceCC20OrdinaryTraceFoundation
SourceCC20OrdinaryTrace_eq_basisSeries
SourceCC20OrdinaryTrace_basisIndependent
SourceCC20HilbertSchmidtProductTrace
SourceCC20TraceClassBoundedCyclicity

cc20-phase-0-compiled-contracts.md contains the exact #check output
the ordinary trace definition contains no kernel-mass integral
both cyclicity theorems return trace-class witnesses for both product orders
```

Failure:

```text
L2 operator construction fails       -> Fork C
nuclear/ONB trace foundation fails    -> Fork D
HS product trace foundation fails     -> stop at SourceCC20HilbertSchmidtProductTrace
bounded cyclicity foundation fails    -> stop at SourceCC20TraceClassBoundedCyclicity
```

The blocker report states the compiled domain and codomain, the smallest
failing file, and the missing Mathlib lemma. It must not replace the missing
result with `operatorExists : Prop`, a free trace value, or an arbitrary
operator field.

### Phase 1. Build the exact operator/kernel carrier

Entry gate:

```text
Phase 0A source certificates: pass
Phase 0B compiled contracts: pass
allowed files: new Source/CC20OperatorKernel.lean and import-minimal support
forbidden files: Dev, route consumers, legacy remainder records
```

Tasks:

```text
1. Instantiate the passed Phase 0B coordinate with the certified fixed-S data.
2. Construct SourceCC20PreTraceInputData from RouteInputs and g.
3. Define F_g through the source half-density convolution square.
4. Define theta_S(g), theta_S(g*), P, P_hat, and A = P_hat P theta_S(g).
5. Prove P and P_hat are self-adjoint idempotents.
6. Prove theta_S(g*) is the adjoint of theta_S(g).
7. Prove theta_S(g*) theta_S(g) represents F_g.
8. Define the concrete kernel K_A.
9. Prove the L2 kernel-action identity for A.
10. Derive the displayed formula for A* A from the adjoint and projection laws.
```

Acceptance:

```text
SourceTraceOperatorIdentity is a theorem projected from one data owner.
No field chooses an arbitrary operator or kernel after seeing the target scalar.
```

Rejection condition:

```text
If the only available fixed-S source statement gives an abstract smoothing
operator without a kernel formula or equivalence, record that exact source/API
bottom. Do not claim operator identity from matching names.
```

### Phase 2. Prove Hilbert-Schmidt square integrability

Tasks:

```text
1. Translate the passed Phase 0A kernel certificate into the exact theorem
   SourceCC20FixedSKernelEstimate for the Phase 1 operatorKernel.
2. Prove the displayed K_A formula from the Phase 1 action identities.
3. Prove the certified majorant and its square-integrability bound.
4. Prove measurability and regularity of K_A.
5. Apply SourceCC20SquareIntegrableKernelToContinuousLinearMap.
6. Prove integrability of norm(K_A)^2 on the product measure.
7. Define hsNormSq as that integral.
8. Prove bounded left/right projection transport.
9. Do not construct any legacy gate yet; keep the witness on the analytic owner.
```

Acceptance:

```text
SourceCC20FixedSKernelEstimate is a theorem about the exact Phase 1 K_A.
SourceHilbertSchmidtForThetaSmoothedOperator constructs
SourceCC20HilbertSchmidtKernelData for the exact A from Phase 1.
```

Do not accept:

```text
traceClass g
cyclicLegal g
hilbertSchmidtGate g
```

as inputs to the proof.

### Phase 3. Construct the positive square and ordinary trace

Tasks:

```text
1. Define K_Astar(x,y) = conjugate(K_A(y,x)).
2. Define the composition kernel for A* A.
3. Prove Tonelli/Fubini hypotheses and representative regularity.
4. Prove A* A belongs to SourceCC20PositiveKernelClass.
5. Prove convergence of the ordinary-trace diagonal series.
6. Prove basis independence using the Phase 0B trace foundation.
7. Prove ordinaryTrace(A* A) = (hsNormSq : Complex).
8. Prove nonnegativity from the norm-square integral.
9. Define the route-facing positiveTrace as re(ordinaryTrace(A* A)).
```

Acceptance:

```text
ordinaryTrace(A* A) = (hsNormSq : Complex)
positiveTrace = re(ordinaryTrace(A* A)) = hsNormSq >= 0
```

The ordinary trace has an independent nuclear-series definition. The Phase 0B
foundation proves its equality with each countable ONB diagonal series. Phase 3
then proves equality with the kernel mass before any route theorem uses
nonnegativity.

### Phase 4. Prove the five-move ledger

Tasks:

```text
1. C1 positive-square rewrite.
2. C2 support-projection move.
3. C3 theta-smoothed phase-derivative trace.
4. C4 projection-order defect routing.
5. C5 no cyclic move after rank/pole extraction.
6. For C1-C4, record either two HS factors or a trace-class/bounded pair.
7. Prove both product traces exist before each cyclic equality.
8. Bundle the five witnesses without erasing their operator products.
```

Acceptance:

```text
SourceCyclicMoveWitnessLedger contains five inspectable witnesses. Each C1-C4
trace equality names its factors and cites a legal trace-ideal factorization.
```

### Phase 5. Construct the remainder normal form

Entry gate:

```text
cc20-fixed-s-remainder-source-certificate.md has decision: pass
each fixed-S Euler and comparison row has a source theorem or an exact Lean
derivation obligation
the certificate and Phase 1 owner use the same coordinate and measures
```

Tasks:

```text
1. Construct the regularized source-trace and Sonin-trace objects.
2. Define the source trace remainder delta and its Q image.
3. Construct the zero-mode and two Tate evaluation objects from one source evaluator.
4. Define rank and pole terms from those evaluations.
5. Construct every projection defect from its named commutator.
6. Define projectionDefectTerm as the sum of their ordinary traces.
7. Construct endpointStrip and define cdefRemainder from it.
8. Prove W_infinity = L - D and the S - E form from one equation set.
9. Prove the Cdef trace-norm bound and no-hidden-defect equation.
10. Derive no-bulk and no-hidden-finite-part statements.
```

Acceptance:

```text
every remainder scalar unfolds to a named source object; a constructor cannot
choose all remainder terms as zero unless the source objects evaluate to zero
```

This phase may use the paper's archimedean trace-remainder formula. The fixed-S
Euler and comparison terms require their own transport proofs.

If implementation exposes a source gap that the Phase 0A certificate missed,
correct the certificate and select Fork G or Fork H. Do not add a remainder
field to preserve the prior `pass` decision.

### Phase 6. Support-square and no-defect read-off

Tasks:

```text
1. Prove SourceSupportSquareTraceAfterLegality from Phases 1-5.
2. Identify the route's support-square scalar with the kernel positive trace.
3. Prove SourceNoDefectTraceAfterSupportSquare.
4. Keep rank, pole, and Cdef terms outside the CCM25 main term.
5. Construct SourceTraceReadOffData inputs g from the completed analytic owner.
6. Attach the existing 011 B2 support-square/QW_lambda read-off only after step 3.
```

Acceptance order:

```text
ordinary positive trace of A* A
  -> support-square trace
  -> no-defect source trace
  -> SourceTraceReadOffData
  -> existing selected QW_lambda read-off
```

Reject any proof that jumps from trace nonnegativity to `QW_lambda` without the
two middle equalities.

### Phase 7. Rewire packages and retire roots

Tasks:

```text
1. Add a selected analytic constructor for CC20TraceObjectPackage or its replacement.
2. Change SourceObjectTheoremBasePackage to store the selected analytic owner.
3. Derive legacy HS, trace, cyclicity, and remainder rows from that owner.
4. Rewire S2B1TraceScale consumers.
5. Rewire Dev construction.
6. Remove normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot.
7. Remove normalizedCoreS2B1TracePackageRemaindersRoot.
8. Prove old universal records are inactive in the no-argument route.
9. Audit the remaining root graph.
```

The old universal constructors may stay for compatibility if other modules use
them. They must not appear in the dependency chain of
`unconditional_rh_skeleton`.

## 10. Consumer Rewiring Graph

Entry graph:

```text
two Dev axioms
  -> CC20TracePackageRemainderData
  -> normalizedSeedTraceObjectPackage
  -> SourceObjectTheoremBasePackage
  -> S2B1 trace-scale package
  -> route package
  -> unconditional_rh_skeleton
```

Target graph:

```text
RouteInputs + SourceBackedFixedSTest + S/I/lambda admissibility
  |
  +-- SourceCC20PreTraceInputData
  |     -> fixed-S complex kernel coordinate
  |
  +-- exact theta-smoothed compressed operator/kernel
  |     -> orthogonal projection and adjoint laws
  |     -> square-integrable kernel
  |     -> independent ordinary trace of A* A
  |     -> five cyclic witnesses
  |
  +-- concrete trace-remainder data
        -> rank/pole/Cdef normal form
        -> support-square read-off
        -> no-defect read-off
        -> SourceTraceReadOffData
        -> attach existing B2 scalar bridge
        -> selected CC20 trace object
        -> SourceObjectTheoremBasePackage
        -> S2B1 route
```

## 11. Rejection Guards

Add or retain named Lean guards for these shortcuts:

```text
1. current trace amplitude is encoded evaluation norm
2. current convolution is addition
3. current HS gate is traceClass and cyclicLegal
4. old universal scalar identification family is false
5. selected B2 read-off does not imply B3 QW/pole collapse
6. operator identity cannot be derived from an arbitrary positive scalar
7. HS data cannot be constructed from legacy traceClass/cyclicLegal Props
8. a generic L2 kernel does not supply a diagonal trace theorem
9. fixed-S legality cannot be imported from the single archimedean theorem by notation
10. old universal remainder records are not active route producers after rewiring
11. SourceTraceReadOffData cannot serve as a producer for its own HS/trace fields
12. a free positiveTrace or free remainder scalar cannot populate the analytic owner
13. bounded-times-HS alone does not justify a trace or cyclic trace equality
14. A* A support-square identity requires self-adjoint idempotent projections
15. kernel mass equals ordinary trace only after an independent trace definition
16. the complex ordinary trace must equal the real positive scalar through an explicit theorem
17. a Phase 0A certificate cannot pass from the project manuscript alone
18. the certified kernel formula and majorant are definitions, not owner fields
```

Forbidden producer inputs:

```text
True
Set.univ
SourceRH
no-off-line source-zero
CC20 Proposition C1 source criterion
selected detector criterion coverage
QW/pole or psi/pole collapse
stored determinant rows
stored Mellin rows
arbitrary positiveTrace values
anonymous traceClass or cyclicLegal propositions
SourceTraceReadOffData as an operator/kernel producer
free rank, pole, projection-defect, or Cdef real fields
bounded-times-HS used as a trace-class premise
```

## 12. Feasibility Forks

### Fork A. Phase 0A-0B gates succeed

Begin Phase 1 in source modules. Route consumers and Dev remain unchanged until
Phases 1-6 construct the completed selected analytic owner.

### Fork B. Fixed-S kernel formula or estimate is missing

Stop at:

```text
Phase 0A: cc20-fixed-s-kernel-source-certificate.md
Phase 2:  SourceCC20FixedSKernelEstimate
```

The blocker must contain the exact source coordinate, proposed kernel formula,
missing bound, external source search, and smallest Lean statement for the
needed estimate. The project manuscript alone cannot discharge this bottom.

### Fork C. L2 integral-operator construction is missing

Stop at:

```text
SourceCC20SquareIntegrableKernelToContinuousLinearMap
```

The blocker must contain:

```text
exact Mathlib types
compiled kernel integrability statement
missing boundedness/operator theorem
smallest file that reproduces the gap
source theorem needed to prove the bound
```

Do not create an abstract operator record whose action law is assumed.

### Fork D. Ordinary-trace foundation is missing

Stop at:

```text
SourceCC20OrdinaryTraceFoundation
```

The blocker must state the nuclear decomposition, chosen basis index, diagonal
series, summability goal, basis-series equality, and the exact missing Mathlib
result. Do not rename the kernel mass as ordinary trace.

### Fork E. Selected source theorem gives only operator smoothing

Stop at:

```text
SourceCC20ThetaSmoothedOperatorKernelReadOff
```

The blocker must show that the operator exists but no concrete kernel or kernel
equivalence is available. A future source import may discharge this exact
bottom.

### Fork F. Archimedean kernel works, fixed-S transport fails

Keep the archimedean theorem as a local result and stop at:

```text
SourceCC20FixedSEulerKernelTransport
```

Do not cast the archimedean kernel into the fixed-S coordinate through a bare
Hilbert-space equivalence. The theorem must transport the scaling action,
support projections, Fourier-support projection, and kernel measure.

### Fork G. Remainder theory blocks after positive trace succeeds

Record partial progress only. The active named bottoms become the precise
unproved rows among:

```text
SourceCC20TraceRemainderAfterQ
SourceCC20ProjectionDefectNormalForm
SourceCC20RankPoleLedgerIdentification
SourceCC20EndpointStripCdefDomination
SourceCC20NoHiddenPositiveDefectOutsideCdef
```

Do not claim either root removed until the package consumer no longer needs the
old mixed record.

### Fork H. Remainder fixed-S transport is missing

Stop during Phase 0A when the archimedean remainder formulas have no theorem
that transports all of these objects to the selected fixed-S coordinate:

```text
scaling action
support and Fourier-support projections
regularized source trace
Q image
projection-defect commutators
endpoint-strip measure and Cdef bound
```

The blocker must identify the strongest archimedean theorem, the exact source
and target spaces, and the first transport equality that lacks proof. A bare
Hilbert-space equivalence does not discharge Fork H.

## 13. Verification Plan

No Lean build is required for writing this document. Implementation
verification uses WSL2 on ext4 under the repository lock.

### 13.1 Smallest builds by phase

```text
Phase 0A:
  no Lean build; validate both completed source certificates

Phase 0B:
  lake build ConnesWeilRH.Source.CC20KernelCoordinate
  lake build ConnesWeilRH.Source.CC20KernelTraceIdeal

Phase 1:
  lake build ConnesWeilRH.Source.CC20OperatorKernel

Phase 2:
  lake build ConnesWeilRH.Source.CC20HilbertSchmidt

Phase 3-4:
  lake build ConnesWeilRH.Source.CC20PositiveTrace

Phase 5:
  lake build ConnesWeilRH.Source.CC20TraceRemainder

Phase 6-7:
  lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  lake build ConnesWeilRH.Source.ObjectTheoremBasePackage
  lake build ConnesWeilRH.Source.S2B1TraceScale
  lake build ConnesWeilRH.Dev.UnconditionalSkeleton
```

Command form:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <target>
```

Never run Lake through Windows Lean or from `/mnt/c`.

### 13.2 Import-facing audit

Create an untracked scratch file in the ext4 verification environment that
imports the owning modules and checks the new declarations:

```lean
import ConnesWeilRH.Source.CC20KernelCoordinate
import ConnesWeilRH.Source.CC20OperatorKernel
import ConnesWeilRH.Source.CC20KernelTraceIdeal
import ConnesWeilRH.Source.CC20HilbertSchmidt
import ConnesWeilRH.Source.CC20PositiveTrace
import ConnesWeilRH.Source.CC20TraceRemainder
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check SourceCC20PreTraceInputData
#check SourceCC20FixedSKernelEstimate
#check SourceCC20OrdinaryTraceFoundation
#check SourceCC20OrdinaryTrace_basisIndependent
#check SourceCC20HilbertSchmidtProductTrace
#check SourceCC20TraceClassBoundedCyclicity
#check SourceCC20ThetaSmoothedOperatorKernelData
#check SourceHilbertSchmidtForThetaSmoothedOperator
#check SourcePositiveTraceEqualsOrdinaryTrace
#check SourceCC20CyclicMoveWitnessLedger
#check SourceSupportSquareTraceAfterLegality
#check SourceNoDefectTraceAfterSupportSquare
#check unconditional_rh_skeleton
```

### 13.3 Focused axiom audit

Audit at least:

```lean
#print axioms SourceCC20FixedSKernelEstimate
#print axioms SourceCC20OrdinaryTrace_basisIndependent
#print axioms SourceCC20HilbertSchmidtProductTrace
#print axioms SourceCC20TraceClassBoundedCyclicity
#print axioms SourceHilbertSchmidtForThetaSmoothedOperator
#print axioms SourcePositiveTraceEqualsOrdinaryTrace
#print axioms SourcePositiveTraceNonnegative
#print axioms SourceCyclicMoveWitnessLedger
#print axioms SourceSupportSquareTraceAfterLegality
#print axioms SourceNoDefectTraceAfterSupportSquare
#print axioms normalizedCoreS2B1SelectedAnalyticTraceDataFromTheorems
#print axioms unconditional_rh_skeleton
```

Acceptance:

```text
new 012 declarations:
  no sorryAx
  no new project axioms

unconditional_rh_skeleton:
  both S2-B1 root names absent
  the four expected non-012 roots remain visible
```

### 13.4 Shortcut scans

```text
rg -n "sorry|admit|axiom|opaque|unsafe" \
  ConnesWeilRH/Source/CC20KernelCoordinate.lean \
  ConnesWeilRH/Source/CC20OperatorKernel.lean \
  ConnesWeilRH/Source/CC20KernelTraceIdeal.lean \
  ConnesWeilRH/Source/CC20HilbertSchmidt.lean \
  ConnesWeilRH/Source/CC20PositiveTrace.lean \
  ConnesWeilRH/Source/CC20TraceRemainder.lean

rg -n "normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot|normalizedCoreS2B1TracePackageRemaindersRoot" \
  ConnesWeilRH/Dev/UnconditionalSkeleton.lean

rg -n "True|Set.univ|SourceRH|noOffLine|DetectorCriterion|PropositionC1" \
  ConnesWeilRH/Source/CC20KernelCoordinate.lean \
  ConnesWeilRH/Source/CC20OperatorKernel.lean \
  ConnesWeilRH/Source/CC20KernelTraceIdeal.lean \
  ConnesWeilRH/Source/CC20HilbertSchmidt.lean \
  ConnesWeilRH/Source/CC20PositiveTrace.lean \
  ConnesWeilRH/Source/CC20TraceRemainder.lean

rg -n "SourceTraceReadOffData|fullTraceReadOffBridge|restrictedTraceReadOffBridge|hilbertSchmidtGate" \
  ConnesWeilRH/Source/CC20KernelCoordinate.lean \
  ConnesWeilRH/Source/CC20OperatorKernel.lean \
  ConnesWeilRH/Source/CC20KernelTraceIdeal.lean \
  ConnesWeilRH/Source/CC20HilbertSchmidt.lean \
  ConnesWeilRH/Source/CC20PositiveTrace.lean

rg -n "RouteInputs|SourceBackedFixedSTest|SourceTraceReadOffData|traceClass|cyclicLegal" \
  ConnesWeilRH/Source/CC20KernelCoordinate.lean \
  ConnesWeilRH/Source/CC20KernelTraceIdeal.lean

rg -n "positiveTrace[[:space:]]*:[[:space:]]*ℝ|rankTerm[[:space:]]*:[[:space:]]*ℝ|poleTerm[[:space:]]*:[[:space:]]*ℝ|cdefRemainder[[:space:]]*:[[:space:]]*ℝ" \
  ConnesWeilRH/Source/CC20PositiveTrace.lean \
  ConnesWeilRH/Source/CC20TraceRemainder.lean

git diff --check
```

Review every match. Comments that name a forbidden shortcut are allowed; proof
dependencies are not.

## 14. Milestones

```text
+------+-------------------------------------------------------+-----------------------------+
| ID   | milestone                                             | route effect                |
+------+-------------------------------------------------------+-----------------------------+
| M0   | source certificates and generic trace foundation pass | feasibility established     |
| M1   | exact selected A and K_A share one owner              | operator Prop replaced      |
| M2   | fixed-S estimate, integrability, hsNormSq proved      | HS Prop replaced            |
| M3   | basis-independent ordinary trace of A* A proved       | scalar seed bypass begins   |
| M4   | five named move witnesses proved                      | cyclicLegal Prop replaced   |
| M5   | source-defined rank/pole/Cdef normal form constructed | mixed remainder Props lower |
| M6   | no-defect read-off constructs SourceTraceReadOffData  | 011 B2 bridge can attach    |
| M7   | two Dev roots removed and axiom graph audited         | plan 012 complete           |
+------+-------------------------------------------------------+-----------------------------+
```

M1-M4 are meaningful analytic progress but do not complete this plan while the
old root records remain active. Record `partial`, not `accepted`, if the work
stops before M7.

## 15. Success And Failure Criteria

### Complete

All conditions hold:

```text
M0-M7 complete
both Phase 0A source certificates have decision: pass
Phase 0 compiled contracts match their import-facing #check output
selected route consumes the data-bearing analytic owner
SourceTraceReadOffData appears only after support-square and no-defect proofs
ordinary trace uses an independent nuclear-series definition and agrees with
every countable ONB diagonal series
projection and theta-convolution laws derive the A* A support-square identity
remainder scalars unfold to source evaluations, defect operators, or strip data
both S2-B1 roots removed from Dev
old universal records inactive in the final route
smallest builds pass
import-facing checks pass
focused new declarations contain no sorryAx or new project axioms
unconditional_rh_skeleton shows only the four expected remaining roots
```

### Partial

The implementation reaches a named analytic bottom, but one or both old roots
remain in the final route. Report the exact bottom and keep RH status
conditional.

### Rejected

Reject the route if a named theorem proves that the required selected operator
or remainder identity is false for the actual source model. Keep the
counterexample or equivalence theorem in Lean and update plans 013-015.

### Blocked

Use `blocked` only after reproducing the same external mathematical/API gap in
three consecutive work rounds and exhausting in-scope alternatives. A large
proof obligation or missing convenience lemma is not enough.

## 16. Handoff Template

```text
012 handoff:
  status: accepted / partial / blocked / rejected
  RH status: still conditional / unconditional
  milestone reached:
  files changed:
  declarations added:
  fixed-S kernel source certificate:
  fixed-S remainder source certificate:
  Phase 0 compiled contracts:
  pre-trace input:
  exact operator:
  exact kernel:
  HS evidence:
  ordinary-trace definition and basis-independence:
  positive trace evidence:
  cyclic moves proved:
  remainder rows proved:
  consumer rewired:
  old S2-B1 roots present or absent:
  smallest WSL builds:
  import-facing checks:
  focused axioms:
  remaining four-root graph:
  next safe action:
```

## 17. Start Order

Final stop:

```text
fixed-S Hilbert-Schmidt mathematics: proved
L2 kernel existence: proved
exact no-defect read-off: disproved
steps 3-14: cancelled under this plan
```

Any successor plan must change the consumer before Lean work starts:

```text
1. retain D_S in the trace read-off statement, or
2. add the finite-codimension conditioning used by CC20 and prove that the
   selected tests satisfy it.
```

Do not implement the old `supportSquareTrace = qwLambda` target by assigning
zero values to remainder fields. The source counterexample would remain hidden
behind an axiom-clean proof of a weak model.
