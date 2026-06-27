# CCM24 Semilocal Object Normalization Discharge

Status: source-object replacement package for CCM24 semilocal place sets,
support windows, support transport, bounded comparison, and Sonin exhaustion.

This package sharpens:

```text
docs/proofs/ccm24-support-window-transport-discharge.md
```

The earlier package proves the route-level one-window invariant:

```text
positive trace window
  =
restricted QW_lambda window
  =
fixed-test Cdef exhaustion window.
```

This package records the source definitions that must replace:

```text
ConnesWeilRH.SemilocalModelSymbols
```

before final certification.

## Evidence Boundary

| claim | evidence |
|---|---|
| symbolic CCM24 semilocal fields | `ConnesWeilRH/Basic.lean:144-183` |
| source-interface obligations | `ConnesWeilRH/Source/CCM24.lean:19-54` |
| route source-backed fixed-S test fields | `ConnesWeilRH/Route/Definitions.lean:44-64` |
| route admissible-window consumers | `ConnesWeilRH/Route/AdmissibleWindow.lean:22-34,101-134` |
| canonical model source ranges | `mainc2m24fine.tex:237-253,786-804`; `docs/audits/source-reread-v0.2.md:43` |
| support and Fourier transport source ranges | `mainc2m24fine.tex:761-771,983-1003`; `docs/audits/source-reread-v0.2.md:44` |
| bounded comparison source range | `mainc2m24fine.tex:806-823`; `docs/audits/source-reread-v0.2.md:45` |
| Sonin comparison source range | `mainc2m24fine.tex:1050-1060`; `docs/audits/source-reread-v0.2.md:46` |
| fixed-window route use | `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057,1310-1325` |

## Problem

The current symbolic layer exposes:

```text
PlaceSet : Type
Window : Type
Test : Type
canonicalHilbertModel : PlaceSet -> Prop
supportInWindow : Test -> Window -> Prop
fourierSupportInWindow : Test -> Window -> Prop
supportTransported : Test -> Window -> Prop
convolutionSupportTransported : Test -> Window -> Prop
boundedComparisonMap : PlaceSet -> Prop
soninSpaceComparison : Window -> Prop
fixedWindowExhaustionCompatible : Window -> Prop
```

This shape proves route composition. It does not yet define the CCM24 objects.

The certification risk is fixed-`S` drift:

```text
source place set S
  |
  v
support window I
  |
  v
canonical coordinate V_S=M_S U_S
  |
  v
bounded comparison
  |
  v
Sonin window and lambda exhaustion
```

If any arrow uses a fresh route-local object, Theorem 1 can read a positive
trace in one model and identify a restricted Weil form in another.

## Target Statement

For a source-backed fixed-`S` test `g`, support window `I`, and `lambda > 1`,
the CCM24 object replacement target is:

```text
CCM24SemilocalObjectNormalization(S,I,lambda,g):
  S is the CCM24 finite place set;

  I is the CCM24 source support window contained in [lambda^-1,lambda];

  g is the CCM24 source test tied to the common CCM25/CC20 test;

  V_S=M_S U_S gives the canonical fixed-S coordinate and Fourier grading;

  eta_S and theta_S transport support, Fourier support, and the convolution
  square through that same window;

  the bounded comparison map and inverse preserve the analytic class supplied
  by CC20 and the endpoint-strip packages;

  the Sonin comparison and fixed-window exhaustion use the same window.
```

Lean-facing replacement outputs:

```text
SourcePlaceSetMatchesVisiblePrimes
SourceSupportWindow
SourceCCM24TestCompatibility
SourceCanonicalSemilocalModel
SourceSupportAndFourierSupportTransport
SourceConvolutionSupportTransport
SourceBoundedComparisonTraceClassTransport
SourceFixedWindowSoninExhaustion
SourceWindowLambdaCompatibility
```

## Lemma 1. Place Set Is The Fixed Source Set

Statement:

```text
SourcePlaceSetMatchesVisiblePrimes(S,g):
  S is the fixed CCM24 place set containing the archimedean place and every
  finite prime visible to F_g=g^* * g.
```

Proof.

The admissibility condition in Theorem 1 says:

```text
S contains every finite prime visible to F_g=g^* * g.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
```

CCM24 supplies the semilocal model for a finite set of places:

```text
mainc2m24fine.tex:237-253
```

Thus:

```text
PlaceSet : Type
```

must be replaced by the CCM24 finite place-set object, with the route-side
visible-prime side condition proved before the fixed-S trace read-off.

Failure blocked:

```text
S grows with lambda or omits a finite prime visible to F_g.
```

## Lemma 2. Window Is The Source Support Window

Statement:

```text
SourceSupportWindow(I,lambda,g):
  I is the CCM24 source support window for g, and I lies in
  [lambda^-1,lambda].
```

Proof.

The route requires:

```text
I subset [lambda^(-1),lambda]
supp(g) subset I
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1054-1057
docs/proofs/ccm25-restricted-read-off-discharge.md:77-119
```

CCM24 support and Fourier-support transport supply the source window:

```text
mainc2m24fine.tex:761-771
mainc2m24fine.tex:983-1003
```

The symbolic predicates:

```text
supportInWindow
fourierSupportInWindow
windowContainedInLambda
lambdaCompatible
```

must be derived from this source window, not chosen independently.

Failure blocked:

```text
QW_lambda uses one lambda cutoff while the fixed-S trace uses another.
```

## Lemma 3. Test Compatibility Uses The Common Source Test

Statement:

```text
SourceCCM24TestCompatibility(g):
  the CCM24 semilocal test is the same source-backed test that feeds
  CCM25 QW and CC20 Mellin conventions.
```

Proof.

The common-test package ties:

```text
CCM24 fixed-S support test
CCM25 half-density test and F_g=g^* * g
CC20 Mellin/Fourier test
```

Evidence:

```text
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/cc20-trace-object-normalization-discharge.md
```

Therefore:

```text
SemilocalModelSymbols.Test
```

must be replaced by the CCM24 leg of the common source test package.

Failure blocked:

```text
support transport is proved for one test while finite-prime visibility is
computed for another.
```

## Lemma 4. Canonical Model Owns The Operator Coordinate

Statement:

```text
SourceCanonicalSemilocalModel(S):
  V_S=M_S U_S gives the canonical fixed-S coordinate, scaling action, and
  Fourier grading used by the route.
```

Proof.

CCM24 defines the canonical coordinate through:

```text
V_S=M_S U_S.
```

It also identifies the Fourier grading as reflection:

```text
s -> -s.
```

Evidence:

```text
mainc2m24fine.tex:237-253
mainc2m24fine.tex:786-804
docs/audits/source-reread-v0.2.md:43
```

The manuscript records that it moves between Hilbert-space coordinates only
through `U_S`, `M_S`, `V_S=M_S U_S`, bounded comparison, and Fourier
compatibility:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1310-1325
```

Thus:

```text
canonicalHilbertModel
scalingActionImplemented
fourierGradingCompatible
```

must become source theorem outputs.

Failure blocked:

```text
commutators and support projections are interpreted across mismatched Hilbert
spaces.
```

## Lemma 5. Support Transport Includes The Convolution Square

Statement:

```text
SourceConvolutionSupportTransport(g,I):
  support and Fourier support of g, and support of F_g=g^* * g, transport
  through the same CCM24 window.
```

Proof.

CCM24 supplies the support and Fourier transport:

```text
mainc2m24fine.tex:761-771
mainc2m24fine.tex:983-1003
```

The route uses the transported convolution square for finite-prime visibility:

```text
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
```

Therefore:

```text
supportTransported
convolutionSupportTransported
```

must be source-backed transport statements for the same test/window pair.

Failure blocked:

```text
finite-prime visibility is checked on a convolution square whose support was
not transported through the fixed-S CCM24 window.
```

## Lemma 6. Bounded Comparison Preserves The Class Already Proved

Statement:

```text
SourceBoundedComparisonTraceClassTransport(S):
  the CCM24 bounded comparison map and inverse preserve the bounded,
  Hilbert-Schmidt, trace-class, and graph-norm estimates supplied elsewhere.
```

Proof.

CCM24 gives a bounded comparison map and bounded inverse:

```text
mainc2m24fine.tex:806-823
docs/audits/source-reread-v0.2.md:45
```

This theorem does not supply trace-class estimates by itself. It transports the
analytic class after CC20 trace legality or endpoint-strip Cdef estimates have
supplied that class.

Evidence for those supplied classes:

```text
docs/proofs/cc20-trace-object-normalization-discharge.md
docs/proofs/battle-3-cdef-exhaustion-proof-package.md
```

Thus:

```text
boundedComparisonMap
boundedComparisonInverse
```

must be paired with a preservation theorem, not treated as inert existence
facts.

Failure blocked:

```text
a bounded comparison exists abstractly but does not preserve the trace-ideal
or norm class used downstream.
```

## Lemma 7. Sonin Exhaustion Fixes The Window Before The Limit

Statement:

```text
SourceFixedWindowSoninExhaustion(I,g):
  Sonin comparison and Cdef exhaustion keep g, I, S_A, and graph order fixed
  before lambda tends to infinity.
```

Proof.

CCM24 supplies Sonin-space comparison and fixed-window isomorphism:

```text
mainc2m24fine.tex:1050-1060
docs/audits/source-reread-v0.2.md:46
```

The fixed-test exhaustion package requires a fixed test/window before the
limit:

```text
docs/proofs/fixed-test-graph-cdef-exhaustion.md
```

Therefore:

```text
soninSpaceComparison
fixedWindowExhaustionCompatible
```

must be source-backed fixed-window statements.

Failure blocked:

```text
Cdef exhaustion changes the order of fixing g, I, S_A, graph order, and
lambda.
```

## Combined Result

The seven lemmas give:

```text
CCM24SemilocalObjectNormalization(S,I,lambda,g):
  SourcePlaceSetMatchesVisiblePrimes S g
  SourceSupportWindow I lambda g
  SourceCCM24TestCompatibility g
  SourceCanonicalSemilocalModel S
  SourceSupportAndFourierSupportTransport g I
  SourceConvolutionSupportTransport g I
  SourceBoundedComparisonTraceClassTransport S
  SourceFixedWindowSoninExhaustion I g
  SourceWindowLambdaCompatibility I lambda g
```

This strengthens:

```text
CanonicalSemilocalModelStatement
SupportTransportStatement
BoundedComparisonStatement
SoninComparisonStatement
WindowLambdaCompatibility
```

by naming the CCM24 source objects behind their fields.

## Formalization Consequence

A later Lean pass should avoid keeping CCM24 semilocal data as unrelated
predicates:

```text
PlaceSet
Window
Test
canonicalHilbertModel
supportInWindow
fourierSupportInWindow
supportTransported
convolutionSupportTransported
boundedComparisonMap
boundedComparisonInverse
soninSpaceComparison
fixedWindowExhaustionCompatible
```

without a source-owned package. The replacement layer should expose fields or
theorems shaped like:

```text
sourcePlaceSet_contains_visible_primes
sourceWindow_contained_in_lambda
sourceCCM24Test_matches_common_test
sourceCanonicalModel_eq_VS
sourceSupportTransport_eta_theta
sourceConvolutionSupportTransport
sourceBoundedComparison_preserves_trace_ideal
sourceFixedWindowSoninExhaustion
```

The route can then derive the compact symbolic statements from these theorems.

## Remaining Boundary

| task | reason |
|---|---|
| define the CCM24 finite place-set object | current `PlaceSet` is abstract |
| define the CCM24 support window object | current `Window` is abstract |
| formalize `V_S=M_S U_S` and Fourier grading | current canonical model fields are symbolic |
| formalize eta/theta support transport | current support predicates are symbolic |
| formalize bounded-comparison trace-ideal preservation | bounded maps must transport analytic classes |
| formalize fixed-window Sonin exhaustion | Cdef exhaustion must keep fixed data fixed |

This package does not prove RH. It removes one CCM24 ambiguity: the route must
use one source-backed fixed-`S` model and one source-backed support window
through positive trace, restricted `QW_lambda`, and Cdef exhaustion.
