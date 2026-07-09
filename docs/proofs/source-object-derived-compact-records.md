# Source Object Derived Compact Records

Status: proof package for deriving the current compact Lean records from the
expanded source-object packages.

This package is the mathematical specification for:

```text
formalization/source-object-interface-plan.md
```

It proves, at proof-package level, that the expanded source-object packages can
derive the compact records already consumed by the route:

```text
SemilocalModelSymbols
WeilFormSymbols
ArchimedeanTraceSymbols
FiniteVanishingCriterionPackage
```

It does not edit Lean code and does not prove the analytic source theorems.

## Evidence Boundary

| object | evidence |
|---|---|
| compact symbolic records | `ConnesWeilRH/Basic.lean:41-210` |
| route source interfaces | `ConnesWeilRH/Source/CCM24.lean`, `ConnesWeilRH/Source/CCM25.lean`, `ConnesWeilRH/Source/CC20.lean` |
| current route consumers | `ConnesWeilRH/Route/*` |
| interface plan | `formalization/source-object-interface-plan.md` |
| consistency audit | `docs/audits/source-object-replacement-consistency-audit.md` |
| CCM24 object package | `docs/proofs/ccm24-semilocal-object-normalization-discharge.md` |
| CCM25 object package | `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` |
| CC20 trace object package | `docs/proofs/cc20-trace-object-normalization-discharge.md` |
| CC20 RH exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |

## Target Statement

The derivation target is:

```text
SourceObjectPackageDerivesCompactRecords:
  SourceObjectPackage
    ->
  SemilocalModelSymbols
    x
  WeilFormSymbols
    x
  ArchimedeanTraceSymbols
    x
  FiniteVanishingCriterionPackage
```

with theorem outputs:

```text
CanonicalSemilocalModelStatement
SupportTransportStatement
BoundedComparisonStatement
SoninComparisonStatement

QWDefinitionStatement
PsiSignStatement
QWLambdaFormulaStatement
FinitePrimeNormalizationStatement
PoleNormalizationStatement

TraceSquareStatement
TraceClassTemplateStatement
MellinHalfDensityConventionStatement
SignsAndNormalizationsStatement

finiteSetAdmissible
criterion
```

The compact records are allowed to survive as route-facing views. They are not
allowed to serve as final source evidence without this derivation.

## Lemma 1. Derived SemilocalModelSymbols

Statement:

```text
SourceObjectPackage.toSemilocalModelSymbols:
  CCM24SemilocalObjectPackage
    ->
  SemilocalModelSymbols
```

and:

```text
SourceObjectPackage.provesSemilocalStatements:
  CanonicalSemilocalModelStatement
  SupportTransportStatement
  BoundedComparisonStatement
  SoninComparisonStatement.
```

Proof.

The CCM24 source-object package supplies:

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

Evidence:

```text
docs/proofs/ccm24-semilocal-object-normalization-discharge.md
```

Map the source objects to compact fields:

| compact field | source-object evidence |
|---|---|
| `PlaceSet` | CCM24 finite place-set object |
| `Window` | CCM24 source support window |
| `Test` | common source test, through the CCM24 leg |
| `canonicalHilbertModel` | `SourceCanonicalSemilocalModel` |
| `scalingActionImplemented` | same canonical model package |
| `fourierGradingCompatible` | same canonical model package |
| `supportInWindow` | `SourceSupportWindow` |
| `fourierSupportInWindow` | `SourceSupportAndFourierSupportTransport` |
| `supportTransported` | `SourceSupportAndFourierSupportTransport` |
| `convolutionSupportTransported` | `SourceConvolutionSupportTransport` |
| `windowContainedInLambda` | `SourceWindowLambdaCompatibility` |
| `lambdaCompatible` | `SourceWindowLambdaCompatibility` |
| `boundedComparisonMap` | `SourceBoundedComparisonTraceClassTransport` |
| `boundedComparisonInverse` | same bounded comparison package |
| `soninSpaceComparison` | `SourceFixedWindowSoninExhaustion` |
| `fixedWindowExhaustionCompatible` | same Sonin package |

Then the four compact statements follow by projection from the source package:

```text
CanonicalSemilocalModelStatement
SupportTransportStatement
BoundedComparisonStatement
SoninComparisonStatement.
```

Failure blocked:

```text
SemilocalModelSymbols fields are supplied as unrelated route-local predicates.
```

## Lemma 2. Derived WeilFormSymbols

Statement:

```text
SourceObjectPackage.toWeilFormSymbols:
  CCM25WeilObjectPackage
    ->
  WeilFormSymbols
```

and:

```text
SourceObjectPackage.provesWeilFormStatements:
  QWDefinitionStatement
  PsiSignStatement
  QWLambdaFormulaStatement
  FinitePrimeNormalizationStatement
  PoleNormalizationStatement.
```

Proof.

The CCM25 source-object packages supply:

```text
SourceQWDefinition
SourcePsiSignSplit
SourceRestrictedQWLambdaFormula
SourceGlobalPrimePowerSupport
SourceRestrictedPrimePowerSupport
SourceVonMangoldtWeight
SourcePrimePowerPairing
SourceFinitePrimeTermNormalization
SourcePoleNormalization
SourceArchimedeanSignBridge
```

Evidence:

```text
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md
```

Map the source objects to compact fields:

| compact field | source-object evidence |
|---|---|
| `qw` | CCM25 source `QW` |
| `qwLambda` | CCM25 source `QW_lambda` |
| `psi` | CCM25 source `Psi` |
| `convolutionStar` | common source convolution square |
| `globalPrimeIndexSet` | source global prime-power support |
| `restrictedPrimeIndexSet lambda` | source lambda cut `1<n<=lambda^2` |
| `finitePrimeAtomVisible` | source visible prime-power atom predicate |
| `finitePrimeTerm` | source finite-prime atom term |
| `archimedeanTerm` | CCM25 archimedean term with CC20-compatible sign |
| `poleFunctional` | source `W_(0,2)` pole functional |
| `polePairing` | restricted source pole pairing |
| `primePowerPairing` | source `<g|T(n)g>` |
| `vonMangoldtWeight` | source `Lambda(n)` |

The compact formula statements follow:

```text
QWDefinitionStatement
```

from:

```text
QW(f,g)=Psi(f^* * g).
```

```text
PsiSignStatement
```

from:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)
```

with the source sign split.

```text
QWLambdaFormulaStatement
```

from the restricted `QW_lambda` formula and the CCM24 window compatibility.

```text
FinitePrimeNormalizationStatement
```

from pointwise source term normalization:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>
```

for every source prime-power index `n`.

```text
PoleNormalizationStatement
```

from the global and restricted pole packages.

Failure blocked:

```text
finite-prime or sign data are hidden inside a sum-level equality or a
route-local positivity predicate.
```

## Lemma 3. Derived ArchimedeanTraceSymbols

Statement:

```text
SourceObjectPackage.toArchimedeanTraceSymbols:
  CC20TraceObjectPackage
    ->
  ArchimedeanTraceSymbols
```

and:

```text
SourceObjectPackage.provesTraceStatements:
  TraceSquareStatement
  TraceClassTemplateStatement
  MellinHalfDensityConventionStatement
  SignsAndNormalizationsStatement.
```

Proof.

The CC20 trace object package supplies:

```text
SourceCC20TraceTestCompatibility
SourceHilbertSchmidtGate
SourceTraceClassCyclicityTemplate
SourcePositiveTraceNonnegative
SourceSupportSquareTraceReadOff
SourceNoDefectTraceReadOff
SourceMellinHalfDensityCompatibility
SourceCC20SignNormalizations
```

Evidence:

```text
docs/proofs/cc20-trace-object-normalization-discharge.md
```

Map the source objects to compact fields:

| compact field | source-object evidence |
|---|---|
| `Test` | CC20 trace test tied to the common source test |
| `supportSquareTrace` | source support-square trace |
| `sourceNoDefectTrace` | source no-defect trace |
| `positiveTrace` | ordinary trace `Tr(A^*A)` |
| `traceClass` | CC20 trace-class theorem output |
| `cyclicLegal` | CC20 cyclic trace legality output |
| `hilbertSchmidtGate` | CC20 Hilbert-Schmidt gate |
| `mellinHalfDensityMatched` | source Mellin half-density bridge |
| `uInfinityNormalized` | CC20 sign normalization |
| `qduNormalized` | CC20 quantized differential sign |
| `archimedeanSignNormalized` | CC20-to-CCM25 archimedean sign bridge |

Then:

```text
TraceClassTemplateStatement
```

comes from the chain:

```text
Hilbert-Schmidt gate -> trace-class and cyclicity.
```

```text
TraceSquareStatement
```

comes only after:

```text
trace-class and cyclicity
  -> support-square trace read-off
  -> no-defect source trace read-off
  -> positive trace nonnegativity.
```

The Mellin and sign statements follow from their named source bridge packages.

Failure blocked:

```text
positive trace, support-square trace, and no-defect trace are treated as the
same scalar without source equalities.
```

## Lemma 4. Derived FiniteVanishingCriterionPackage

Statement:

```text
SourceObjectPackage.toFiniteVanishingCriterionPackage:
  CC20RHExitObjectPackage
    ->
  FiniteVanishingCriterionPackage
```

with:

```text
finiteSetAdmissible
criterion : input -> tripleVanishing -> fullWeilPositivity -> RH.
```

Proof.

The CC20 RH exit package supplies:

```text
SourceFiniteSetF
SourceFiniteSetAdmissibility
SourceTripleVanishingOnF
SourceCC20WeilInequality
SourceCC20PropositionC1
SourceFiniteVanishingCriterionToMathlibRH
```

Evidence:

```text
docs/proofs/cc20-rh-exit-object-normalization-discharge.md
docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md
```

The compact field:

```text
finiteSetAdmissible
```

is `SourceFiniteSetAdmissibility` for the fixed source set:

```text
F={0,1/2,1}.
```

The compact field:

```text
criterion
```

is derived by this chain:

```text
route triple vanishing
  -> CC20 Mellin vanishing on F

route full Weil positivity
  -> QW(g,g) >= 0
  -> CC20 nonpositivity through QW(g,g) = -sum_v W_v

CC20 Proposition C.1
  -> CC20 source RH

source RH to Mathlib bridge
  -> _root_.RiemannHypothesis.
```

The final target remains:

```text
_root_.RiemannHypothesis.
```

Failure blocked:

```text
FiniteVanishingCriterionPackage.criterion acts as a route-local RH axiom.
```

## Combined Result

Combining Lemmas 1 through 4 gives:

```text
SourceObjectPackageDerivesCompactRecords:
  expanded source-object packages
    ->
  compact source interfaces consumed by the existing route.
```

The route can keep using:

```text
inputs.ccm24.semilocalSymbols
inputs.ccm25.weilSymbols
inputs.cc20.archimedeanSymbols
inputs.cc20.finiteVanishingRhExit
```

only after those views are derived from the expanded package.

## Formalization Consequence

The next Lean pass should implement the derivation in two layers:

```text
ConnesWeilRH.Source.Objects
  defines expanded source-object package records

ConnesWeilRH.Source.ObjectDerivations
  defines projections to compact records and proves compact statements
```

The implementation should keep route modules stable at first. The route should
continue consuming compact records, but those records should be constructed
from expanded source-object packages in the source layer.

## Remaining Boundary

| task | reason |
|---|---|
| create Lean records for expanded packages | this document is only a specification |
| prove compact-record derivation in Lean | needed before route can claim source-object package visibility |
| formalize or import source theorems | expanded packages still contain source theorem fields |
| rerun axiom audit | the final theorem must not gain new project-local axioms |

This package does not prove RH. It makes the next Lean interface step
semantics-preserving: expanded source-object evidence should derive the compact
records, not replace them with unrelated route assumptions.
