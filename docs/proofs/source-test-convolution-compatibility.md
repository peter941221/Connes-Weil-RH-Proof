# Source Test And Convolution Compatibility

Status: proof package for the common test-object and convolution-square gate in
the source-object replacement phase.

This package attacks the first two rows of the source-object definition ledger:

```text
SourceTestFunctionCompatibility
SourceConvolutionSquareReadOff
```

It does not replace the current Lean type:

```text
TestFunction := Type
```

It records the mathematical bridge that a later Lean/import pass must expose
before replacing that placeholder.

## Evidence Boundary

| claim | evidence |
|---|---|
| current Lean test placeholder | `ConnesWeilRH/Basic.lean:39` |
| current Lean convolution placeholder | `ConnesWeilRH/Basic.lean:45,58-60,68-75,86-94` |
| CCM25 full test conversion | `docs/manuscripts/connes-weil-rh-proof-draft.md:66`; `docs/audits/source-reread-v0.2.md:47` |
| CCM25 restricted formula and pairing | `docs/manuscripts/connes-weil-rh-proof-draft.md:70-71,988-1002`; `docs/audits/source-reread-v0.2.md:48` |
| CC20 half-density convention | `docs/manuscripts/connes-weil-rh-proof-draft.md:87,1224-1238`; `docs/audits/source-reread-v0.2.md:51` |
| CC20 finite-vanishing convention | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:166-227` |
| fixed-S visible-prime side condition | `docs/manuscripts/connes-weil-rh-proof-draft.md:309-326,1043-1057,1368-1374` |
| current definition-ledger rows | `docs/audits/source-object-definition-ledger.md` |

## Target Statement

For the source-backed fixed-`S` test `g`, the route must use one test object
through three source interfaces:

```text
CCM24 support-window test
      |
      v
CCM25 half-density test g and F_g=g^* * g
      |
      v
CC20 Mellin/Fourier test used in Proposition C.1
```

The required bridge is:

```text
SourceTestFunctionCompatibility(g):
  the CCM24, CCM25, and CC20 test objects are the same test after the
  recorded half-density and support-coordinate identifications.

SourceConvolutionSquareReadOff(g):
  the source test read by CCM25 `Psi`, by the restricted finite-prime support,
  by the CC20 support-square trace, and by the final Mellin vanishing condition
  is the same convolution square

    F_g = g^* * g.
```

## Lemma 1. CCM25 Owns The Convolution Square

Statement:

```text
CCM25SourceConvolutionSquare(g):
  QW(g,g) is evaluated through Psi(F_g), where F_g=g^* * g.
```

Proof.

The CCM25 full Weil form enters the route through:

```text
QW(f,g)=Psi(f^* * g).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:66
docs/audits/source-reread-v0.2.md:47
```

The diagonal case gives:

```text
QW(g,g)=Psi(g^* * g).
```

Thus the finite-prime, archimedean, and pole pieces inside `Psi` all evaluate
the same test:

```text
F_g=g^* * g.
```

Lean replacement target:

```text
WeilFormSymbols.convolutionStar
WeilFormSymbols.QWDefinitionStatement
```

Current failure if omitted:

```text
QW(g,g) could be proved for a route-local product while the source `Psi`
acts on a different test.
```

## Lemma 2. The Restricted Formula Uses The Same Square

Statement:

```text
CCM25RestrictedConvolutionSquare(lambda,g):
  the restricted formula `QW_lambda(g,g)` uses the same `F_g=g^* * g`
  in its prime-power pairing and finite-prime support.
```

Proof.

The restricted formula uses the diagonal test `g` and the prime-power pairing:

```text
<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:70-71
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002
docs/audits/source-reread-v0.2.md:48
```

The finite-prime support condition also refers to the support of:

```text
F_g=g^* * g.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:309-326
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
```

Therefore the restricted finite-prime support and the restricted finite-prime
pairing must share the same convolution square. Coverage and normalization
cannot use separate tests.

Lean replacement targets:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

Current failure if omitted:

```text
the restricted index set could cover the support of one test while
`primePowerPairing n g g` evaluates another.
```

## Lemma 3. CC20 Half-Density Convention Preserves The Test

Statement:

```text
CC20HalfDensityTestCompatibility(g):
  the CC20 Mellin/Fourier convention sends the route half-density test to
  the same source test used by CCM25.
```

Proof.

CC20 relates the source multiplicative test `k` and the half-density test `f`
by:

```text
f(x)=x^(1/2) k(x)
```

and records the Mellin/Fourier variable convention used by the final exit.

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:87
docs/manuscripts/connes-weil-rh-proof-draft.md:1224-1238
docs/audits/source-reread-v0.2.md:51
docs/proofs/cc20-trace-legality-mellin-discharge.md:293-341
```

The route uses this convention twice:

```text
1. The CC20 support-square trace reads the no-defect trace for the same
   half-density test.
2. The final finite-vanishing exit translates route triple vanishing to
   Mellin vanishing on F={0,1/2,1}.
```

Evidence for the final translation:

```text
docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:166-227
```

Thus the half-density bridge must state more than a variable substitution. It
must identify the test used in the CC20 trace and in the final Mellin
vanishing condition with the CCM25 test `g`.

Lean replacement targets:

```text
ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
FiniteVanishingCriterionPackage.criterion
```

Current failure if omitted:

```text
the route can prove triple vanishing for a centered half-density test while
CC20 Proposition C.1 receives a different Mellin test.
```

## Lemma 4. CCM24 Carries The Same Fixed-S Test

Statement:

```text
CCM24FixedSTestCompatibility(S,I,lambda,g):
  the fixed-S support, Fourier support, and convolution-support facts are
  attached to the same source test `g` and the same square `F_g`.
```

Proof.

The CCM24 support-window bridge records:

```text
source support in the CCM24 window
Fourier support in the same window
convolution-support transport
window containment in [lambda^-1,lambda]
```

Evidence:

```text
docs/proofs/ccm24-support-window-transport-discharge.md
docs/audits/source-object-definition-ledger.md
```

The restricted CCM25 read-off requires that same window before it reads the
fixed-S trace as the full restricted form:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md:76-112
```

The admissibility side condition also uses the square:

```text
F_g=g^* * g.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:899
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
```

So the CCM24 test object cannot be a separate route-local carrier. It must
bridge to the same `g` whose square enters CCM25 and whose Mellin transform
enters CC20.

Lean replacement targets:

```text
SemilocalModelSymbols.supportInWindow
SemilocalModelSymbols.fourierSupportInWindow
SemilocalModelSymbols.convolutionSupportTransported
```

Current failure if omitted:

```text
fixed-S support transport can certify one test while QW_lambda reads another.
```

## Lemma 5. One Test Controls Vanishing, Support, And Positivity

Statement:

```text
UnifiedRouteTest(g):
  the same source-backed test `g` controls:
    support admissibility,
    finite-prime visibility of F_g,
    trace legality,
    restricted QW_lambda read-off,
    triple vanishing,
    and the final CC20 positivity criterion.
```

Proof.

The route uses `g` in six places:

| use | source owner |
|---|---|
| support and Fourier support | CCM24 |
| convolution square `F_g=g^* * g` | CCM25 and CC20 |
| finite-prime support of `F_g` | CCM25 |
| positive trace and cyclicity gates | CC20 trace template |
| triple vanishing | CC20 Mellin/Fourier convention |
| final inequality `sum_v W_v(F_g) <= 0` | CC20 Proposition C.1 plus CCM25 sign bridge |

Previous packages cover each local gate. This package adds the missing global
constraint: those gates must quantify over the same source-backed test.

The dependency picture is:

```text
             CCM24 support window
                    |
                    v
test g -----> F_g=g^* * g -----> CCM25 QW / QW_lambda
  |                 |
  |                 v
  |          finite-prime visibility
  |
  v
CC20 Mellin test -----> finite vanishing on {0,1/2,1}
  |
  v
CC20 Weil inequality for F_g
```

The theorem-source bridge should expose this as one compatibility package
rather than separate unconnected `Prop` fields.

## Combined Result

Combining Lemmas 1 through 5 gives:

```text
SourceTestConvolutionCompatibility(S,I,lambda,g)
```

with two Lean-facing outputs:

```text
SourceTestFunctionCompatibility(g)
SourceConvolutionSquareReadOff(g)
```

The package closes the first source-object definition ledger item at
proof-package level:

```text
`TestFunction := Type` and `convolutionStar` have a named replacement bridge.
```

## Formalization Consequence

A later Lean replacement should not introduce independent source objects:

```text
ccm24Test : M.Test
ccm25Test : TestFunction
cc20Test : A.Test
```

unless it also supplies bridge fields:

```text
ccm24Test_maps_to_ccm25Test
ccm25ConvolutionSquare_eq_cc20SupportSquare
cc20MellinTest_eq_sourceTest
tripleVanishing_eq_mellinVanishingOnFiniteSet
```

The final route certificate should consume the bridge package before it consumes
finite-prime coverage, trace read-off, sign bridge, or RH exit data.

## Remaining Boundary

| task | reason |
|---|---|
| define or import the common test-function class | this package still works at proof-package level |
| formalize the half-density convolution and involution | `convolutionStar` remains symbolic in Lean |
| formalize the support-window map from CCM24 to the test object | current CCM24 predicates remain abstract |
| formalize the CC20 Mellin bridge | the final vanishing translation still depends on the source convention |

This package does not prove RH. It blocks a specific certification failure:
the route cannot later prove the correct-looking equations while applying them
to different source tests.
