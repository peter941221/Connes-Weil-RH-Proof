# CCM25 QW Psi Definition Sign Discharge

Status: proof package for the CCM25 global `QW` and `Psi` source-object
replacement gate.

This package attacks the source-object ledger rows:

```text
SourceQWDefinition
SourcePsiSignSplit
SourceGlobalPrimeIndexCoverage
SourceArchimedeanSignBridge
SourcePoleNormalization
```

It does not replace the symbolic Lean fields yet:

```text
WeilFormSymbols.qw
WeilFormSymbols.psi
WeilFormSymbols.archimedeanTerm
WeilFormSymbols.poleFunctional
WeilFormSymbols.globalPrimeIndexSet
WeilFormSymbols.finitePrimeTerm
```

It records the theorem shape a later Lean/import pass must expose before those
fields can become source definitions.

## Evidence Boundary

| claim | evidence |
|---|---|
| current Lean `QW` statement | `ConnesWeilRH/Basic.lean:42,58-60` |
| current Lean `Psi` sign statement | `ConnesWeilRH/Basic.lean:44,62-66` |
| current Lean finite-prime global index field | `ConnesWeilRH/Basic.lean:46,78-80` |
| current Lean archimedean and pole fields | `ConnesWeilRH/Basic.lean:50-52,103-105` |
| CCM25 source range for `W_p`, `W_R`, `QW`, `Psi`, and `W_(0,2)` | `mc2arXiv.tex:445-470`; `docs/audits/source-reread-v0.2.md:47` |
| manuscript formula map | `docs/manuscripts/connes-weil-rh-proof-draft.md:66-69,971-985,1115-1126,1349-1357` |
| common source test and convolution square | `docs/proofs/source-test-convolution-compatibility.md` |
| finite-prime support and pairing package | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| final CC20 sign bridge | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` |

## Target Statement

For every source test `F` and every source-backed half-density test pair
`f,g`, the CCM25 global Weil-form replacement must expose:

```text
QW(f,g)=Psi(f^* * g)
```

and:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

Together with:

```text
W_R=-W_infty.
```

The Lean-facing replacement is:

```text
SourceQWDefinition(W):
  WeilFormSymbols.QWDefinitionStatement W

SourcePsiSignSplit(W):
  WeilFormSymbols.PsiSignStatement W
```

where the symbolic fields are no longer free fields but source objects:

```text
qw              -> CCM25 QW
psi             -> CCM25 Psi
convolutionStar -> source half-density convolution square
poleFunctional  -> W_(0,2)
archimedeanTerm -> W_R in the Psi formula, with the CC20 bridge recording W_R=-W_infty
finitePrimeTerm -> W_p terms indexed by source prime-power support
```

## Lemma 1. QW Is Defined Through Psi

Statement:

```text
CCM25QWDefinition(f,g):
  QW(f,g)=Psi(f^* * g).
```

Proof.

The manuscript records the CCM25 formula:

```text
QW(f,g)=Psi(f^* * g).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:66
docs/manuscripts/connes-weil-rh-proof-draft.md:973
docs/audits/source-reread-v0.2.md:47
```

The common-test package fixes the product:

```text
f^* * g
```

as the same half-density convolution used by CCM25 and CC20:

```text
docs/proofs/source-test-convolution-compatibility.md
```

Therefore a formal replacement for `WeilFormSymbols.qw` cannot define a new
bilinear form and later identify it by convention. It must define or import
`QW` through the source distribution `Psi` on the source convolution product.

Lean replacement target:

```text
WeilFormSymbols.QWDefinitionStatement W
```

Current failure if omitted:

```text
the route can prove positivity for a quadratic form that is not the CCM25
Weil form.
```

## Lemma 2. Psi Has Three Visible Source Legs

Statement:

```text
CCM25PsiSignSplit(F):
  Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

Proof.

The source formula decomposes `Psi` into:

```text
pole leg:          W_(0,2)(F)
archimedean leg:   -W_R(F)
finite-prime leg:  -sum_p W_p(F)
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:68-69
docs/manuscripts/connes-weil-rh-proof-draft.md:975-985
docs/manuscripts/connes-weil-rh-proof-draft.md:1118-1126
docs/audits/source-reread-v0.2.md:47
```

This split must stay visible in Lean. A single opaque equality for `Psi` would
hide the two places where sign errors enter:

```text
-W_R(F)
-sum_p W_p(F)
```

Lean replacement target:

```text
WeilFormSymbols.PsiSignStatement W
```

Current failure if omitted:

```text
the proof can import a source-named `Psi` while silently changing the
archimedean or finite-prime sign.
```

## Lemma 3. Pole Functional Is W_(0,2)

Statement:

```text
CCM25PoleFunctionalDefinition(F):
  poleFunctional(F)=W_(0,2)(F)=hat F(i/2)+hat F(-i/2).
```

Proof.

The manuscript records the pole functional:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:67
docs/manuscripts/connes-weil-rh-proof-draft.md:977
docs/proofs/ccm25-restricted-read-off-discharge.md:316-358
```

The restricted form displays the diagonal pole pairing, and the restricted
read-off package keeps the route `PoleJetExtra` ledger outside `QW_lambda` until
triple vanishing kills it.

Therefore the global pole field must map to source `W_(0,2)`, not to the route
quotient pole ledger.

Lean replacement targets:

```text
WeilFormSymbols.poleFunctional
WeilFormSymbols.PoleNormalizationStatement
```

Current failure if omitted:

```text
the route can kill a project pole ledger while leaving the source pole
functional unaccounted for.
```

## Lemma 4. The Archimedean Term Keeps The W_R Sign

Statement:

```text
CCM25ArchimedeanTermDefinition(F):
  the archimedean term in Psi is W_R(F), and CCM25 records W_R=-W_infty.
```

Proof.

The `Psi` formula contains:

```text
-W_R(F).
```

CCM25 records:

```text
W_R=-W_infty.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:68
docs/manuscripts/connes-weil-rh-proof-draft.md:979-985
docs/manuscripts/connes-weil-rh-proof-draft.md:1017
docs/manuscripts/connes-weil-rh-proof-draft.md:1353-1354
docs/audits/source-reread-v0.2.md:47
```

Thus:

```text
-W_R(F)=+W_infty(F)
```

under the CC20-compatible archimedean convention. The final sign bridge uses
this equality when it rewrites `QW(g,g)` as the negative of the CC20 local Weil
sum.

Lean replacement target:

```text
WeilFormSymbols.archimedeanTerm
```

plus the bridge:

```text
SourceArchimedeanSignBridge
```

Current failure if omitted:

```text
the restricted formula can display the correct positive archimedean density
while the global Psi formula keeps the wrong sign.
```

## Lemma 5. The Global Finite-Prime Leg Is Source-Indexed

Statement:

```text
CCM25GlobalFinitePrimeLeg(F):
  the global finite-prime leg in Psi is the source sum over finite-prime
  terms W_p(F), not an arbitrary finite set.
```

Proof.

The finite-prime part of the source formula is:

```text
-sum_p W_p(F).
```

The source finite-prime term has the prime-power shape:

```text
W_p(F)=(log p) sum_(m>=1) p^(-m/2)(F(p^m)+F(p^(-m))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:69
docs/manuscripts/connes-weil-rh-proof-draft.md:971
docs/manuscripts/connes-weil-rh-proof-draft.md:1018
docs/manuscripts/connes-weil-rh-proof-draft.md:1355
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:66-97
```

The global index set in Lean must therefore become a source prime-power support
object. It cannot be an empty placeholder or a finite route-local set chosen
after the test has been fixed.

Lean replacement targets:

```text
WeilFormSymbols.globalPrimeIndexSet
WeilFormSymbols.finitePrimeTerm
WeilFormSymbols.GlobalPrimeIndexCoverageStatement
```

Current failure if omitted:

```text
the global `Psi` formula can erase finite primes before the restricted
coverage theorem checks them.
```

## Lemma 6. Restricted QW Lambda Inherits The Global Sign Spine

Statement:

```text
CCM25RestrictedInheritsGlobalSign(lambda,g):
  the restricted formula `QW_lambda(g,g)` is the windowed form of the same
  global `Psi` sign convention.
```

Proof.

The restricted read-off package records:

```text
QW_lambda(g,g)
  =
archimedean term
  + pole pairing
  - restricted finite-prime sum.
```

Evidence:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md:172-225
docs/proofs/ccm25-restricted-read-off-discharge.md:379-433
```

The finite-prime support package records that the local summand is the source
von Mangoldt and prime-power pairing contribution, with the negative sign owned
by the surrounding `QW_lambda` formula:

```text
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:150-260
```

So the restricted formula cannot use a separate sign convention. It inherits:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

Lean replacement targets:

```text
CCM25PsiSignReadOff
CCM25QWLambdaFormulaReadOff
```

Current failure if omitted:

```text
the route can pass the restricted theorem while the final global `QW` exit
uses a different sign convention.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
CCM25QWPsiDefinitionSignDischarge(W):
  SourceQWDefinition(W)
  SourcePsiSignSplit(W)
  SourceGlobalPrimeIndexCoverage(W)
  SourceArchimedeanSignBridge(W)
  SourcePoleNormalization(W)
```

The proof-package output matches the current Lean source interface:

```text
ccm25QWDefinition:
  QWDefinitionStatement W and PsiSignStatement W
```

and strengthens the source-object replacement ledger:

```text
qw, psi, archimedeanTerm, poleFunctional, globalPrimeIndexSet, and
finitePrimeTerm now have named source replacement bridges.
```

## Formalization Consequence

A later Lean pass should not replace:

```text
WeilFormSymbols.psi
```

with a single uninterpreted function plus one end theorem. It should expose
separate fields or theorems for:

```text
source_qw_eq_psi_convolution
source_psi_eq_pole_minus_archimedean_minus_finite_primes
source_archimedean_WR_eq_neg_Winfty
source_poleFunctional_eq_W02
source_globalPrimeIndexSet_covers_Wp_terms
```

The final route certificate should consume these bridges before it consumes
`fullWeilPositivity` or the CC20 finite-vanishing exit package.

## Remaining Boundary

| task | reason |
|---|---|
| define or import CCM25 `QW` and `Psi` | this package cites source formulas and manuscript anchors |
| define the global prime-power support object | `globalPrimeIndexSet` remains symbolic |
| formalize the archimedean sign bridge to CC20 | this package names the bridge but does not prove CC20 analysis |
| formalize `W_(0,2)` and its restricted pairing | pole normalization still needs a source theorem or formal proof |
| connect this package to `QWToCC20WeilInequalitySignBridge` in Lean | the final sign bridge remains proof-package level |

This package does not prove RH. It prevents a specific source-object failure:
the final positivity argument cannot treat an arbitrary `QW` and `Psi` pair as
the CCM25 Weil form without exposing the source sign split.
