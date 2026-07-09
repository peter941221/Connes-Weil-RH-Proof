# CCM25 Restricted QW Lambda Window Discharge

Status: proof package for the CCM25 restricted `QW_lambda` source-object
replacement gate.

This package attacks the source-object ledger rows:

```text
SourceRestrictedQWLambdaFormula
SourceRestrictedPrimeIndexCoverage
SourcePoleNormalization
SourceWindowLambdaContainment
```

It builds on the global CCM25 spine:

```text
QW(f,g)=Psi(f^* * g)
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)
```

and records how the restricted formula specializes that spine to the
`lambda`-window used by Theorem 1.

## Evidence Boundary

| claim | evidence |
|---|---|
| current Lean restricted formula statement | `ConnesWeilRH/Basic.lean:43,68-75` |
| current Lean restricted index field | `ConnesWeilRH/Basic.lean:47,81-84` |
| current Lean pole pairing statement | `ConnesWeilRH/Basic.lean:52,103-105` |
| route `WindowLambdaCompatibility` | `ConnesWeilRH/Route/Theorem1.lean:42-47,276-290` |
| restricted CCM25 source range | `mc2arXiv.tex:530-540`; `docs/audits/source-reread-v0.2.md:48` |
| manuscript restricted formula | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002` |
| visible-prime side condition | `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057,1368-1374` |
| global CCM25 spine package | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` |
| finite-prime support and pairing package | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| CCM24 one-window transport package | `docs/proofs/ccm24-support-window-transport-discharge.md` |

## Target Statement

For a source-backed fixed-`S` test `g` and a parameter `lambda > 1`, the
restricted source-object replacement must expose:

```text
QW_lambda(g,g)
  =
archimedean term on the lambda window
  + pole pairing
  - sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

It must also prove that the restricted index set is the `lambda`-window cut of
the global prime-power support for:

```text
F_g=g^* * g.
```

Lean-facing outputs:

```text
SourceRestrictedQWLambdaFormula(W,lambda,g)
SourceRestrictedPrimeIndexCoverage(W,lambda,F_g)
SourceRestrictedPolePairing(W,g)
SourceWindowLambdaContainment(S,I,lambda,g)
```

## Lemma 1. The Lambda Parameter Is Source-Owned

Statement:

```text
RestrictedLambdaIsSourceWindow(S,I,lambda,g):
  the `lambda` in `QW_lambda` is the same `lambda` that bounds the CCM24
  support window and the fixed-S positive trace.
```

Proof.

The Lean route already names this as:

```text
WindowLambdaCompatibility inputs g lambda.
```

It contains:

```text
1 < lambda
WindowSupportContainment inputs g lambda
lambdaCompatible g.window lambda
```

Evidence:

```text
ConnesWeilRH/Route/Theorem1.lean:42-47
ConnesWeilRH/Route/Theorem1.lean:276-290
docs/proofs/ccm24-support-window-transport-discharge.md:269-324
```

The CCM24 package supplies the one-window invariant:

```text
positive trace window = restricted Weil window = Cdef exhaustion window.
```

Thus the restricted formula cannot choose a fresh cutoff after the positive
trace has been formed.

Lean replacement target:

```text
WindowLambdaCompatibility inputs g lambda
```

Current failure if omitted:

```text
the fixed-S trace can be computed in one window while QW_lambda reads another.
```

## Lemma 2. QW Lambda Is The Restricted Source Form

Statement:

```text
CCM25RestrictedQWLambdaDefinition(lambda,g):
  QW_lambda(g,g) is the CCM25 restricted quadratic form on the source
  lambda-window.
```

Proof.

The manuscript records the restricted formula:

```text
QW_lambda(g,g)
  =
int_R |hat g(t)|^2 (2 partial_t theta(t))/(2 pi) dt
  +
2 Re(hat g(i/2) overline{hat g(-i/2)})
  -
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002
docs/audits/source-reread-v0.2.md:48
```

The Lean symbolic statement has the same three-part shape:

```text
archimedeanTerm (g^* * g)
  + polePairing g
  - restricted finite-prime sum.
```

Evidence:

```text
ConnesWeilRH/Basic.lean:68-75
```

This lemma replaces `WeilFormSymbols.qwLambda` with the source `QW_lambda`
object and keeps the three terms visible.

Lean replacement target:

```text
WeilFormSymbols.QWLambdaFormulaStatement W
```

Current failure if omitted:

```text
the route can satisfy the restricted read-off with a route-local quadratic
form that has the same outer shape but not the CCM25 source content.
```

## Lemma 3. Restricted Prime Support Is The Lambda Cut

Statement:

```text
CCM25RestrictedPrimeSupport(lambda,F_g):
  restrictedPrimeIndexSet lambda is the source prime-power support selected by
  the restricted formula, and visible atoms of F_g land in that set.
```

Proof.

The restricted formula uses:

```text
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:997-1001
docs/audits/source-reread-v0.2.md:48
```

The global `Psi` package identifies finite-prime terms as source `W_p(F)`
terms. The finite-prime support package identifies visible atoms as
prime-power evaluations of:

```text
F_g=g^* * g.
```

Evidence:

```text
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:66-148
```

Therefore `restrictedPrimeIndexSet lambda` must be the source support cut
selected by the `lambda` formula. It is not an arbitrary finite set and not a
post-hoc filter applied after the fixed-S trace.

Lean replacement target:

```text
WeilFormSymbols.RestrictedPrimeIndexCoverageStatement W lambda F_g
```

Current failure if omitted:

```text
the restricted formula can drop a prime-power atom visible to F_g while the
global formula still claims full finite-prime coverage.
```

## Lemma 4. The Restricted Pairing Uses The Same Source Pairing

Statement:

```text
CCM25RestrictedPrimePairing(lambda,g,n):
  the term inside the restricted finite-prime sum is the CCM25 pairing
  Lambda(n)<g|T(n)g>.
```

Proof.

The source formula records:

```text
<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:70-71
docs/manuscripts/connes-weil-rh-proof-draft.md:999-1001
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:190-260
```

The negative sign belongs to the surrounding `QW_lambda` formula, not to the
local pairing. This split matters because the global `Psi` formula already
owns the finite-prime sign:

```text
Psi(F)=...-sum_p W_p(F).
```

Lean replacement targets:

```text
WeilFormSymbols.primePowerPairing
WeilFormSymbols.vonMangoldtWeight
WeilFormSymbols.FinitePrimeTermNormalizationStatement
```

Current failure if omitted:

```text
the proof can put the correct restricted index set on the wrong coefficient
or pairing.
```

## Lemma 5. The Restricted Pole Pairing Is The Source Pole Functional

Statement:

```text
CCM25RestrictedPolePairing(g):
  the displayed pole pairing in QW_lambda is the restriction of W_(0,2) to
  the diagonal test g.
```

Proof.

The global pole functional is:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2).
```

The restricted formula displays:

```text
2 Re(hat g(i/2) overline{hat g(-i/2)}).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:67
docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md:140-174
docs/proofs/ccm25-restricted-read-off-discharge.md:316-358
```

So the restricted pole pairing must be tied to `poleFunctional (g^* * g)`.
The route `PoleJetExtra` ledger remains outside `QW_lambda`.

Lean replacement target:

```text
WeilFormSymbols.PoleNormalizationStatement W
```

Current failure if omitted:

```text
the proof can count the pole once in QW_lambda and again in the quotient
ledger, or kill the wrong pole channel.
```

## Lemma 6. The Restricted Formula Inherits The Global Sign

Statement:

```text
CCM25RestrictedGlobalSignCompatibility(lambda,g):
  QW_lambda uses the same sign spine as global QW/Psi.
```

Proof.

The global package fixes:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)
W_R=-W_infty.
```

The restricted formula displays:

```text
+ archimedean density
+ pole pairing
- restricted finite-prime sum.
```

Evidence:

```text
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md
docs/proofs/ccm25-restricted-read-off-discharge.md:379-433
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:305-340
```

Thus the restricted formula is not a separate convention. It is the
`lambda`-windowed form of the same source sign package that later feeds:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Lean replacement targets:

```text
CCM25PsiSignReadOff
CCM25QWLambdaFormulaReadOff
QWToCC20WeilInequalitySignBridge
```

Current failure if omitted:

```text
the restricted read-off can pass while the final global Weil positivity exit
uses a sign-incompatible form.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
CCM25RestrictedQWLambdaWindowDischarge(lambda,g):
  SourceRestrictedQWLambdaFormula(W,lambda,g)
  SourceRestrictedPrimeIndexCoverage(W,lambda,F_g)
  SourceRestrictedPolePairing(W,g)
  SourceWindowLambdaContainment(S,I,lambda,g)
  SourceRestrictedGlobalSignCompatibility(W,lambda,g)
```

The package strengthens the source-object replacement ledger:

```text
qwLambda and restrictedPrimeIndexSet lambda now have named replacement
bridges tied to the global QW/Psi spine.
```

## Formalization Consequence

A later Lean pass should not define:

```text
qwLambda : Real -> TestFunction -> TestFunction -> Real
restrictedPrimeIndexSet : Real -> Finset Nat
```

as unrelated fields.

It should expose a bridge package with fields or theorems shaped like:

```text
source_qwLambda_eq_windowed_QW
source_restrictedPrimeIndexSet_eq_lambda_prime_power_support
source_restrictedPolePairing_eq_W02_diagonal
source_qwLambda_finite_sum_uses_global_Wp_terms
source_qwLambda_sign_inherits_PsiSignSplit
```

The final route certificate should consume this package before it consumes
`FixedSPositiveTraceReadOff` or the `QW_lambda -> QW` exhaustion step.

## Remaining Boundary

| task | reason |
|---|---|
| define or import source `QW_lambda` | this package cites source formulas and manuscript anchors |
| formalize the lambda-window support cut | `restrictedPrimeIndexSet lambda` remains symbolic |
| formalize the window bridge from CCM24 | `WindowLambdaCompatibility` still relies on symbolic CCM24 predicates |
| formalize the restricted pole pairing | `polePairing` remains symbolic |
| connect restricted `QW_lambda` to global `QW` in the limit | this package fixes the restricted object but not the exhaustion theorem |

This package does not prove RH. It blocks a specific source-object failure:
the restricted positive-trace read-off cannot use a `lambda`-windowed form that
drifts away from the global CCM25 Weil form.
