# CCM25 Finite-Prime Index Normalization Discharge

Status: source-object replacement package for CCM25 finite-prime indices,
weights, pairings, and term normalization.

This package sharpens:

```text
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md
```

The earlier package proves the route-level finite-prime obligations:

```text
GlobalPrimeIndexCoverageStatement W F_g
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

This package records the source definitions that must replace the symbolic
fields behind those statements. Its target is the concrete CCM25 indexing
spine:

```text
prime-power index n
  |
  v
lambda-window condition 1 < n <= lambda^2
  |
  v
von Mangoldt coefficient Lambda(n)
  |
  v
source pairing <g|T(n)g>
  |
  v
finite-prime term Lambda(n)<g|T(n)g>
```

## Evidence Boundary

| claim | evidence |
|---|---|
| global finite-prime source term | `docs/manuscripts/connes-weil-rh-proof-draft.md:53,69` |
| restricted finite-prime source term | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002` |
| restricted finite-prime sign | `docs/manuscripts/connes-weil-rh-proof-draft.md:1017-1019,1349-1366` |
| fixed-S visible-prime side condition | `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057,1368-1374` |
| source reread anchors | `docs/audits/source-reread-v0.2.md:47-48` |
| symbolic Lean fields | `ConnesWeilRH/Basic.lean:46-54,77-101` |
| current route consumers | `ConnesWeilRH/Route/AdmissibleWindow.lean:43-68` |
| previous finite-prime package | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| restricted-window package | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` |

## Problem

The current Lean-facing finite-prime layer exposes enough structure to prevent
an empty restricted index set:

```text
finitePrimeAtomVisible n F_g -> n in restrictedPrimeIndexSet lambda.
```

That statement does not yet say what `n` is. It also does not say that the
restricted set is exactly the CCM25 source range:

```text
1 < n <= lambda^2.
```

Nor does it force the term to use the source arithmetic coefficient and source
operator pairing:

```text
Lambda(n)<g|T(n)g>.
```

The next replacement pass must therefore split `Nat`-indexed coverage into
source-level data:

```text
source prime-power support
source lambda cut
source Lambda(n)
source <g|T(n)g>
source finite-prime term
```

## Target Statement

For the source-backed fixed-`S` test `g`, let:

```text
F_g = g^* * g.
```

The finite-prime index normalization target is:

```text
CCM25FinitePrimeIndexNormalization(lambda,g):
  each visible finite-prime atom of F_g is represented by a source
  prime-power index n;

  restrictedPrimeIndexSet lambda is the lambda-window cut of those source
  prime-power indices;

  finitePrimeTerm n F_g equals Lambda(n)<g|T(n)g> with the source CCM25
  pairing convention.
```

Lean-facing replacement outputs:

```text
SourcePrimePowerIndex
SourceGlobalPrimePowerSupport
SourceRestrictedPrimePowerSupport(lambda)
SourceVonMangoldtWeight
SourcePrimePowerPairing
SourceFinitePrimeTermNormalization
```

## Lemma 1. Source Prime-Power Index

Statement:

```text
SourcePrimePowerIndex(n):
  n is a source prime-power index used by the CCM25 finite-prime term.
```

Proof.

The global finite-prime term is:

```text
W_p(F)=(log p) sum_(m>=1) p^(-m/2)(F(p^m)+F(p^(-m))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:53
docs/manuscripts/connes-weil-rh-proof-draft.md:69
docs/audits/source-reread-v0.2.md:47
```

Thus a CCM25 finite-prime atom is not an arbitrary natural number. It is a
prime-power evaluation point built from `(p,m)`.

Lean replacement consequence:

```text
finitePrimeAtomVisible : Nat -> TestFunction -> Prop
```

should not remain the only typed witness. A later Lean pass should introduce a
source index type or a predicate such as:

```text
SourcePrimePowerIndex n
```

and require visibility to factor through it:

```text
finitePrimeAtomVisible n F_g -> SourcePrimePowerIndex n.
```

Failure blocked:

```text
a non-prime-power natural number can enter the finite-prime sum.
```

## Lemma 2. Global Support Is The Full Source Support

Statement:

```text
SourceGlobalPrimePowerSupport(F_g):
  globalPrimeIndexSet contains exactly the source prime-power atoms of F_g
  used by the global Psi finite-prime sum.
```

Proof.

The global sign spine is:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

The source reread records the finite-prime term and the sign pattern at:

```text
docs/audits/source-reread-v0.2.md:47
docs/manuscripts/connes-weil-rh-proof-draft.md:66-69
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md
```

The route currently asks only for:

```text
GlobalPrimeIndexCoverageStatement W F_g.
```

Evidence:

```text
ConnesWeilRH/Basic.lean:77-80
ConnesWeilRH/Route/AdmissibleWindow.lean:49-54
```

Coverage is necessary but not enough. The replacement theorem should identify:

```text
globalPrimeIndexSet = source support of W_p(F_g).
```

or an equivalent pair of inclusions with source hypotheses:

```text
visible atom -> in globalPrimeIndexSet
in globalPrimeIndexSet -> source prime-power atom of F_g.
```

Failure blocked:

```text
the route can add irrelevant finite-prime indices that later carry route-local
coefficients.
```

## Lemma 3. Restricted Support Is The Lambda Cut

Statement:

```text
SourceRestrictedPrimePowerSupport(lambda,F_g):
  restrictedPrimeIndexSet lambda is the source prime-power support of F_g
  cut by the CCM25 condition 1 < n <= lambda^2.
```

Proof.

The restricted source formula uses:

```text
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002
docs/audits/source-reread-v0.2.md:48
docs/proofs/ccm25-restricted-qwlambda-window-discharge.md:191-236
```

Therefore `restrictedPrimeIndexSet lambda` must be the lambda cut of the
source prime-power support, not a separate route-local finite set.

The fixed-S admissibility condition supplies the bridge from source visibility
to the restricted formula:

```text
S contains every finite prime visible to F_g.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
```

Lean replacement consequence:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
```

should be strengthened by a source equality or two-sided characterization:

```text
n in restrictedPrimeIndexSet lambda
  iff
SourcePrimePowerIndex n
  and
VisiblePrimePowerAtom n F_g
  and
1 < n
  and
n <= lambda^2.
```

Failure blocked:

```text
the restricted read-off can pass with a finite set that covers visible atoms
but does not equal the source lambda-window sum.
```

## Lemma 4. Weight Is Source Lambda

Statement:

```text
SourceVonMangoldtWeight(n):
  vonMangoldtWeight n is the CCM25 arithmetic weight Lambda(n).
```

Proof.

The restricted formula writes:

```text
Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:997-1001
docs/manuscripts/connes-weil-rh-proof-draft.md:1017-1019
```

The sign belongs to the surrounding restricted formula:

```text
-sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

So the local weight theorem should identify only the coefficient:

```text
vonMangoldtWeight n = Lambda(n).
```

It should not absorb the leading minus sign into the weight.

Failure blocked:

```text
the proof can hide a sign correction or scale factor inside
vonMangoldtWeight.
```

## Lemma 5. Pairing Is The Source Operator Pairing

Statement:

```text
SourcePrimePowerPairing(n,g):
  primePowerPairing n g g is the CCM25 source pairing <g|T(n)g>.
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
docs/manuscripts/connes-weil-rh-proof-draft.md:999-1001
docs/audits/source-reread-v0.2.md:48
```

The route must use the same source convolution square:

```text
F_g=g^* * g.
```

Evidence:

```text
docs/proofs/source-test-convolution-compatibility.md
```

Thus the pairing theorem must consume the common-test bridge. Otherwise the
finite-prime term can use the correct arithmetic weight on the wrong test
function.

Failure blocked:

```text
the finite-prime sum can pair Lambda(n) with a route-local bilinear form.
```

## Lemma 6. Term Normalization Is Pointwise

Statement:

```text
SourceFinitePrimeTermNormalization(n,g):
  finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>
  for each source prime-power index n.
```

Proof.

Combine Lemma 4 and Lemma 5:

```text
finitePrimeTerm n (g^* * g)
  =
vonMangoldtWeight n * primePowerPairing n g g
  =
Lambda(n)<g|T(n)g>.
```

Evidence:

```text
ConnesWeilRH/Basic.lean:86-90
ConnesWeilRH/Route/AdmissibleWindow.lean:64-68
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:243-270
```

The equality must be pointwise in `n`. A sum-level equality alone would not
prevent cancellation errors between a wrong coefficient and a wrong pairing.

Failure blocked:

```text
the restricted sum can match numerically while its individual source atoms do
not match CCM25.
```

## Combined Result

The six lemmas give:

```text
CCM25FinitePrimeIndexNormalization(lambda,g):
  SourceGlobalPrimePowerSupport F_g
  SourceRestrictedPrimePowerSupport lambda F_g
  for every n in the source support:
    SourcePrimePowerIndex n
    SourceVonMangoldtWeight n
    SourcePrimePowerPairing n g
    SourceFinitePrimeTermNormalization n g
```

This result strengthens the current finite-prime proof package:

```text
CCM25FinitePrimeSupportPairingDischarge(lambda,g)
```

by naming the source definitions behind its three route-facing outputs.

## Formalization Consequence

A later Lean pass should avoid defining finite-prime data as unrelated fields:

```text
globalPrimeIndexSet : Finset Nat
restrictedPrimeIndexSet : Real -> Finset Nat
finitePrimeAtomVisible : Nat -> TestFunction -> Prop
finitePrimeTerm : Nat -> TestFunction -> Real
primePowerPairing : Nat -> TestFunction -> TestFunction -> Real
vonMangoldtWeight : Nat -> Real
```

The replacement layer should expose a source-backed package with fields or
theorems shaped like:

```text
sourcePrimePowerIndex
sourceGlobalPrimeSupport_eq_Wp_support
sourceRestrictedPrimeSupport_eq_lambda_cut
sourceVonMangoldtWeight_eq_Lambda
sourcePrimePowerPairing_eq_Tn_pairing
sourceFinitePrimeTerm_eq_weight_mul_pairing
```

Then the existing route lemmas can consume the package to produce:

```text
GlobalPrimeIndexCoverageStatement
RestrictedPrimeIndexCoverageStatement
FinitePrimeTermNormalizationStatement
```

without treating these statements as primitive assumptions.

## Remaining Boundary

| task | reason |
|---|---|
| define the source prime-power index type or predicate | `Nat` alone does not encode prime-power status |
| formalize the lambda cut `1 < n <= lambda^2` | current restricted coverage does not expose the cut |
| import or define the CCM25 von Mangoldt weight | current `vonMangoldtWeight` is symbolic |
| import or define the CCM25 `T(n)` pairing | current `primePowerPairing` is symbolic |
| prove pointwise term normalization | sum-level matching is too weak for certification |

This package does not prove RH. It removes one finite-prime ambiguity: the
restricted CCM25 sum must use the source prime-power indices, the source
lambda cut, the source von Mangoldt weight, and the source operator pairing.
