# CCM25 Finite-Prime Normalization Theorem Contract

Status: theorem contract for the CCM25 finite-prime normalization gate.

This file converts:

```text
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md
```

from a proof-package spine into precise theorem targets for a future Lean pass
or accepted source import. It does not formalize CCM25 arithmetic. It fixes the
statements that must be proved, imported, or rejected before the route can use
the finite-prime part of `QW`, `Psi`, or `QW_lambda`.

## Evidence Lock

| item | evidence |
|---|---|
| CCM25 finite-prime signs and global `Psi` | `mc2arXiv.tex:445-470`; `docs/audits/source-reread-v0.2.md:47` |
| restricted `QW_lambda` and prime-power pairing | `mc2arXiv.tex:530-540`; `docs/audits/source-reread-v0.2.md:48` |
| restricted displayed formula | `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1001` |
| finite-prime sign audit | `docs/manuscripts/connes-weil-rh-proof-draft.md:1013-1021` |
| fixed-S visible-prime side condition | `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057,1368-1374` |
| finite-prime support-pairing package | `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| finite-prime index package | `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md` |
| finite-prime spine package | `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` |
| formal-gate consistency audit | `docs/audits/formal-gate-spine-consistency-audit.md:166-215,304-315` |

This contract relies on the project source audit for CCM25 source-line anchors.
This pass did not add a new externally confirmed paper identity beyond those
existing source-file references.

## Boundary

This contract gives a stronger target than the current proof package:

```text
proof-package spine
  |
  v
formal/import theorem contract
```

It still gives weaker evidence than a completed proof:

```text
formal/import theorem contract
  |
  v
Lean theorem or accepted source theorem with audited hypotheses
```

The final RH route cannot treat this contract as discharge. A later phase must
replace each target below with a Lean theorem or an accepted imported theorem.

## Objects Fixed Before Any Sum

For fixed route data:

```text
lambda  restricted CCM25 parameter
g       common source test
F_g     source convolution square g^* * g
n       finite-prime source index
```

the finite-prime theorem must factor every route-visible index through a source
prime-power atom before it enters a global or restricted finite-prime sum.

The source formula to preserve is:

```text
QW_lambda(g,g)
  =
archimedean term
  + pole term
  - sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>
```

with:

```text
<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

Blocked shortcut:

```text
restrictedFinitePrimeSum_eq : Prop
```

as the only finite-prime theorem.

## Contract Theorem 1. Prime-Power Index Factorization

Target:

```text
SourcePrimePowerIndexFactorization:
  RouteFinitePrimeIndex(n,F_g)
  -> SourcePrimePowerIndex(n)
  -> SourcePrimePowerAtomVisible(n,F_g).
```

Equivalent target:

```text
RouteFinitePrimeIndex(n,F_g)
  ->
exists p m,
  p is prime
  and 1 <= m
  and n = p^m
  and the source finite-prime term reads F_g at n and n^(-1).
```

Meaning:

The route may use `Nat` as a carrier, but `Nat` alone does not encode
prime-power status. The theorem must prove that each index consumed by the
finite-prime formula comes from the CCM25 source prime-power support.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1001
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:126-171
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md:87-117
```

Blocked shortcut:

```text
n : Nat
```

with no source prime-power predicate.

## Contract Theorem 2. Global Support Is Source Support

Target:

```text
SourceGlobalPrimePowerSupport:
  n in globalPrimeIndexSet(F_g)
  <->
  SourcePrimePowerIndex(n)
    and SourcePrimePowerAtomVisible(n,F_g)
    and n contributes to the global finite-prime leg of Psi(F_g).
```

Meaning:

The global finite-prime support must be the CCM25 source support for the
finite-prime part of `Psi(F_g)`. A one-way coverage theorem is too weak for
certification because extra route-local atoms can enter the sum.

Evidence used:

```text
mc2arXiv.tex:445-470
docs/audits/source-reread-v0.2.md:47
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:179-229
docs/audits/source-object-definition-ledger.md:84
```

Blocked shortcut:

```text
GlobalPrimeIndexCoverageStatement W F_g
```

without a reverse source-support inclusion.

## Contract Theorem 3. Restricted Support Is The Lambda Cut

Target:

```text
SourceRestrictedPrimePowerSupport:
  n in restrictedPrimeIndexSet(lambda,F_g)
  <->
  n in globalPrimeIndexSet(F_g)
    and SourcePrimePowerIndex(n)
    and SourcePrimePowerAtomVisible(n,F_g)
    and 1 < n
    and n <= lambda^2.
```

Equivalent target:

```text
restrictedPrimeIndexSet(lambda,F_g)
  =
{ n in globalPrimeIndexSet(F_g) | 1 < n and n <= lambda^2 }.
```

Meaning:

The restricted finite-prime set must be the lambda-window cut of the same
source support used globally. It cannot be an independent finite set that only
covers visible atoms.

Evidence used:

```text
mc2arXiv.tex:530-540
docs/audits/source-reread-v0.2.md:48
docs/manuscripts/connes-weil-rh-proof-draft.md:997-1001
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:238-290
```

Blocked shortcut:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
```

without equality or two-sided characterization of the source lambda cut.

## Contract Theorem 4. Visibility Precedes The Lambda Cut

Target:

```text
SourceVisiblePrimePowerBeforeLambdaCut:
  n in restrictedPrimeIndexSet(lambda,F_g)
  ->
  SourcePrimePowerAtomVisible(n,F_g)
  and SourcePrimePowerIndex(n)
  and 1 < n
  and n <= lambda^2.
```

Separate route-side admissibility target:

```text
FixedSVisiblePrimeSetBeforeLimit:
  S contains every finite prime visible to F_g before the lambda limit.
```

Meaning:

Visibility comes from the support of `F_g=g^* * g`. The numeric lambda cut
then selects which visible source atoms enter `QW_lambda`. The cut must not
define visibility by itself.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
docs/manuscripts/connes-weil-rh-proof-draft.md:1368-1374
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md:177-222
```

Blocked shortcut:

```text
1 < n and n <= lambda^2
```

as the only restricted-support predicate.

## Contract Theorem 5. Von Mangoldt Weight Normalization

Target:

```text
SourceVonMangoldtWeightNormalization:
  SourcePrimePowerIndex(n)
  -> vonMangoldtWeight(n) = Lambda(n).
```

Meaning:

The finite-prime coefficient is the CCM25 source von Mangoldt weight. The
theorem must not hide a sign, scale factor, or route-local coefficient inside
`vonMangoldtWeight`.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:997-1019
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:309-343
docs/audits/source-object-definition-ledger.md:88
```

Blocked shortcut:

```text
someWeight(n)
```

with no proof that it is the source `Lambda(n)`.

## Contract Theorem 6. Prime-Power Pairing Normalization

Target:

```text
SourcePrimePowerPairingNormalization:
  SourcePrimePowerIndex(n)
  -> primePowerPairing(n,g,g)
       =
     <g|T(n)g>.
```

Source expansion target:

```text
<g|T(n)g>
  =
n^(-1/2)(F_g(n)+F_g(n^(-1))).
```

Meaning:

The pairing must use the same common source test and convolution square
consumed by CCM24, CCM25, and CC20. It cannot be a route-local bilinear form
with the same type.

Evidence used:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:999-1001
docs/audits/source-reread-v0.2.md:48
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:353-393
docs/audits/source-object-definition-ledger.md:89
```

Blocked shortcut:

```text
primePowerPairing : Nat -> TestFunction -> TestFunction -> Real
```

with no source `T(n)` bridge.

## Contract Theorem 7. Pointwise Term Normalization

Target:

```text
SourceFinitePrimeTermPointwiseNormalization:
  SourcePrimePowerIndex(n)
  -> SourcePrimePowerAtomVisible(n,F_g)
  -> finitePrimeTerm(n,F_g)
       =
     Lambda(n) * <g|T(n)g>.
```

Restricted form target:

```text
forall n in restrictedPrimeIndexSet(lambda,F_g),
  finitePrimeTerm(n,F_g)
    =
  Lambda(n) * <g|T(n)g>.
```

Meaning:

The pointwise theorem must hold before the global or restricted finite-prime
sum is formed. A sum equality cannot replace this theorem because cancellation
can hide wrong weights, pairings, or support atoms.

Evidence used:

```text
docs/proofs/ccm25-finite-prime-index-normalization-discharge.md:401-428
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md:267-308
formalization/source-object-interface-plan.md:213-219
formalization/source-object-interface-risk-audit.md:156-182
```

Blocked shortcut:

```text
sum finitePrimeTerm = sum Lambda(n)<g|T(n)g>
```

without pointwise equality for each source prime-power index.

## Contract Theorem 8. Formula Owns The Finite-Prime Sign

Target:

```text
SourceFinitePrimeFormulaOwnsSign:
  finitePrimeTerm(n,F_g) = Lambda(n) * <g|T(n)g>
  and the minus sign appears only in
    Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)
  and in
    QW_lambda finite-prime leg =
      - sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Meaning:

The local atom stays positive in the source normalization. The global or
restricted CCM25 formula owns the subtraction. The final CC20 sign bridge
depends on that split.

Evidence used:

```text
mc2arXiv.tex:445-470,530-540
docs/audits/source-reread-v0.2.md:47-48
docs/manuscripts/connes-weil-rh-proof-draft.md:1013-1021
docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md:312-344
```

Blocked shortcut:

```text
finitePrimeTerm(n,F_g) = - Lambda(n) * <g|T(n)g>
```

or any equivalent sign absorption into the local atom.

## Combined Contract

The formal/import target for this gate is:

```text
CCM25FinitePrimeNormalizationContract(lambda,g):
  SourcePrimePowerIndexFactorization(lambda,g)
  SourceGlobalPrimePowerSupport(g)
  SourceRestrictedPrimePowerSupport(lambda,g)
  SourceVisiblePrimePowerBeforeLambdaCut(lambda,g)
  FixedSVisiblePrimeSetBeforeLimit(lambda,g)
  SourceVonMangoldtWeightNormalization(lambda,g)
  SourcePrimePowerPairingNormalization(lambda,g)
  SourceFinitePrimeTermPointwiseNormalization(lambda,g)
  SourceFinitePrimeFormulaOwnsSign(lambda,g)
```

Projection target:

```text
CCM25FinitePrimeNormalizationContract(lambda,g)
  ->
CCM25FinitePrimeNormalizationSpine(lambda,g).
```

Route consumption target:

```text
CCM25FinitePrimeNormalizationContract(lambda,g)
  ->
the route may use the global and restricted finite-prime sums.
```

only through:

```text
source prime-power atom
  -> visibility in F_g
  -> global support
  -> restricted lambda cut
  -> Lambda(n)
  -> <g|T(n)g>
  -> pointwise term equality
  -> finite-prime sum.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies these items:

| item | required evidence |
|---|---|
| source index | prime-power status or equivalent `(p,m)` source index |
| global support | two-sided source characterization of global finite-prime support |
| restricted support | two-sided lambda-cut characterization `1 < n <= lambda^2` |
| visibility | support of `F_g`, separate from the numeric lambda cut |
| fixed-S side condition | `S` contains every finite prime visible to `F_g` before the lambda limit |
| weight | source `Lambda(n)` theorem |
| pairing | source `<g|T(n)g>` theorem using `F_g=g^* * g` |
| pointwise atom | `finitePrimeTerm(n,F_g)=Lambda(n)<g|T(n)g>` for each source atom |
| sign owner | minus sign stays in `Psi` or `QW_lambda`, not in the atom |

If an import supplies only a finite-prime sum equality, it fails this contract.

## Lean Interface Consequence

A later Lean interface should define a structure with fields equivalent to the
combined contract. The compact current fields:

```text
globalPrimeIndexSet
restrictedPrimeIndexSet
finitePrimeTerm
vonMangoldtWeight
primePowerPairing
```

should become projections from that structure. They should not remain primitive
source evidence.

The first Lean pass may keep theorem bodies as source-interface assumptions.
It must still expose the names above so that `#print axioms` shows exactly
which finite-prime source theorem contracts the final route consumes.

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove the CCM25 finite-prime theorem? | no |
| Does it specify the theorem shape needed to discharge the finite-prime gate? | yes |
| Does it block non-prime-power indices? | yes |
| Does it block independent restricted finite sets? | yes |
| Does it block sum-level cancellation hiding wrong atoms? | yes |
| Does it keep the finite-prime sign outside the local atom? | yes |
| Can a later Lean/source-import pass use this as a checklist? | yes |

The finite-prime gate is now stated as a theorem contract. The next work is to
write the final sign-bridge contract or to encode these contracts in the future
source-interface layer after Peter reopens Lean work.
