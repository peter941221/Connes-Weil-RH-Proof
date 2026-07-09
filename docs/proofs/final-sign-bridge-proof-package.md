# Final Sign Bridge Proof Package

Status: route-evidence proof package for the final CCM25-to-CC20 sign bridge.

This package proves the project-level target stated in:

```text
docs/proofs/final-sign-bridge-theorem-contract.md
```

It strengthens and reuses:

```text
docs/proofs/final-sign-bridge-spine-discharge.md
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md
```

It is not a CCM25 or CC20 accepted source import. It is not a Lean theorem. It
does not prove Proposition C.1, the RH definition bridge, or RH.

## Result

Good result:

```text
FinalSignBridgeContract is closed at route-evidence level.
```

Boundary:

```text
Accepted source-import status remains open.
Lean proof status remains open.
CC20 Proposition C.1 remains an imported final-exit theorem.
The RH proof is not complete.
```

## Target

For the common source test:

```text
F_g = g^* * g,
```

prove:

```text
QW(g,g) = - sum_v W_v(F_g),
```

and therefore:

```text
QW(g,g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

The proof must keep the common-test, pole, archimedean, finite-prime, and
inequality-direction legs visible.

## Evidence Boundary

| claim | evidence |
|---|---|
| common test `QW(g,g)=Psi(F_g)` | `docs/proofs/source-test-convolution-compatibility.md`; `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` |
| `Psi` sign expansion | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`; `docs/proofs/final-sign-bridge-spine-discharge.md` |
| archimedean sign bridge `W_R=-W_infty` | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md`; `docs/proofs/final-sign-bridge-spine-discharge.md` |
| finite-prime sign ownership | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`; `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md` |
| pole sign in the CC20 local sum | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md`; `docs/proofs/final-sign-bridge-spine-discharge.md` |
| inequality direction | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:344-396`; `docs/proofs/final-sign-bridge-theorem-contract.md` |

## Proof Skeleton

```text
QW(g,g)
        |
        v
Psi(F_g)
        |
        v
W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g)
        |
        v
- sum_v W_v(F_g)
        |
        v
QW(g,g) >= 0 -> sum_v W_v(F_g) <= 0
```

## Lemma 1. QW Uses The Common Source Test

Statement:

```text
SourceQWUsesCommonTest(g,F_g):
  F_g = g^* * g
  ->
  QW(g,g) = Psi(F_g).
```

Proof.

The common-test package identifies the source square:

```text
F_g = g^* * g.
```

The CCM25 definition-sign package records the source definition:

```text
QW(f,g) = Psi(f^* * g).
```

Therefore the diagonal value is:

```text
QW(g,g) = Psi(F_g).
```

Output:

```text
same_source_test
same_convolution_square
no_wrong_test_transfer
```

## Lemma 2. Psi Has The Source Sign Expansion

Statement:

```text
SourcePsiSignExpansion(F_g):
  Psi(F_g)
    =
  W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g).
```

Proof.

The CCM25 definition-sign package separates the pole, archimedean, and
finite-prime legs of `Psi`. The final sign spine records the same order and
keeps each sign visible.

The pole leg enters with plus sign:

```text
W_(0,2)(F_g).
```

The archimedean and finite-prime legs enter with minus sign:

```text
- W_R(F_g) - sum_p W_p(F_g).
```

No local finite-prime atom absorbs that minus sign.

## Lemma 3. Archimedean And Pole Signs Match CC20

Statement:

```text
SourceArchimedeanAndPoleSignBridge(F_g):
  W_R(F_g) = - W_infty(F_g)
  and
  sum_v W_v(F_g)
    =
  W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g).
```

Proof.

The sign bridge package identifies the CC20 local Weil sum convention:

```text
sum_v W_v(F_g)
  =
W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g).
```

The archimedean bridge uses the CCM25 relation:

```text
W_R = - W_infty.
```

The route pole ledger is a separate quotient ledger. It does not erase the
source pole term `W_(0,2)` inside the local Weil sum.

## Lemma 4. QW Equals The Negative CC20 Weil Sum

Statement:

```text
SourceQWEqualsNegCC20WeilSum(g,F_g):
  QW(g,g) = - sum_v W_v(F_g).
```

Proof.

Combine Lemmas 1 and 2:

```text
QW(g,g)
  =
W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g).
```

Use Lemma 3:

```text
sum_v W_v(F_g)
  =
W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g).
```

Multiplying the second equality by `-1` gives:

```text
-sum_v W_v(F_g)
  =
W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g).
```

Therefore:

```text
QW(g,g) = - sum_v W_v(F_g).
```

## Lemma 5. Inequality Direction

Statement:

```text
SourceQWNonnegativeToCC20Nonpositive(g,F_g):
  QW(g,g) >= 0
  ->
  sum_v W_v(F_g) <= 0.
```

Proof.

By Lemma 4:

```text
QW(g,g) = - sum_v W_v(F_g).
```

If:

```text
QW(g,g) >= 0,
```

then:

```text
-sum_v W_v(F_g) >= 0.
```

Multiplying by `-1` gives:

```text
sum_v W_v(F_g) <= 0.
```

This is the CC20 Proposition C.1 inequality direction. The route does not feed
`QW(g,g) >= 0` to CC20 directly.

## Theorem. Final Sign Bridge

Statement:

```text
FinalSignBridgeContract(g,F_g):
  SourceQWUsesCommonTest
  + SourcePsiSignExpansion
  + SourceArchimedeanSignBridge
  + SourceFinitePrimeSignOwnedByFormula
  + SourcePoleSignInCC20LocalSum
  + SourceQWEqualsNegCC20WeilSum
  + SourceQWNonnegativeToCC20Nonpositive.
```

Proof.

Combine Lemmas 1 through 5 with the pointwise finite-prime sign ownership from
the finite-prime normalization package.

The proof uses:

```text
common source square F_g,
CCM25 Psi expansion,
CC20 local Weil sum convention,
finite-prime pointwise sign ownership,
source pole sign,
explicit multiplication by -1.
```

It does not use:

```text
route-local fullWeilPositivity as a black box,
finite-prime sign absorption,
triple vanishing to erase the source pole term,
or RH.
```

## Output To The Route

This package supplies, at route-evidence level:

```text
FinalSignBridgeContract
SourceQWEqualsNegCC20WeilSum
SourceQWNonnegativeToCC20Nonpositive
CC20WeilInequality_from_QWNonnegativity
```

It does not supply:

```text
accepted_source_import_discharge
Lean_theorem
CC20PropositionC1Proof
RHDefinitionBridge
RiemannHypothesis
```

## Current Status

```text
Common source test:                     proved at route-evidence level
Psi source sign expansion:              proved at route-evidence level
Archimedean and pole sign bridge:       proved at route-evidence level
Finite-prime sign ownership:            route-evidence available
QW = negative CC20 local Weil sum:       proved at route-evidence level
Inequality direction:                   proved at route-evidence level

Accepted source-import status:          open
Lean proof status:                      open
CC20 Proposition C.1 import:            open
RH definition bridge:                   open
RH proof:                               not complete
```
