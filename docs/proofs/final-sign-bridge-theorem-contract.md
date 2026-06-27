# Final Sign Bridge Theorem Contract

Status: theorem contract for the final CCM25-to-CC20 sign bridge gate.

This file converts:

```text
docs/proofs/final-sign-bridge-spine-discharge.md
```

from a proof-package spine into precise theorem targets for a future Lean pass
or accepted source import. It does not formalize CCM25 or CC20 sign
normalizations. It fixes the statements that must be proved, imported, or
rejected before route positivity can feed CC20 Proposition C.1.

## Evidence Lock

| item | evidence |
|---|---|
| CCM25 `QW`, `Psi`, finite-prime, archimedean, and pole source range | `mc2arXiv.tex:445-470`; `docs/audits/source-reread-v0.2.md:47` |
| restricted CCM25 sign check | `mc2arXiv.tex:530-540`; `docs/audits/source-reread-v0.2.md:48` |
| CC20 Proposition C.1 inequality input | `weil-compo.tex:2075-2078`; `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:45` |
| CC20 sign normalization source range | `weil-compo.tex:2131-2165`; `docs/audits/source-reread-v0.2.md:54` |
| manuscript sign map | `docs/manuscripts/connes-weil-rh-proof-draft.md:66-69,971-985,1013-1021,1118-1126,1349-1357` |
| existing sign bridge package | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` |
| final sign spine package | `docs/proofs/final-sign-bridge-spine-discharge.md` |
| finite-prime theorem contract | `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md` |
| formal-gate consistency audit | `docs/audits/formal-gate-spine-consistency-audit.md:195-255,305-316` |

The official source package URLs already recorded by the sign-bridge package
are:

```text
https://arxiv.org/e-print/2511.22755
https://arxiv.org/e-print/2006.13771
```

This contract relies on the project source audit for exact source-file ranges.

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

## Objects Fixed Before Any Inequality

For a fixed source-backed test:

```text
g       common half-density test
F_g     source convolution square g^* * g
QW      CCM25 Weil quadratic form
Psi     CCM25 source distribution
sum_v   CC20 local Weil sum used by Proposition C.1
```

the sign theorem must prove:

```text
QW(g,g) = - sum_v W_v(F_g)
```

before it derives:

```text
QW(g,g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

Blocked shortcut:

```text
fullWeilPositivity : Prop
```

as the final CC20 input.

## Contract Theorem 1. Common Source Test

Target:

```text
SourceQWUsesCommonTest:
  QW(g,g) = Psi(F_g)
```

with:

```text
F_g = g^* * g.
```

Meaning:

The CCM25 diagonal form and the CC20 local Weil sum must use the same source
test. The route cannot prove nonnegativity for one test and feed CC20 a local
Weil sum for another.

Evidence used:

```text
mc2arXiv.tex:464-467
docs/manuscripts/connes-weil-rh-proof-draft.md:66,973
docs/proofs/source-test-convolution-compatibility.md
docs/proofs/final-sign-bridge-spine-discharge.md:83-121
```

Blocked shortcut:

```text
QW(g,g) >= 0
```

with no theorem identifying the `F_g` consumed by `Psi` and CC20.

## Contract Theorem 2. Psi Sign Expansion

Target:

```text
SourcePsiSignExpansion:
  Psi(F_g)
    =
  W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g).
```

The theorem must keep three source legs visible:

```text
SourcePoleTermInPsi
SourceArchimedeanTermInPsi
SourceFinitePrimeTermsInPsi
```

Meaning:

The sign split in `Psi` is source data. It cannot be hidden in an opaque
distribution equality because the archimedean and finite-prime signs can fail
independently.

Evidence used:

```text
mc2arXiv.tex:465-470
docs/manuscripts/connes-weil-rh-proof-draft.md:68-69,975-985,1118-1126
docs/proofs/ccm25-qw-psi-definition-sign-discharge.md:140-186
docs/proofs/final-sign-bridge-spine-discharge.md:124-152
```

Blocked shortcut:

```text
PsiSignStatement : Prop
```

unless it projects to the three source legs above.

## Contract Theorem 3. Archimedean Sign Bridge

Target:

```text
SourceArchimedeanSignBridge:
  W_R(F_g) = - W_infty(F_g)
```

and therefore:

```text
-W_R(F_g) = W_infty(F_g)
```

under the CC20 `u_infty` and `qd u` convention.

Meaning:

The archimedean sign bridge consumes both the CCM25 relation and the CC20
source sign convention. Positivity of the route trace cannot determine this
sign by itself.

Evidence used:

```text
mc2arXiv.tex:448-455
weil-compo.tex:2131-2165
docs/manuscripts/connes-weil-rh-proof-draft.md:1017,1349-1354
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:187-235
docs/proofs/final-sign-bridge-spine-discharge.md:155-183
```

Blocked shortcut:

```text
archimedeanTermMatches : Prop
```

with no `W_R=-W_infty` theorem and no CC20 sign convention input.

## Contract Theorem 4. Finite-Prime Sign Ownership

Target:

```text
SourceFinitePrimeSignOwnedByFormula:
  finitePrimeTerm(n,F_g) = Lambda(n) * <g|T(n)g>
```

and:

```text
Psi finite-prime leg = - sum_p W_p(F_g)
QW_lambda finite-prime leg =
  - sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Meaning:

The local finite-prime atom keeps the source positive sign. The surrounding
`Psi` or `QW_lambda` formula owns the subtraction. The final bridge must not
pass because a local atom absorbed the minus sign.

Evidence used:

```text
mc2arXiv.tex:445-470,530-540
docs/manuscripts/connes-weil-rh-proof-draft.md:1017-1019
docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md
docs/proofs/final-sign-bridge-spine-discharge.md:184-212
```

Blocked shortcut:

```text
finitePrimeTerm(n,F_g) = - Lambda(n) * <g|T(n)g>
```

or any equivalent sign absorption into `Lambda`, `<g|T(n)g>`, or
`finitePrimeTerm`.

## Contract Theorem 5. Pole Sign In The CC20 Local Sum

Target:

```text
SourcePoleSignInCC20LocalSum:
  sum_v W_v(F_g)
    =
  W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g).
```

Consequent equality:

```text
-sum_v W_v(F_g)
  =
W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g).
```

Meaning:

The source pole functional `W_(0,2)` appears with plus sign in `Psi` and with
minus sign inside the CC20 local Weil sum. The route's separate pole ledger
does not redefine or remove this source pole term.

Evidence used:

```text
mc2arXiv.tex:469-470,533-535
docs/manuscripts/connes-weil-rh-proof-draft.md:67,977,1004-1011,1020-1021
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:244-297
docs/proofs/final-sign-bridge-spine-discharge.md:214-247
```

Blocked shortcut:

```text
tripleVanishing kills all pole terms
```

if that sentence erases the source `W_(0,2)` term rather than the separate
route quotient ledger.

## Contract Theorem 6. QW Equals Negative CC20 Weil Sum

Target:

```text
SourceQWEqualsNegCC20WeilSum:
  QW(g,g) = - sum_v W_v(F_g).
```

Required proof chain:

```text
QW(g,g)
  =
Psi(F_g)
  =
W_(0,2)(F_g) - W_R(F_g) - sum_p W_p(F_g)
  =
-sum_v W_v(F_g).
```

Meaning:

The equality must be a theorem produced from common-test, `Psi`, archimedean,
finite-prime, and pole sign targets. The final route cannot store it as an
opaque proposition without the source legs visible.

Evidence used:

```text
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:61-91,344-361
docs/proofs/final-sign-bridge-spine-discharge.md:252-283
docs/audits/source-object-definition-ledger.md:93-108
```

Blocked shortcut:

```text
qW_sign_bridge : Prop
```

unless it projects to the equality above and its source-leg proof chain.

## Contract Theorem 7. Inequality Direction

Target:

```text
SourceQWNonnegativeToCC20Nonpositive:
  QW(g,g) >= 0
  -> sum_v W_v(F_g) <= 0.
```

Required derivation:

```text
QW(g,g) = -sum_v W_v(F_g)
QW(g,g) >= 0
  ->
-sum_v W_v(F_g) >= 0
  ->
sum_v W_v(F_g) <= 0.
```

Meaning:

CC20 Proposition C.1 consumes the nonpositivity of the local Weil sum. It does
not consume `QW(g,g) >= 0` directly.

Evidence used:

```text
weil-compo.tex:2075-2078
docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md:353-396
docs/proofs/cc20-rh-exit-object-normalization-discharge.md:261-288
docs/proofs/final-sign-bridge-spine-discharge.md:258-295
```

Blocked shortcut:

```text
QW(g,g) >= 0
```

as the CC20 Proposition C.1 hypothesis.

## Combined Contract

The formal/import target for this gate is:

```text
FinalSignBridgeContract(g):
  SourceQWUsesCommonTest(g)
  SourcePsiSignExpansion(F_g)
  SourceArchimedeanSignBridge(F_g)
  SourceFinitePrimeSignOwnedByFormula(g)
  SourcePoleSignInCC20LocalSum(F_g)
  SourceQWEqualsNegCC20WeilSum(g)
  SourceQWNonnegativeToCC20Nonpositive(g)
```

Projection target:

```text
FinalSignBridgeContract(g)
  ->
FinalSignBridgeSpine(g).
```

Route consumption target:

```text
FinalSignBridgeContract(g)
  ->
route QW nonnegativity may feed CC20 Proposition C.1.
```

only through:

```text
QW(g,g)=Psi(F_g)
  -> Psi source sign expansion
  -> archimedean sign bridge
  -> finite-prime sign ownership
  -> pole sign in CC20 local sum
  -> QW(g,g)=-sum_v W_v(F_g)
  -> QW(g,g)>=0 implies sum_v W_v(F_g)<=0.
```

## Import Acceptance Checklist

A source import can discharge this contract only if it supplies these items:

| item | required evidence |
|---|---|
| common test | `QW(g,g)=Psi(F_g)` with the same `F_g` consumed by CC20 |
| `Psi` expansion | visible pole, archimedean, and finite-prime source legs |
| archimedean sign | `W_R=-W_infty` plus CC20 sign convention |
| finite-prime sign | local atoms remain positive; formula owns the minus sign |
| pole sign | source `W_(0,2)` appears with the CC20 local-sum sign |
| sign equality | theorem `QW(g,g)=-sum_v W_v(F_g)` |
| inequality direction | theorem `QW(g,g)>=0 -> sum_v W_v(F_g)<=0` |

If an import supplies only a positivity statement, it fails this contract.

## Lean Interface Consequence

A later Lean interface should define a structure with fields equivalent to the
combined contract. The compact current fields:

```text
fullWeilPositivity
qW_sign_bridge
sourceRH_to_mathlibRH
```

should not blur the sign bridge. The final-exit package should consume:

```text
SourceQWEqualsNegCC20WeilSum
SourceQWNonnegativeToCC20Nonpositive
```

before it invokes the CC20 finite-vanishing criterion.

The first Lean pass may keep theorem bodies as source-interface assumptions.
It must still expose the names above so that `#print axioms` shows exactly
which sign source theorem contracts the final route consumes.

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove the CCM25-to-CC20 sign theorem? | no |
| Does it specify the theorem shape needed to discharge the final sign gate? | yes |
| Does it block wrong-test sign transfer? | yes |
| Does it block finite-prime sign absorption? | yes |
| Does it block route pole ledger collapse into source `W_(0,2)`? | yes |
| Does it force equality before inequality direction? | yes |
| Can a later Lean/source-import pass use this as a checklist? | yes |

The final sign gate is now stated as a theorem contract. The next work is to
commit the three contract batch or continue with the RH definition bridge and
source-definition contracts before the next signed milestone.
