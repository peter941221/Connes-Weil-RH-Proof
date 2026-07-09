# Final Sign Bridge Spine Discharge

Status: proof package for the final CCM25-to-CC20 sign bridge spine.

This package attacks the fourth remaining formal gate from:

```text
docs/audits/source-interface-discharge-completion-audit.md
```

The gate is:

```text
final sign bridge
```

The package does not formalize CCM25 or CC20 signs in Lean. It records the
theorem chain that a later source-import or Lean pass must expose before route
positivity can feed CC20 Proposition C.1.

The stronger formal/import theorem contract is:

```text
docs/proofs/final-sign-bridge-theorem-contract.md
```

It names the theorem targets that must replace this proof-package spine before
the final sign bridge gate can count as discharged.

## Evidence Boundary

| object | evidence |
|---|---|
| existing sign bridge package | `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md` |
| CCM25 global definition-sign package | `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md` |
| restricted sign check | `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md` |
| finite-prime sign owner | `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md` |
| CC20 trace/sign object package | `docs/proofs/cc20-trace-object-normalization-discharge.md` |
| CC20 final exit package | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md` |
| CC20 RH-exit object package | `docs/proofs/cc20-rh-exit-object-normalization-discharge.md` |
| source definition spine | `docs/proofs/source-object-definition-spine-discharge.md` |
| source reread audit | `docs/audits/source-reread-v0.2.md:47,54` |

## Target Statement

The final sign bridge target is:

```text
FinalSignBridgeSpine(g):
  QW(g,g) is the CCM25 source form on F_g;
  Psi(F_g) expands as W_(0,2)(F_g)-W_R(F_g)-sum_p W_p(F_g);
  W_R=-W_infty is the same archimedean convention used by CC20;
  the local finite-prime atoms keep positive Lambda(n)<g|T(n)g> sign;
  the pole term is subtracted inside the CC20 local Weil sum;
  therefore QW(g,g) = - sum_v W_v(F_g);
  therefore QW(g,g) >= 0 implies sum_v W_v(F_g) <= 0.
```

The dependency order is:

```text
source test g and F_g=g^* * g
      |
      v
QW(g,g)=Psi(F_g)
      |
      v
Psi(F_g)=W_(0,2)(F_g)-W_R(F_g)-sum_p W_p(F_g)
      |
      v
CCM25 W_R=-W_infty plus CC20 archimedean convention
      |
      v
finite-prime sign owned by Psi/QW, not by each atom
      |
      v
CC20 local Weil sum
      |
      v
QW(g,g) = - sum_v W_v(F_g)
      |
      v
QW(g,g) >= 0 -> sum_v W_v(F_g) <= 0
```

The key rule is:

```text
the inequality direction is a theorem output, not a convention.
```

## Lemma 1. QW Uses The Same Source Test As CC20

Statement:

```text
SignBridgeSourceTest(g):
  the CCM25 diagonal form QW(g,g) and the CC20 local Weil sum both evaluate
  the same source square F_g.
```

Proof.

The source-definition spine fixes:

```text
F_g = g^* * g.
```

The CCM25 definition gives:

```text
QW(g,g) = Psi(F_g).
```

The CC20 finite-vanishing criterion uses:

```text
sum_v W_v(g * bar(g)^sharp).
```

The half-density and convolution packages identify these as the same source
test. The sign bridge must consume that identification before it compares
inequalities.

Failure blocked:

```text
QW(g,g) is nonnegative on one test while CC20 Proposition C.1 receives a
different local Weil sum.
```

## Lemma 2. Psi Expansion Owns The Global Sign Pattern

Statement:

```text
SignBridgePsiExpansion(F_g):
  Psi(F_g)=W_(0,2)(F_g)-W_R(F_g)-sum_p W_p(F_g).
```

Proof.

The CCM25 global sign package identifies `Psi` and its three signs. The pole
functional enters with plus sign. The archimedean `W_R` term and finite-prime
terms enter with minus signs.

The formal theorem should expose these components separately:

```text
SourcePoleTermInPsi
SourceArchimedeanTermInPsi
SourceFinitePrimeTermsInPsi
SourcePsiSignSplit.
```

Failure blocked:

```text
a route-local Psi has the same name but a different pole, archimedean, or
finite-prime sign.
```

## Lemma 3. Archimedean Sign Bridge Is Separate

Statement:

```text
SignBridgeArchimedean(F_g):
  the rewrite -W_R(F_g)=W_infty(F_g) uses the CCM25 relation W_R=-W_infty
  and the CC20 archimedean sign convention.
```

Proof.

The CCM25 sign package supplies:

```text
W_R=-W_infty.
```

The CC20 trace/sign package supplies the `u_infty` and quantized differential
sign convention. The final bridge must consume both. It cannot infer the
archimedean sign only from the positivity of the route trace.

Failure blocked:

```text
the archimedean term is flipped when passing from CCM25 notation to CC20
notation.
```

## Lemma 4. Finite-Prime Sign Belongs To The Formula

Statement:

```text
SignBridgeFinitePrimeAtoms(n,g):
  local finite-prime atoms are Lambda(n)<g|T(n)g>; the negative sign belongs
  to Psi or QW_lambda.
```

Proof.

The finite-prime normalization spine proves pointwise atom normalization:

```text
finitePrimeTerm n F_g = Lambda(n)<g|T(n)g>.
```

The global `Psi` formula and restricted `QW_lambda` formula place a minus sign
in front of the finite-prime sum. A formal bridge must keep these layers
separate. If the local atom absorbs the sign, the final CC20 inequality can
look correct while the source finite-prime term is wrong.

Failure blocked:

```text
the final sign bridge passes because the local finite-prime atom already has
the wrong sign.
```

## Lemma 5. The Pole Term Has The CC20 Sum Sign

Statement:

```text
SignBridgePoleTerm(F_g):
  W_(0,2)(F_g) appears with plus sign in Psi and therefore with minus sign
  inside the CC20 local Weil sum when QW=-sum_v W_v.
```

Proof.

The existing sign bridge package identifies:

```text
sum_v W_v(F_g) = W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g).
```

Then:

```text
-sum_v W_v(F_g)
  =
W_(0,2)(F_g)-W_R(F_g)-sum_p W_p(F_g)
  =
Psi(F_g).
```

The route pole ledger remains separate. Triple vanishing kills route pole jets;
it does not redefine the source `W_(0,2)` functional.

Failure blocked:

```text
the proof kills a route pole channel and silently removes the source pole
term from the CC20 local Weil sum.
```

## Lemma 6. Equality Comes Before Inequality Direction

Statement:

```text
SignBridgeInequalityDirection(g):
  QW(g,g) >= 0 implies the CC20 inequality only after the equality
  QW(g,g) = -sum_v W_v(F_g) has been proved.
```

Proof.

The formal order is:

```text
QW(g,g) = -sum_v W_v(F_g)
QW(g,g) >= 0
```

then:

```text
-sum_v W_v(F_g) >= 0.
```

Multiplying by `-1` gives:

```text
sum_v W_v(F_g) <= 0.
```

The inequality direction must be stored as an explicit theorem or derived from
the explicit equality. A final certificate must not accept:

```text
fullWeilPositivity : Prop
```

as the CC20 Proposition C.1 input.

Failure blocked:

```text
QW(g,g) >= 0 is passed to CC20 as if CC20 asked for a nonnegative condition.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
FinalSignBridgeSpine(g)
```

with these Lean-facing theorem targets:

```text
SourceQWUsesCommonTest
SourcePsiSignExpansion
SourceArchimedeanSignBridge
SourceFinitePrimeSignOwnedByFormula
SourcePoleSignInCC20LocalSum
SourceQWEqualsNegCC20WeilSum
SourceQWNonnegativeToCC20Nonpositive
```

This strengthens the older package:

```text
QWToCC20WeilInequalitySignBridge(g)
```

The older package proves the sign bridge at proof-package level. This package
fixes the theorem targets a Lean or source-import pass must expose.

## Formalization Consequence

A later Lean interface should not expose only:

```text
fullWeilPositivity : Prop
qW_sign_bridge : Prop
```

as final evidence.

It should expose a package shaped like:

```text
FinalSignBridge
  +-- QW(g,g)=Psi(F_g)
  +-- Psi(F_g)=W_(0,2)-W_R-sum_p W_p
  +-- W_R=-W_infty and CC20 sign compatibility
  +-- finite-prime atoms have positive local sign
  +-- CC20 sum_v convention
  +-- QW(g,g)=-sum_v W_v(F_g)
  +-- QW(g,g)>=0 -> sum_v W_v(F_g)<=0
```

Then the compact final-exit package can consume the derived CC20 inequality.

## Remaining Boundary

| task | reason |
|---|---|
| formalize or import CCM25 `QW` and `Psi` definitions | the current package cites source formulas |
| formalize or import the CC20 local Weil sum convention | `sum_v W_v` remains prose-level notation |
| formalize the archimedean sign bridge | `W_R=-W_infty` must match CC20 `u_infty` and `qd u` |
| keep finite-prime local signs separate from formula signs | the finite-prime atom must stay pointwise source-normalized |
| expose inequality-direction theorem in Lean | Proposition C.1 requires `sum_v W_v(F_g) <= 0` |

This package does not prove RH. It removes a final-exit loophole: route
nonnegativity becomes the CC20 nonpositivity input only through a named sign
equality and an explicit inequality-direction theorem.
