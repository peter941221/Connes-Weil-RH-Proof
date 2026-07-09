# QW To CC20 Weil Inequality Sign Bridge

Status: proof package for the final sign bridge between the CCM25 Weil form and
the CC20 positivity criterion.

This package attacks the remaining semantic risk in the final RH exit:

```text
route full positivity:
  QW(g,g) >= 0

CC20 Proposition C.1 hypothesis:
  sum_v W_v(g * bar(g)^sharp) <= 0
```

The route may pass from the first statement to the second only after it proves:

```text
QW(g,g) = - sum_v W_v(g * bar(g)^sharp).
```

## Evidence Boundary

Official source packages:

```text
https://arxiv.org/e-print/2511.22755
https://arxiv.org/e-print/2006.13771
```

Relevant source files:

```text
mc2arXiv.tex
weil-compo.tex
```

| claim | evidence |
|---|---|
| finite-prime term `W_p(F)` | `mc2arXiv.tex:445-447` |
| archimedean relation `W_R=-W_infty` | `mc2arXiv.tex:448-455` |
| `QW(f,g)=Psi(f^* * g)` | `mc2arXiv.tex:464-467` |
| `Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)` | `mc2arXiv.tex:465-470` |
| restricted form has `+W_infty`, pole term, and negative finite-prime sum | `mc2arXiv.tex:530-540` |
| CC20 criterion uses `sum_v W_v(g * bar(g)^sharp) <= 0` | `weil-compo.tex:2075-2078` |
| CC20 half-density/Mellin convention | `weil-compo.tex:2014-2030` |
| CC20 archimedean sign normalization | `weil-compo.tex:2131-2165` |
| route final-exit package requiring this sign bridge | `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md:230-297` |

## Target Statement

For the half-density test `g` and its source convolution square:

```text
F_g = g^* * g,
```

prove:

```text
QW(g,g)
  =
- sum_v W_v(F_g)
```

where:

```text
sum_v W_v(F_g)
  =
W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g)
```

under the CC20/CCM source convention used by Proposition C.1.

The bridge has this shape:

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
-[W_R(F_g) + sum_p W_p(F_g) - W_(0,2)(F_g)]
      |
      v
- sum_v W_v(F_g)
```

## Lemma 1. Source Test Agreement

Statement:

```text
QWSourceTest(g):
  QW(g,g) is evaluated on F_g=g^* * g.
```

Proof.

CCM25 defines the Weil form by polarization:

```text
QW(f,g)=Psi(f^* * g).
```

Evidence:

```text
mc2arXiv.tex:464-467
```

For the diagonal input `f=g`, the source test is:

```text
F_g = g^* * g.
```

The CC20 half-density package verifies that this is the same convolution square
used by the Mellin finite-vanishing convention:

```text
docs/proofs/cc20-trace-legality-mellin-discharge.md:293-341
```

Output:

```text
QW(g,g) = Psi(F_g).
```

## Lemma 2. CCM25 Global Sign Expansion

Statement:

```text
CCM25GlobalSignExpansion(F):
  Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F).
```

Proof.

CCM25 writes:

```text
Psi(F):= W_(0,2)(F) - W_R(F) - sum_p W_p(F).
```

Evidence:

```text
mc2arXiv.tex:465-470
```

It also writes the finite-prime distribution:

```text
W_p(F)=(log p) sum_(m>=1) p^(-m/2)(F(p^m)+F(p^(-m))).
```

Evidence:

```text
mc2arXiv.tex:445-447
```

Thus finite primes enter `Psi` with a negative sign. The proof may not rebuild
finite primes from a local even-trace shortcut.

Output:

```text
QW(g,g)
  =
W_(0,2)(F_g)-W_R(F_g)-sum_p W_p(F_g).
```

## Lemma 3. Archimedean Sign Compatibility

Statement:

```text
ArchimedeanSignCompatibility(F):
  the archimedean term in the CCM25 expansion matches the CC20 source
  archimedean convention.
```

Proof.

CCM25 records:

```text
W_R = - W_infty.
```

Evidence:

```text
mc2arXiv.tex:448-455
```

CC20 records the quantized-differential sign through the phase unitary and
the diagonal formula for `u^* qd u`:

```text
weil-compo.tex:2131-2165
```

Therefore:

```text
-W_R(F) = W_infty(F).
```

This is why the restricted formula displays the archimedean density with a
positive sign:

```text
int_R |hat f(t)|^2 (2 partial_t theta(t))/(2 pi) dt.
```

Evidence:

```text
mc2arXiv.tex:530-535
```

Output:

```text
archimedean sign in QW matches the CC20 source convention.
```

## Lemma 4. Pole Term Is Subtracted In The CC20 Sum

Statement:

```text
PoleSignForCC20Sum(F):
  the pole functional W_(0,2)(F) appears with plus sign in QW and therefore
  with minus sign inside sum_v W_v when QW=-sum_v W_v.
```

Proof.

CCM25 defines:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2).
```

Evidence:

```text
mc2arXiv.tex:469-470
```

The restricted formula displays the corresponding diagonal pole pairing:

```text
2 Re(hat f(i/2) overline{hat f(-i/2)}).
```

Evidence:

```text
mc2arXiv.tex:533-535
```

This pole functional belongs inside `QW` and `QW_lambda`. The route's
`PoleJetExtra` ledger is separate and gets killed by triple vanishing before
the final CC20 exit:

```text
docs/proofs/ccm25-restricted-read-off-discharge.md:316-358
```

Thus the source sum compatible with Proposition C.1 is:

```text
sum_v W_v(F)
  =
W_R(F) + sum_p W_p(F) - W_(0,2)(F).
```

Then:

```text
-sum_v W_v(F)
  =
W_(0,2)(F)-W_R(F)-sum_p W_p(F)
  =
Psi(F).
```

## Lemma 5. Restricted Formula Checks The Same Sign

Statement:

```text
RestrictedSignCheck(lambda,g):
  QW_lambda(g,g) restricts the same global sign convention.
```

Proof.

CCM25 states:

```text
QW_lambda(f,f)
  =
archimedean density
  + pole pairing
  - sum_(1<n<=lambda^2) Lambda(n)<f|T(n)f>.
```

Evidence:

```text
mc2arXiv.tex:530-540
```

The finite-prime source-discharge package identifies the local restricted
summand as:

```text
Lambda(n) * <g|T(n)g>
```

and leaves the negative sign to the surrounding `QW_lambda` formula:

```text
docs/proofs/ccm25-finite-prime-support-pairing-discharge.md:150-260
```

Therefore the restricted formula is not a separate convention. It is the
windowed version of:

```text
QW(g,g) = - sum_v W_v(F_g).
```

## Lemma 6. Inequality Direction

Statement:

```text
QWNonnegativeToCC20Inequality(g):
  QW(g,g) >= 0 implies sum_v W_v(F_g) <= 0.
```

Proof.

Combine Lemmas 1 through 4:

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

This is exactly the inequality in CC20 Proposition C.1:

```text
weil-compo.tex:2075-2078
```

## Integrated Sign Bridge

Combining Lemmas 1 through 6 gives:

```text
QWToCC20WeilInequalitySignBridge(g):
  QW(g,g) >= 0
    ->
  sum_v W_v(g * bar(g)^sharp) <= 0.
```

The dependency graph is:

```text
CCM25 QW(f,g)=Psi(f^* * g)
        |
        v
Psi(F)=W_(0,2)-W_R-sum_p W_p
        |
        v
CCM25 W_R=-W_infty and CC20 u_infty sign
        |
        v
QW(g,g) = - sum_v W_v(F_g)
        |
        v
CC20 Proposition C.1 inequality direction
```

## Formalization Consequence

The final Lean replacement for `FiniteVanishingCriterionPackage` should not
accept:

```text
fullWeilPositivity : Prop
```

as an opaque route-local proposition.

It should expose a bridge field with this shape:

```text
qW_to_cc20_inequality :
  QW_nonnegative_on_finite_vanishing_tests ->
  CC20_weil_inequality_on_F
```

or a proved equality:

```text
QW(g,g) = - sum_v W_v(F_g).
```

Without this bridge, a later proof could satisfy the Lean interface with the
wrong sign and still conclude RH from a proposition that is not CC20
Proposition C.1.

## Remaining Boundary

This package closes the sign bridge at source-interface proof-package level.
It leaves three stronger evidence tasks:

| task | reason |
|---|---|
| formalize the CCM25 definition of `QW` and `Psi` | this package cites source formulas |
| formalize the CC20 local Weil sum convention | the sum `sum_v W_v` still lives in prose notation |
| add a Lean-visible sign bridge before final certification | the current Lean package stores `fullWeilPositivity` as a symbolic proposition |

The route remains source-conditional until these sign statements are formalized
or imported as accepted theorem interfaces.
