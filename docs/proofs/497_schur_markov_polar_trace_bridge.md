# Proof 497: Schur--Markov polar trace bridge

Date: 2026-07-22

Status: the polar numerator and the route-ordered Gram endpoint now have an
exact ordinary-trace readback.  This is a reduction of Gate 3U to one
family-uniform signed estimate; it is not that estimate.

## 1. Result

```text
+-----------------------------------------------------+------------------+
| layer                                               | result           |
+-----------------------------------------------------+------------------+
| terminal polar factors, both multiplication orders  | exact inverses   |
| empty-suffix polar coordinate                       | Z_empty^2 = I    |
| complete forward/reverse polar similarities         | exact inverses   |
| forward Schur product                               | upper^-1 * F_S   |
| reverse Markov product                              | lower * R_S      |
| complete signed numerator                           | rho_S similarity |
| similarity trace cycle                              | legal S2 cycle   |
| left/right Gram ordering                            | adjoints         |
| absolute-trace readback                             | rho_S scaling    |
| family-uniform support--Sobolev estimate            | open             |
| Gate 3U                                             | open             |
+-----------------------------------------------------+------------------+
```

Here `S2` means Hilbert--Schmidt class.  The spaces in the trace cycle are
connected by the existing four physical boundary branches, not by a formal
infinite-dimensional cyclic permutation.

## 2. Polar similarities

Let

```text
Z_S     = Gamma_S^(-1/2),
L_S     = Z_S Gamma_S,
R_S     = Z_S.
```

Lean proves both ordered products

```text
R_S L_S = I,
L_S R_S = I.
```

The complete suffix products also retain the fixed empty polar coordinate:

```text
F_S = L_S Z_empty,
R_S^complete = Z_empty R_S.
```

Only the already proved identity

```text
Z_empty Z_empty = I
```

is used.  The proof does not assume the stronger statement `Z_empty = I`.
The two empty factors cancel only after the full forward/base/reverse product
has been assembled.

## 3. Complete numerator

Proof 496 supplies the ordered Schur--Markov numerator

```text
N_S
 = transitionProduct_S * alpha_empty * reverseProduct_S
   - rho_S * alpha_S.
```

Proof 497 identifies the complete products as

```text
transitionProduct_S = upper_S^(-1) * F_S,
reverseProduct_S    = lower_S * R_S^complete,
rho_S               = lower_S / upper_S.
```

After the two empty polar coordinates cancel, Lean obtains the operator
identity

```text
N_S
 = rho_S *
   (L_S * leftOrderedSourceBandGramResponse_S * R_S).
```

This identity is formed before any norm or absolute value.  No local prime
term is estimated separately, and no inverse transition is exposed.

## 4. Legal trace readback

The left-ordered and route-ordered Gram responses are adjoints:

```text
leftOrderedSourceBandGramResponse_S
  = sourceBandGramResponse_S^dagger.
```

They are not equal as operators.  To remove the bounded similarity from the
ordinary trace, the proof sandwiches the swapped four-branch
Hilbert--Schmidt pair by `L_S` and `R_S`.  The explicit inverse identity
`R_S L_S = I` then acts on the boundary carrier inside two already legal
trace cycles.  Consequently

```text
Tr(N_S)
  = rho_S * conjugate(Tr(sourceBandGramResponse_S)),

|Tr(N_S)|
  = rho_S * |Tr(sourceBandGramResponse_S)|.
```

The complex conjugation is the surviving left/right Gram-order distinction.
It disappears only after taking the complex norm; the operator ordering is
never identified or discarded.

## 5. Remaining Gate 3U theorem

The exact missing analytic producer is a family-uniform estimate

```text
|Tr(N_S)|
  <= rho_S * C * (1+B_root)^d * ||g||_(H^r)^2,
```

where `C`, `d`, and `r` do not depend on the finite visible-prime family.
By the exact positive scaling above, this is equivalent to the corresponding
support--Sobolev bound for the route endpoint.

Proof 497 proves only this exact equivalence.  It supplies no bound for the
signed cocycle itself.  Therefore Gate 3U, the finite-S sign,
negative-owner integration, Burnol's identity, and RH remain open.
