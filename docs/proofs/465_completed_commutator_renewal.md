# Proof 465: Completed commutator renewal

## Result

The normalized finite-Euler inverse has the existing operator-norm expansion

```text
A_S = sum'_i weight_i U_(-d_i).
```

Proof 465 pushes this series through Proof 464's complete common-right-leg
owner:

```text
C_g P [A_S,B] B
  = sum'_i C_g P [weight_i U_(-d_i),B] B.
```

The map from a transport operator `A` to `C_g P[A,B]B` is constructed as a
continuous linear map on the operator Banach space.  Therefore the equality
uses `map_tsum` on the already proved operator-norm summable renewal series.

Every atom contains the convolution root, source Sonin projection, and both
quotient-band positions before summation.  The proof does not expand the
three physical branches or cycle an infinite-dimensional trace.

The fixed left root leg is then pushed through the same operator-norm series:

```text
(C_g B)^dagger C_g P [A_S,B] B
  = sum'_i (C_g B)^dagger C_g P [weight_i U_(-d_i),B] B.
```

Thus the summands are atoms of the complete root-homogeneous first-jet owner,
not merely atoms of an intermediate transport operator.

Each atom is also separated into its probability coefficient and its literal
causal displacement:

```text
pairAtom_i
  = weight_i * TranslationCommutatorPair(displacement_i).
```

The unweighted response retains the complete root/Sonin/band sandwich.  This
is the form needed to compare the displacement with compact root support.

Combining the two steps gives the direct displacement-law interface

```text
completeCorner
  = sum'_i weight_i * TranslationCommutatorPair(displacement_i).
```

Future analysis can therefore work with the single real parameter
`displacement` while the multi-prime combinatorics remains confined to a
probability law.

## Boundary

Proof 465 establishes operator-norm summability and an exact same-object
series.  It does not take atomwise absolute values, prove compact-support
vanishing of an atom's trace, construct a Hilbert--Schmidt boundary factor,
or prove a family-uniform trace bound.  Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
