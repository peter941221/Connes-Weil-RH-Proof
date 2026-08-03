# Proof 779: One-row Hardy--Prolate Gate factorization

## Result

Proof 779 turns the complete causal bracket of Proofs 777--778 into one
rectangular row product on the literal common-log Hilbert carrier.  Let

```text
E = radial support projection
F = I-E
T_S = finite Euler transport
A = F H E
P = Q(E-R)
L = (A, P)  in the Hilbert L2 direct sum.
```

The source Gram remains exactly

```text
L* L = A* A + P* P = E-R.
```

Define the two complete rows

```text
X_S = (E, L T_S*),
Y_S = (T_S F, L).
```

Lean proves the exact row identity

```text
X_S* Y_S = E T_S F + T_S L* L.
```

Consequently the literal Gate target is

```text
Target_S
 = (X_S D_S)* Y_S C_root* C_root J.
```

Every matrix coefficient is therefore one root-sandwiched completed-row
pairing:

```text
<x, Target_S y>
 = <X_S D_S x, Y_S C_root* C_root J y>.
```

For every named source Hilbert basis `(e_i)`, the ordinary trace is therefore
the one signed diagonal series

```text
Tr(Target_S)
 = sum_i <X_S D_S e_i, Y_S C_root* C_root J e_i>.
```

## Why This Form Matters

The first coordinate of the row is the causal outer crossing.  The second
coordinate is the entire Hardy/prolate Gram.  The Hilbert `L2` row inner
product adds them only after they have been evaluated against the same two
vectors:

```text
same left vector          same right vector
       |                         |
       v                         v
  (outer, Hardy, prolate)  <---- one row pairing
```

This is the correct object for a root-relative weighted Toeplitz or
Wiener--Hopf estimate.  It does not authorize a bound of the form
`norm(outer) + norm(Hardy) + norm(prolate)`: that would apply an absolute
value before the cancellation required by Proof 260.

## Scope

Proof 779 is an operator and scalar-pairing identity.  It supplies neither a
uniform bound for the completed row pairing nor a trace estimate.  The active
Gate 3U producer remains a compact-root, support-polynomial estimate for this
one signed pairing, uniform in the visible finite prime set.

It does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
