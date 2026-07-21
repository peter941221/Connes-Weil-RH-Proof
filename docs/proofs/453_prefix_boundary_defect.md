# Proof 453: Finite-prefix boundary defect

## Result

The first-`N` Hilbert-basis matrix compression does not preserve operator
composition.  Proof 453 names the exact defect

```text
Delta_N(A,B) = M_N(AB) - M_N(A) M_N(B).
```

For the operator commutator, Lean proves

```text
M_N(AB-BA)
  = M_N(A)M_N(B)-M_N(B)M_N(A)
    + Delta_N(A,B)-Delta_N(B,A).
```

Finite-dimensional trace cyclicity is legal on the internal matrix term, so

```text
Tr(M_N(AB-BA))
  = Tr(Delta_N(A,B)-Delta_N(B,A)).
```

The right side is the prefix-boundary leakage.  It is retained rather than
being erased by an invalid infinite-dimensional trace cycle.

## Lean interface

The source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSPrefixBoundaryDefect.lean
```

Its main declarations are:

```lean
basisPrefixProductDefect
basisPrefixMatrix_commutator_eq_internal_add_boundaryDefect
trace_basisPrefixMatrix_commutator_eq_trace_boundaryDefect
```

## Boundary

Proof 453 is an exact ledger, not a bound.  The next analytic producer must
estimate the antisymmetrized defect for the actual complete physical-boundary
owner uniformly in the visible finite prime set and in `N`.  Gate 3U, the
finite-`S` sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.
