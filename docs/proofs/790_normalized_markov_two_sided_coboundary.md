# Proof 790: Two-sided normalized Markov coboundary

## Result

For the literal normalized actual-band first jet `J_S`, prepending a visible
prime gives the exact two-sided difference

```text
J_(p::S) - J_S = X_(p,S) + X_(p,S)^dagger.
```

Here `X_(p,S)` retains the complete old normalized Markov prefix, the genuine
one-prime translation coboundary, the detector, the quotient band, and the
source Sonin projection.  The second summand has a plus sign.

```text
old Markov prefix + one-prime coboundary
                    |
                    v
              X + X^dagger
                    |
                    v
       no internal linear cancellation
```

## Why It Matters

The raw one-prime coefficient is `p^(-1/2)`.  Since the two-sided first jet
is Hermitian addition rather than subtraction, it cannot produce the
`p^(-1)` or lower-factor-square decay needed for Gate 3U by itself.

The matching completed remainder must stay in the same physical pairing
before any absolute value is taken.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovTwoSidedFirstDifference.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovTwoSidedFirstDifferenceAudit.lean
```

Key declarations:

```text
normalizedListActualBandPairedResponse_cons_sub_eq_twoSidedCoboundary
normalizedListActualBandTwoSidedCoboundary_eq_left_add_adjoint
sourceActualBandFiniteEulerPairedResponse_eq_normalizedList
```

## Scope

```text
+---------------------------------------------------------+-------------+
| statement                                               | status      |
+---------------------------------------------------------+-------------+
| two-sided first jet is X + X^dagger                    | Lean proved |
| internal Markov cancellation of the half-power term     | ruled out   |
| completed physical cancellation                         | open        |
| Gate 3U / finite-S sign / Burnol / RH                   | open        |
+---------------------------------------------------------+-------------+
```
