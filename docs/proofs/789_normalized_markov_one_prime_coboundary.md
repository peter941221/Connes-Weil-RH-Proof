# Proof 789: Normalized Markov one-prime coboundary

Date: 2026-08-03

Status: axiom-clean Lean closure of the discrete one-prime difference for the
normalized causal Euler inverse. This identifies the exact signed first-order
operator that enters when a visible prime is prepended. It does not prove a
quadratic Euler gain, a trace bound, Gate 3U, the finite-S sign, Burnol's
identity, or `_root_.RiemannHypothesis`.

## Result

For one visible prime, write

```text
a_p = p^(-1/2)
U_p = translation by -log(p)
T_p = I - a_p U_p
M_p = (1-a_p) T_p^(-1).
```

The new Lean theorem proves the literal identity

```text
M_p - I = a_p (U_p-I) T_p^(-1).                       (789.1)
```

For the normalized inverse of an ordered visible-prime list, write `M_S`.
The causal recursion is therefore

```text
M_(p::S) - M_S
  = M_S [a_p (U_p-I) T_p^(-1)].                       (789.2)
```

The old complete prefix remains on the left. The new prime is inserted as a
single signed translation coboundary, with its genuine inverse still attached.

## Derivation

Equation `(789.1)` is direct operator algebra:

```text
M_p - I
 = [(1-a_p) I - (I-a_p U_p)] T_p^(-1)
 = a_p (U_p-I) T_p^(-1).
```

Equation `(789.2)` then uses the existing exact recursion

```text
M_(p::S) = M_S M_p.
```

No renewal atom, prime channel, physical branch, or trace norm is expanded in
this derivation.

## Why It Matters

```text
normalized prefix M_S
        |
        | prepend p
        v
M_S [a_p (U_p-I) T_p^(-1)]
        |
        | must remain inside the completed physical pairing
        v
possible two-sided cancellation
        |
        v
support-polynomial Gate 3U estimate
```

The identity supplies the correct discrete first-variation coordinate. It is
not itself a `p^(-1)` estimate: its explicit scale is `a_p=p^(-1/2)`. A valid
quadratic conversion must recombine both sides of the actual completed
outer/reflected-second-support/prolate kernel before the first absolute value.
Replacing `(789.2)` by a norm bound would lose exactly that possible
cancellation.

The scalar lower-factor gauge cannot repair this on its own. Existing paired
frame/coframe identities make that gauge invariant at the completed
projection owner, while Proof 788 shows that the raw Gate still requires
lower-factor-square decay of the normalized completed trace.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovFirstDifference.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovFirstDifferenceAudit.lean
```

The public declarations are:

```text
normalizedPrimeEulerInverseTranslationCoboundary
normalizedPrimeEulerInverse_sub_id_eq_translationCoboundary
normalizedFiniteEulerInverseList_cons_sub_eq_prefixedTranslationCoboundary
```

## Verification

The Ubuntu-24.04 WSL2 ext4 verification used a clean source snapshot with a
shared package cache and a fresh project build directory.

```text
+-----------------------------------------------------------+-------+--------+
| target                                                    | jobs  | result |
+-----------------------------------------------------------+-------+--------+
| Proof 789 source                                          |  3170 | PASS   |
| Proof 789 focused axiom audit                             |  3171 | PASS   |
| CCM25Concrete aggregate                                   |  4047 | PASS   |
+-----------------------------------------------------------+-------+--------+
```

Both audited theorems use exactly

```text
[propext, Classical.choice, Quot.sound].
```

## Scope

```text
+--------------------------------------------------------------+----------------+
| statement                                                    | status         |
+--------------------------------------------------------------+----------------+
| one-prime normalized inverse equals a signed coboundary      | Lean proved    |
| finite-prefix one-prime difference keeps the old prefix      | Lean proved    |
| two-sided completed-kernel cancellation                      | open           |
| lower-factor-square normalized trace decay                   | open           |
| Gate 3U / finite-S sign / Burnol / RH                        | open           |
+--------------------------------------------------------------+----------------+
```
