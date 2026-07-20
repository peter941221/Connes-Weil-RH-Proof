# Proof 435: centered root-pair normal form

Date: 2026-07-20

Status: axiom-clean exact reduction of the root-completed fixed-quotient first
jet to one centered signed two-leg pairing.  This corrects the provisional
reading of Proof 434's five visible energies as five independent analytic
obligations.

This proof does not establish the family-uniform signed estimate, the
same-object Burnol endpoint bridge, Gate 3U, the finite-`S` sign, Burnol's
identity, or RH.

## 1. Verdict

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| `A_0` supplied by the existing prolate factor        | proved               |
| `A_2` is a projection suffix of `A_1`                | proved               |
| `D_1` is a projection suffix of `D_0`                | proved               |
| independent expanded root legs                       | `A_1`, `D_0`          |
| exact normal form for `A_1`                          | proved               |
| exact centered normal form for `D_0`                 | proved               |
| `A_0+A_1=C_g B`                                      | proved               |
| three branches = one centered signed root pairing    | proved               |
| uniform polynomial estimate for that signed pairing  | open                 |
| same-object Burnol endpoint bridge                   | open                 |
| Gate 3U / finite-S sign / Burnol / RH                | open                 |
+------------------------------------------------------+----------------------+
```

The route correction is

```text
five visible square energies
        |
        +-- A_0: existing prolate factor
        +-- A_2: Q after A_1
        +-- D_1: (I-Q) after D_0
        |
        v
two independent expanded legs A_1 and D_0
        |
        +-- recombine A_0+A_1 before estimating
        v
one centered signed pairing.                              (RN.1)
```

## 2. Notation

On the common logarithmic Hilbert carrier let

```text
E      =radialSupportProjection,
Q      =sourceFourierSupportProjection,
P      =sourceSoninProjection,
B      =E-P,
K_prol =E Q E-P,
C_g    =rootConvolution,
A_S    =normalizedFiniteEulerInverse.                    (RN.2)
```

The projection geometry proved in Lean is

```text
E B=B,       B E=B,
P B=0,
(I-Q)B=(I-Q)E.                                          (RN.3)
```

The first three identities say that `B` is the orthogonal quotient band
inside `E`.  The last identity says that the Fourier-support complement cannot
see the Sonin part removed from `E`.

## 3. Five visible legs, two independent legs

Proof 434's expanded pair uses

```text
A_0=(B Q E C_g^dagger)^dagger,
A_1=(B(I-Q)E C_g^dagger)^dagger,
A_2=(B(I-Q)[E C_g^dagger,Q])^dagger,

D_0=C_g E P(E A_S E)B,
D_1=[C_g E,Q]P(E A_S E)B.                              (RN.4)
```

The existing source prolate factor is

```text
F_prol=Q B,
F_prol^dagger F_prol=K_prol.                           (RN.5)
```

Lean now proves

```text
E F_prol=K_prol,
A_0=C_g K_prol.                                        (RN.6)
```

Thus `A_0` is already square-summable from the axiom-clean source prolate
witness.  The other two reductions are

```text
A_2=Q A_1,
D_1=(I-Q)D_0.                                          (RN.7)
```

Both suffixes are orthogonal projections and have operator norm at most one.
Therefore `A_2` and `D_1` introduce no independent summability or energy
premise.

The reduced geometric-energy consumer from Proof 434 is consequently

```text
abs Tr(first jet)
 <=sqrt(norm(C_gE)^2 E(F_prol)+2 E(A_1))
   sqrt(3 E(D_0)),                                     (RN.8)

E(T)=sum_i norm(T e_i)^2.
```

This bound is correct when its two independent root-leg premises hold.  It is
not the final family-uniform estimator.

## 4. Exact normal forms

The left Fourier-leakage leg is

```text
A_1=C_g E(I-Q)E
   =C_g(B-K_prol).                                     (RN.9)
```

The equality follows from

```text
E(I-Q)E
 =E-E Q E
 =(E-P)-(E Q E-P)
 =B-K_prol.                                            (RN.10)
```

This is important: the existing prolate witness controls `K_prol`, not the
full difference `B-K_prol`.  Fixed-`S` trace legality for a completed product
also does not imply that `A_1` is Hilbert--Schmidt by itself.

The common right leg first reduces to

```text
D_0=C_g P A_S B.                                       (RN.11)
```

Since `P B=0`, its constant part vanishes:

```text
D_0=C_g P(A_S-I)B.                                    (RN.12)
```

The normalized inverse `A_S` is the exact causal probability average from
`CCM24FiniteSCausalMarkov.lean`.  Equation `(RN.12)` removes the probability
law's constant mass before any renewal atom is exposed.

## 5. Recombination before estimation

Equations `(RN.6)` and `(RN.9)` give

```text
A_0+A_1
 =C_g K_prol+C_g(B-K_prol)
 =C_g B.                                               (RN.13)
```

The two commutator orientations in Proof 434 also recombine exactly.  Using
`A_2=Q A_1` and `D_1=(I-Q)D_0`, their operator sum is

```text
A_0^dagger D_0
 +A_1^dagger(I-Q)D_0
 +(Q A_1)^dagger D_0

 =(A_0+A_1)^dagger D_0.                               (RN.14)
```

Because `Q=Q^dagger`, the last two terms add to `A_1^dagger D_0`.  Lean proves
the resulting same-object identity directly:

```text
sourceRootCompletedFixedQuotientCorner
 =(C_g B)^dagger sourceRootCompletedCommonRightLeg.    (RN.15)
```

For the actual normalized finite-Euler inverse this becomes

```text
sourceRootCompletedFixedQuotientCorner_S
 =(C_g B)^dagger C_g P(A_S-I)B.                        (RN.16)
```

The orthogonal three-coordinate `A^dagger B` carrier remains useful: it is a
fixed-`S` trace-legality certificate.  Equation `(RN.16)`, rather than the sum
of five nonnegative energies, is the object on which a family-uniform estimate
must act.

## 6. Why atomwise absolute values are forbidden

The next target is a scalar estimate of the form

```text
abs Tr((C_g B)^dagger C_g P(A_S-I)B)
 <=C_lambda (1+B_root)^d seminorm_r(g)^2,              (RN.17)
```

uniformly for the support-coupled canonical finite-prime family.

Do not expand `A_S-I` into causal renewal atoms and take absolute values term
by term.  Proof 260 gives the exact completed crossing model

```text
K_(I,b,g)=C_g U_b E_I C_g^dagger,
Tr(K_(I,b,g))=|I| F_g(b),
norm(K_(I,b,g))_1=|I| norm(g)_2^2.                    (RN.18)
```

Compact root support makes the signed trace zero for sufficiently large
`abs(b)`, while the nuclear norm stays strictly positive.  Hence total
variation destroys exactly the support cancellation needed for `(RN.17)`.

The required order is

```text
complete causal renewal
  -> outer minus Sonin plus prolate recombination
  -> compact-support cancellation in the scalar pairing
  -> first absolute value.                             (RN.19)
```

## 7. Source audit

A narrow primary-source search found no theorem which supplies `(RN.17)`.

```text
CC20, Weil positivity and Trace formula, the archimedean place:
https://arxiv.org/abs/2006.13771

CCM24, Zeta zeros and prolate wave operators:
https://arxiv.org/abs/2310.18423

Peller, Besov spaces in operator theory:
https://arxiv.org/abs/2402.09853
```

CC20 supplies the archimedean prolate structure.  CCM24 supplies semilocal
Sonin transport and stability.  Peller surveys Besov characterizations of
Hankel operators in Schatten classes.  None of them states a canonical-family
uniform bound for the centered signed pairing `(RN.16)`.  The statement
"no matching producer was found" is a literature-search result; it is not a
proof that no such theorem can exist.

## 8. Lean ownership

The new declarations are in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRootCompletedFirstJet.lean
```

The central declarations are

```lean
rootCompletedSecondSupportCorner_eq_unsplit
radialSupportProjection_comp_sourceProlateFactor_eq_remainder
sourceRootCompletedRangeLeftLeg_eq_root_prolateRemainder
sourceRootCompletedLeftLegs_add_eq_root_band
sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair
sourceRootCompletedFiniteEulerCorner_eq_centeredUnsplitRootPair
```

The generic noncommutative-ring recombination uses only `[propext]`.  The
concrete Hilbert-carrier normal forms use exactly

```text
[propext, Classical.choice, Quot.sound].               (RN.20)
```

No Gate estimate or RH conclusion is stored as an assumption.

## 9. Remaining route

```text
fixed-S trace legality                              CLOSED
root-homogeneous first-jet owner                    CLOSED
five-leg independence error                        CLOSED
centered signed root-pair normal form               CLOSED
uniform estimate (RN.17)                            OPEN
same-object first-jet to Burnol endpoint bridge     OPEN
Gate 3U / finite-S sign                             OPEN
Burnol identity                                     OPEN
_root_.RiemannHypothesis                            OPEN
```

The immediate analytic successor is `(RN.17)` on the complete signed pairing.
It must use the real-line half-line/Sonin geometry and compact root support
before every absolute value.

## 10. Verification

The isolated Ubuntu 24.04 ext4 batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| root-completed first-jet source                      |  3258 | PASS   |
| root-completed first-jet axiom audit                 |  3259 | PASS   |
| CCM25Concrete aggregate                              |  3709 | PASS   |
| full repository                                      |  3790 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit contains `64` `#check` commands and `58` matching
`#print axioms` commands.  No project axiom, proof placeholder, `sorryAx`,
global heartbeat increase, or new source linter warning was introduced.
