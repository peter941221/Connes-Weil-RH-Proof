# Proof 433: fixed-quotient contraction bound

Date: 2026-07-20

Status: axiom-clean, visible-family-uniform bound for the literal normalized
finite-Euler fixed-quotient first-jet owner on `Ran(E-R)`.  The proof keeps the
balanced four-coordinate physical pair whole and uses only contraction of the
maps which change its source carrier.

This result shows that Proof 432's Julia readout and Julia range summability
are not necessary to bound this first-jet owner.  It does not identify the
first jet with the complete Burnol endpoint response, prove the required
support--Sobolev bound for the fixed physical energy, close Gate 3U, prove the
finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| actual input carrier                                 | Ran(E-R)             |
| band-to-Sonin input                                  | contraction          |
| complete four-coordinate pair                        | retained whole       |
| bounded sandwich square energy                       | nonincreasing        |
| band-carrier precomposition square energy            | nonincreasing        |
| first-jet trace bound depends on visible family      | no                   |
| Julia readout needed for this first-jet bound         | no                   |
| fixed physical energy has support--Sobolev bound      | not proved here      |
| first jet = complete Burnol endpoint                 | not proved           |
| Gate 3U / finite-S sign / Burnol / RH                | open / open / open   |
+------------------------------------------------------+----------------------+
```

The dependency has been shortened from

```text
physical first-jet column
  -> actual suffix Julia range column
  -> independent fixed-source readout
  -> square summability premise
  -> trace bound                                             (CT.1)
```

to

```text
fixed physical four-coordinate pair
  -> contractive fixed-quotient sandwich
  -> contractive change to Ran(E-R)
  -> trace bound.                                            (CT.2)
```

Equation `(CT.2)` is stronger for the first-jet owner because it has no
`stepData`, readout, Douglas factor, or visible-prime sum.

## 2. What the owner is

Use the source projections

```text
R <= E,
B = E-R,
J_B : Ran(B) -> H.                                    (CT.3)
```

Let

```text
A_S = normalizedFiniteEulerInverse(S),
N_S = E A_S E.                                       (CT.4)
```

The literal rectangular input from Proof 432 is

```text
I_(S,B->R)=J_R* E A_S E J_B.                         (CT.5)
```

Every factor in `(CT.5)` is a contraction:

```text
norm(J_R*) <= 1,
norm(E) <= 1,
norm(A_S) <= 1,
norm(J_B) <= 1.                                      (CT.6)
```

Lean therefore proves

```text
norm(I_(S,B->R)) <= 1.                               (CT.7)
```

The first-jet response is not estimated by expanding its outer,
reflected-outer, second-support, and prolate terms.  Those four physical
coordinates are already assembled in

```text
fixedPhysicalPairData = (L_phys,R_phys).             (CT.8)
```

The quotient first jet changes only the inputs of this pair:

```text
L_S =L_phys B*,
R_S =R_phys R N_S B.                                 (CT.9)
```

It then precomposes both legs with `J_B`.  The resulting trace product acts
on the genuine band carrier:

```text
Q_S^jet
 =J_B* B [W_E,R] R N_S B J_B.                       (CT.10)
```

The displayed commutator is already the completed physical commutator owned
by the four-coordinate pair.  Equation `(CT.10)` does not split its branches.

## 3. Hilbert--Schmidt ideal step

For a Hilbert--Schmidt map `C` and a bounded contraction `D`, basis
independence of the Hilbert--Schmidt norm gives

```text
sum_k norm(C D f_k)^2
 <=norm(D)^2 sum_i norm(C e_i)^2
 <=sum_i norm(C e_i)^2.                              (CT.11)
```

The first inequality was already proved in the repository as

```lean
CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
```

Proof 433 packages its norm-at-most-one specialization for both legs of
`boundedPrecomp` and `boundedSandwich`.  Applying `(CT.11)` twice gives

```text
sum_i norm(L_S J_B e_i)^2
 <=sum_i norm(L_phys e_i)^2,

sum_i norm(R_S J_B e_i)^2
 <=sum_i norm(R_phys e_i)^2.                         (CT.12)
```

No constant in `(CT.12)` depends on `S` or on `family.visiblePrimes`.

## 4. Trace estimate

For every basis vector, Cauchy--Schwarz and
`2ab <= a^2+b^2` give

```text
abs(<L_S J_B e_i,R_S J_B e_i>)
 <=1/2 [norm(L_S J_B e_i)^2+norm(R_S J_B e_i)^2].    (CT.13)
```

Sum `(CT.13)` and insert `(CT.12)`:

```text
abs Tr(Q_S^jet)
 <=1/2 [
      sum_i norm(L_phys e_i)^2
     +sum_i norm(R_phys e_i)^2
   ].                                                (CT.14)
```

The right side is one fixed physical boundary energy.  It depends on the
selected root, the support window, the Sonin scale, the named bases, and the
prolate Hilbert--Schmidt witness.  It does not depend on the finite Euler
family.

The Lean theorem is

```lean
sourceBandFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_fixedPhysicalEnergy
```

in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSFixedQuotientContractionBound.lean
```

## 5. Consequence for Proof 432

Proof 432 required

```text
physical right column
 =fixed-source readout of an actual suffix Julia range column,

sum_i norm(actual Julia range column on e_i)^2 < infinity.  (CT.15)
```

Those remain valid sufficient premises for its Julia/Douglas consumer.  They
are not necessary to prove `(CT.14)`.  The reason is structural:

```text
Proof 432:
  factor the physical right column through a more specific Julia column;

Proof 433:
  keep the already Hilbert--Schmidt physical pair and use ideal contraction.
                                                               (CT.16)
```

The Julia route asks for a kernel-aligned factorization and therefore solves
a stronger problem.  Proof 388 already showed that such alignment does not
follow from abstract moving-range geometry.  Proof 433 avoids that kernel
condition for the first jet rather than pretending to prove it.

## 6. Exact remaining gap

There are two distinct arrows after `(CT.14)`:

```text
fixed physical square energy
  -> support-polynomial Sobolev bound for the selected root;      (CT.17)

fixed-quotient first jet
  -> complete Burnol weighted endpoint Lambda_(S_F)(F).           (CT.18)
```

Neither arrow is proved here.  The full endpoint is Proof 415's completed
weighted semicommutator, equivalently Proof 429's target-commutator response.
It retains the relative Gram ordering and trace anomaly.  A local first-jet
bound cannot replace the endpoint without an exact source telescope or
integration theorem.

The active decision is therefore

```text
do not spend the next step constructing `fixedSourceReadout`
merely to bound this first jet;

instead prove `(CT.17)` and the same-object endpoint bridge `(CT.18)`,
or estimate the complete endpoint directly.                         (CT.19)
```

## 7. Source boundary

The quantitative ideal inequality in `(CT.11)` is proved locally in Lean.
The primary model-space sources already audited by the route remain useful
for carrier semantics, but they do not supply `(CT.18)`:

```text
J.-F. Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation de Fourier,
Theorem 8,
https://arxiv.org/abs/math/0208121

Y. Liang and J. R. Partington,
Spectra and invariant subspaces of compressed shifts on nearly invariant
subspaces,
Theorem 1.2 and Proposition 2.3,
https://arxiv.org/abs/2506.18646
```

Burnol identifies the Sonin/de Branges carrier.  Liang--Partington supplies
the weighted nearly invariant coordinate and a rank-one compressed-shift
description.  Neither source proves the completed relative projection trace,
the four-branch support--Sobolev energy bound, or the canonical Euler endpoint
telescope required by `(CT.17)--(CT.18)`.

The 2026-07-20 `research-stack` arXiv search for weighted truncated-Toeplitz
Schatten estimates returned results about Bergman/Fock Toeplitz operators,
not this singular-inner model-space relative trace.  Those different carrier
contracts were not imported.

## 8. Verification

The isolated Ubuntu 24.04 ext4 focused audit passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| fixed-quotient contraction-bound axiom audit         |  3258 | PASS   |
| `CCM25Concrete` aggregate                            |  3708 | PASS   |
| full repository                                      |  3789 | PASS   |
+------------------------------------------------------+-------+--------+
```

All six audited declarations depend exactly on

```text
[propext, Classical.choice, Quot.sound].              (CT.20)
```

No project axiom, proof placeholder, `sorryAx`, new linter warning, or Gate
premise was added.
