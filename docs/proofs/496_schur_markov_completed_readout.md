# Proof 496: Schur--Markov completed readout

Date: 2026-07-22

Status: revised Steps 1--3 are complete at the exact Lean producer level.
The former single positive right-leg readout is false and has been replaced by
an actual forward/reverse Schur--Markov signed cocycle.  The remaining Gate 3U
statement is a family-uniform signed trace estimate, not another carrier or
telescoping identity.

## 1. Result

```text
+--------------------------------------------------+-------------------------+
| layer                                            | result                  |
+--------------------------------------------------+-------------------------+
| actual suffix Schur telescope                    | exact                   |
| terminal Julia survivor                          | exact                   |
| reverse source Markov transition                 | contraction             |
| forward/reverse products                         | rho_S * I, both orders  |
| local detector numerator                         | boundary * reverse      |
| complete detector numerator                      | signed finite cocycle   |
| ordered trace-anomaly correction                 | retained exactly        |
| lower-factor completed response readback         | exact after rho_S scale |
| fixed physical source input                      | family independent      |
| fixed source energy                              | <= 2 * fixed majorant   |
| family-uniform signed trace estimate / Gate 3U   | open                    |
+--------------------------------------------------+-------------------------+
```

## 2. Forward and reverse pair

For an adjacent suffix `p :: S -> S`, Lean constructs the actual source
transitions

```text
G_(p,S) = oldFrame^dagger * normalizedForward_p * newFrame,
R_(p,S) = newFrame^dagger * normalizedInverse_p * oldFrame.
```

Both are contractions and satisfy

```text
G_(p,S) R_(p,S) = R_(p,S) G_(p,S) = rho_p I,

rho_p = (1-p^(-1/2))/(1+p^(-1/2)).
```

For the complete ordered products `Gamma_S` and `Lambda_S`,

```text
Gamma_S Lambda_S = Lambda_S Gamma_S = rho_S I,

rho_S
 = product_(p in S) rho_p
 = finiteEulerLowerFactor(S) / finiteEulerUpperFactor(S) > 0.
```

No inverse transition or inverse Gram norm occurs in these identities.

## 3. Signed detector cocycle

Let `alpha_S` be the selected detector compressed through the actual suffix
polar frame.  The complete numerator is

```text
N_S = Gamma_S alpha_empty Lambda_S - rho_S alpha_S.
```

At one step, the direct rectangular-carrier proof gives

```text
N_(p,S)^local
 = -oldFrame^dagger * normalizedForward_p
     * (I-newFrame*newFrame^dagger)
     * detector * newFrame
     * R_(p,S).
```

The complete numerator is the recursive signed telescope

```text
N_(p::S)
 = G_(p,S) N_S R_(p,S)
   + N_(p,S)^local * rho_S.
```

Every sign and operator order is retained until after the complete finite sum.
There is no primewise absolute value.

## 4. Ordered response correction

The polar cocycle and the route's ordered Gram endpoint are not the same
operator ordering.  Cycling one into the other in infinite dimensions would
erase the trace anomaly protected by Proof 264.  Define the scaled ordering
defect

```text
Delta_S^ord
 = N_S - rho_S * sourceBandGramResponse_S.
```

The corrected complete signed owner is

```text
C_S
 = rho_S * actualBandFirstJet_S - N_S + Delta_S^ord.
```

Lean proves the unconditional same-object identity

```text
C_S
 = rho_S * lowerFactorGaugedActualBandCompletedRelativeResponse_S.
```

The actual first jet and ordered endpoint already contain the complete outer,
reflected-outer, second-support, and prolate physical ledger.  None of those
branches is split or discarded in this readback.

Under the existing fixed-family trace-legality witness, Lean also proves

```text
Tr(C_S)
 = rho_S * Tr(lowerFactorGaugedCompletedResponse_S).
```

This trace theorem is obtained from the exact operator equality, not from a
new cyclic permutation.

## 5. Fixed source input

The complete physical pair is pulled back through the literal source Sonin
inclusion before taking its positive Gram square root.  The resulting
`fixedPhysicalSourceInput` contains no finite prime family and satisfies

```text
sum_i ||fixedPhysicalSourceInput e_i||^2
 <= 2 * fixedPhysicalEnergyMajorant.
```

This closes the source-energy producer requested in Step 3.  It does not by
itself construct a uniformly bounded signed readout of `C_S`.

## 6. Rejected shortcut

The former proposal tried to read the combined coframe through one positive
right leg.  At zero detector that identity would force an unsupported
vanishing relation for the forward and metric coframes.  It cannot be used as
a Gate producer.

The replacement keeps the two orientations as a signed cocycle and restores
the exact ordered anomaly before taking a trace.  This is weaker than a
positive factorization but is mathematically valid.

## 7. Remaining Gate 3U theorem

The exact remaining target is a support--Sobolev estimate of the form

```text
abs Tr(C_S)
 <= rho_S * C * (1+B_root)^d * ||g||_(H^r)^2,
```

with `C`, `d`, and `r` independent of the finite visible-prime family.  By the
readback above and `rho_S > 0`, this is equivalent to the desired uniform
bound for the lower-factor-gauged completed response.

Proof 496 does not prove this estimate.  Therefore Gate 3U, the finite-S sign,
negative-owner integration, Burnol's identity, and RH remain open.
