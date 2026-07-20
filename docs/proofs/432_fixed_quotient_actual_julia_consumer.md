# Proof 432: fixed-quotient actual-Julia consumer

Date: 2026-07-20

Status: the nonzero fixed-quotient first jet now reaches the current-range
Douglas/Julia consumer on the correct input carrier.  A second carrier
mismatch is repaired by a rectangular adapter: the physical Euler input lives
on the source Sonin carrier, while the compact Hilbert--Schmidt root lives on
the packed four-coordinate boundary carrier.

This is an axiom-clean consumer theorem, not a Gate 3U estimate.  The physical
right-column readout equality and a uniform bound for the resulting Julia
range energy remain open.  The finite-S sign, Burnol identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| old input carrier Ran(R)                       | right band leg is zero    |
| corrected input carrier Ran(E-R)               | nonzero carrier           |
| abstract packed-boundary Julia adapters        | valid but not physical    |
| actual Euler Julia domain                      | source Sonin carrier      |
| compact pair root domain                       | packed boundary carrier   |
| rectangular band-to-Sonin Euler input          | Lean-owned                |
| actual suffix-generated Julia schedule         | forced by theorem type    |
| physical right-column readout equality         | open source theorem       |
| Julia range square summability                 | open source theorem       |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. The two carrier mismatches

Write

```text
E = source radial-support projection,
R = source Sonin projection,
B = E-R,
J_R : Ran(R) -> H,
J_B : Ran(B) -> H,
A_S = normalized finite-Euler inverse.             (FJ.1)
```

The first mismatch was the old precomposition

```text
B J_R=0.                                           (FJ.2)
```

Proof 431 replaces the source basis by a basis of `Ran(B)`.

The second mismatch appears one layer later:

```text
actual suffix Euler cascade:
  Ran(R) -> packed boundary output

fixed-quotient compact pair:
  Ran(B) -> packed boundary root -> packed boundary output.         (FJ.3)
```

These Hilbert carriers are not definitionally or mathematically
interchangeable:

```text
             J_B                 E A_S E              J_R*
  Ran(B) ----------> H --------------------------> H ---------> Ran(R)
     |                                                        |
     |                                                        |
     +-------------- physical rectangular input -------------+

  Ran(R) -- actual suffix Julia steps --> finite PiLp boundary column
                                                               |
                                                               v
                                                packed boundary readout
                                                               |
                                                               v
                                             physical compact right column
                                                               (FJ.4)
```

## 3. Lean owner

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSFixedQuotientBandConsumer.lean
```

It first specializes the corrected band producer to the actual finite Euler
inverse:

```lean
sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer
```

Four post-root adapters reconnect the existing abstract Douglas/readout
consumers:

```lean
sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDouglas
sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeReadout
sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDomination
sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeNormSqDomination
```

Those adapters are intentionally not counted as the physical Euler producer.
Their Julia step carrier is the packed boundary root.

## 4. Rectangular physical input

The actual carrier-changing input is

```lean
noncomputable def sourceBandFiniteEulerSoninInput
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda ∘L
    sourceBandInclusion lambda
```

Mathematically,

```text
I_(S,B->R)=J_R* E A_S E J_B.                       (FJ.5)
```

The ambient readback is proved rather than assumed:

```text
J_R I_(S,B->R)=R E A_S E J_B.                     (FJ.6)
```

The generic theorem

```lean
inputSideRectangularJuliaReadout_ordinaryTrace_norm_le
```

keeps four types separate:

```text
H = source band carrier,
K = packed compact-root carrier,
D = source Sonin Julia carrier,
G = packed boundary output carrier.                (FJ.7)
```

The route-facing specialization

```lean
sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_actualCurrentRangeReadout
```

uses only

```lean
currentRangeJuliaSteps
  (fixedSourceCurrentRangeJuliaSteps lambda stepData S)
```

and therefore cannot be instantiated with an unrelated bookkeeping list.

## 5. Exact remaining premises

The theorem has two source-specific premises:

```text
physical compact right column
  = actual suffix readout
      after the Julia range column and I_(S,B->R);                  (FJ.8)

sum_i ||JuliaColumn_S(I_(S,B->R)e_i)||^2 < infinity.                (FJ.9)
```

The distinction is essential.  In
`SuffixPrimeEulerProjectedJuliaSchurFrameStepData`,
`fixedSourceReadout` is an independent field.  The existing
`rangeSine_readback` constrains the ambient `readout`; it does not by itself
prove `(FJ.8)` for `fixedSourceReadout`.  Supplying a suffix schedule therefore
does not manufacture the physical right-column equality.

Likewise, `(FJ.9)` must retain the Julia range maps.  Replacing it by
Hilbert--Schmidt summability of the raw input `(FJ.5)` would be a stronger
claim and would discard the compact boundary localization that makes the
physical column trace legal.

The remaining proof problem is therefore:

```text
construct physical stepData and prove (FJ.8)
                       |
                       v
prove a support-polynomial, visible-set-uniform bound for (FJ.9)
                       |
                       v
insert the signed whole-object estimate into Gate 3U.              (FJ.10)
```

No branchwise norm or modewise prime expansion is licensed by this consumer.

## 6. Literature check

Connes' 2026 survey still describes convergence/positivity for the finite to
infinite Euler-product route as a proposed strategy, not a theorem:

```text
Alain Connes,
"The Riemann Hypothesis: Past, Present and a Letter Through Time"
https://arxiv.org/abs/2602.04022
```

The 2026 de Branges--Rovnyak trace model found in the current literature audit
starts with two unitary operators whose resolvent difference has fixed finite
rank:

```text
Daniel Alpay, Fabrizio Colombo, Izchak Lewkowicz, Irene Sabadini,
"Operator model and a trace formula for pairs of unitary operators"
Theorem 4.1, hypotheses (4.1)--(4.2)
https://arxiv.org/abs/2607.05334
```

The route has a nonunitary bounded-invertible Euler transport and only
compact-root-sandwiched trace-class differences.  The paper therefore supplies
neither `(FJ.8)` nor `(FJ.9)`.

## 7. Verification

The isolated Ubuntu 24.04 ext4 verification batch passes:

```text
+----------------------------------------------+-------+--------+
| target                                       | jobs  | result |
+----------------------------------------------+-------+--------+
| fixed-quotient band consumer axiom audit     |  3257 | PASS   |
| CCM25Concrete aggregate                      |  3707 | PASS   |
| full repository                              |  3788 | PASS   |
+----------------------------------------------+-------+--------+
```

The audit target is

```text
ConnesWeilRH.Dev.CCM24FiniteSFixedQuotientBandConsumerAudit.
```

All nine audited declarations depend exactly on

```text
[propext, Classical.choice, Quot.sound].          (FJ.11)
```

The large route-facing declaration uses a scoped
`maxHeartbeats 2000000`.  The step list, rectangular input, readout, and
readout bound are shared as local definitions so Lean does not repeatedly
normalize the same dependent expressions.  No global heartbeat option,
placeholder proof, project axiom, or Gate 3U premise was introduced.
