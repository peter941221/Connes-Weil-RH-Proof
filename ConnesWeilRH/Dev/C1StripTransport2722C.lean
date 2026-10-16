/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointRowBWired2721
import ConnesWeilRH.Dev.C1ExplicitFiniteNodeCorrection

/-!
# Record 2722C: strip-envelope transport from the explicit cardinal sum

The record-2722B screen froze the 2722A bridge-pin lane for the row-B
owner class (`NO-GO-TRIANGLE-LADDER-AT-PIPELINE-GRADE`): a pin built
from `exp B * derivOrderL1 k f` misses the wired constants by the
tabled factors, because it carries no imaginary-part decay.  The
record-2720 certified envelope is a different object: per-factor decay
rungs `Psi_z = min (3 * e^{r_z}, e^{r_z} * D_k * 2^k / tau_z^k)`
raised to the tenth seed power, which do reach the pinned constants
(artifact `results/2720_p3_certified_strip_constants.json`, row B).
The 2722B mechanism paragraph's "cancellation" label is superseded by
the erratum in `docs/proofs/2722B_strip_pin_screen.md`; the envelope
is a term-by-term majorant whose advantage is the decay, not
cancellation.

This module transports those certified objects into the wired slots.
The concrete row-B strip functions are the record-1958 finite-node
corrections `correction nodes seed y` (base: `nodes = targets`,
`y = 1`; correction: `nodes = owner`, `y = stored target values`),
whose Laplace transform is the explicit cardinal sum of record 1980/
2720 (`laplaceAt_correction`).  The three quantified black-box strip
premises of `fourPointContradictionRowBWired2721C` are replaced by
two identification equalities plus three pins ON THE EXPLICIT SUM;
the pins are exactly the record-2720 certified inequalities, kept as
named hypotheses (proxy-tie doctrine, records 2657/2721B) and bound
to the committed artifact by `scripts/check_strip_transport_2722c.py`
(including a tail extension of the envelope scan beyond the recorded
TAIL_T = 600).

No wired hypothesis is removed by this record: the strip obligation
is relocated from an abstract owner to a concrete finite sum whose
artifact-grade certification already exists.  Nothing here is a
producer GO or an RH claim; the map-103 freeze is unchanged (premise
shrinking under the reopen motion, same doctrine as 2721B/C).
-/

namespace ConnesWeilRH
namespace Source
namespace C1StripTransport2722C

open Matrix
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1ArchimedeanIntegrabilityGeneric
open C1CenterTwoCriterionBridge
open C1GateMatrixRepresentation
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SpectralTailBound
open C1SpectralSummability
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open C1FourPointHighShellTail
open C1FourPointSpanGateCertificate
open C1SignedVarianceIdentity
open C1BipartiteMeanGapCertificate
open C1FourPointContradictionAssembly
open C1FourPointRowBWired2721
open C1ExplicitFiniteNodeCorrection
open scoped BigOperators

noncomputable section

/-- The explicit cardinal sum of records 1980/2720:
`cardinal s = sum_z (y z / (Q_z * laplaceAt seed 0)) *
prod_{w != z} (w - s) * laplaceAt seed (s - z)`, cancellation retained
inside the sum.  This is the object the record-2720 envelope
certifies, and (by `laplaceAt_cardinalOwner`) the Laplace transform of
the concrete cardinal owner below. -/
def cardinalSum (nodes : Finset ℂ) (seed : CompactLogTest) (y : ℂ → ℂ)
    (s : ℂ) : ℂ :=
  ∑ z ∈ nodes, (y z / (nodeProduct nodes z z * laplaceAt seed 0)) *
    (nodeProduct nodes z s * laplaceAt seed (s - z))

/-- The concrete strip owner: the record-1958 finite-node correction.
Instantiating `nodes` with the row-B targets (`y = 1`) gives the
record-2720 base; instantiating with the full owner list and the
stored target values gives the row-B correction. -/
def cardinalOwner (nodes : Finset ℂ) (seed : CompactLogTest) (y : ℂ → ℂ) :
    CompactLogTest :=
  C1ExplicitFiniteNodeCorrection.correction nodes seed y

/-- Identification: the Laplace transform of the concrete cardinal
owner is the explicit cardinal sum (record-1980 `cardinal_transform`
in the source `exp (s * x)` convention). -/
theorem laplaceAt_cardinalOwner (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ) (s : ℂ) :
    laplaceAt (cardinalOwner nodes seed y) s = cardinalSum nodes seed y s :=
  laplaceAt_correction nodes seed y s

/-- Transport for the base contraction premise: the wired `hcontract`
threshold bound at `T = 64` follows from the same pin stated on the
explicit cardinal sum. -/
theorem hcontractOfCardinalPin (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ)
    (hpin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, 64 ≤ |t| →
        ‖cardinalSum nodes seed y ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721) :
    ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, 64 ≤ |t| →
        ‖laplaceAt (cardinalOwner nodes seed y)
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721 := by
  intro sigma hsigma t ht
  rw [laplaceAt_cardinalOwner]
  exact hpin sigma hsigma t ht

/-- Transport for the base quartic premise. -/
theorem hquarticOfCardinalPin (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ)
    (hpin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖cardinalSum nodes seed y
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721) :
    ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖laplaceAt (cardinalOwner nodes seed y)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721 := by
  intro sigma hsigma t
  rw [laplaceAt_cardinalOwner]
  exact hpin sigma hsigma t

/-- Transport for the correction quadratic premise. -/
theorem hquadraticOfCardinalPin (nodes : Finset ℂ) (seed : CompactLogTest)
    (y : ℂ → ℂ)
    (hpin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖cardinalSum nodes seed y
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721) :
    ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt (cardinalOwner nodes seed y)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721 := by
  intro sigma hsigma t
  rw [laplaceAt_cardinalOwner]
  exact hpin sigma hsigma t

/-- Record 2722C: the wired row-B contradiction with the three black-box
strip premises replaced by the transport data: two identification
equalities (`hbase`, `hcorr`, naming the strip owners as the concrete
cardinal owners) and three pins `hcontractPin`/`hquarticPin`/
`hquadraticPin` on the explicit cardinal sums — exactly the
record-2720 certified inequalities (artifact row B, `q*(64) <= q`,
`C4* <= C4`, `C2* <= C2`), kept as named hypotheses per the proxy-tie
doctrine and machine-bound by `scripts/check_strip_transport_2722c.py`.
The parent `fourPointContradictionRowBWired2721C` is untouched
(2ab doctrine).  No wired hypothesis is removed by this record: the
strip obligation moves from an abstract owner to a concrete finite
sum.  No producer GO, no RH claim. -/
theorem fourPointContradictionRowBWired2722C
    (nodesB nodesC : Finset ℂ) (seed : CompactLogTest)
    (yB yC : ℂ → ℂ)
    (base correction : CompactLogTest) (rho : sourceNontrivialZeroSet)
    {B : Real}
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hvanish : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (selectedOwner base correction 3).sourceTest)
    (hsupport : Function.support
      (selectedOwner base correction 3).sourceTest.test ⊆ Set.Ioo (-B) B)
    (hbase : base = cardinalOwner nodesB seed yB)
    (hcorr : correction = cardinalOwner nodesC seed yC)
    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, 64 ≤ |t| →
        ‖cardinalSum nodesB seed yB
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721)
    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 * ‖cardinalSum nodesB seed yB
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721)
    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 * ‖cardinalSum nodesC seed yC
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction 3).sourceTest rho.1).involution.convolution
            (selectedOwner base correction 3).sourceTest) +
        ICgate (((selectedOwner base correction 3).sourceTest).involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            (selectedOwner base correction 3).sourceTest rho.1))) +
      24 ^ 2 * ICgate
        (((selectedOwner base correction 3).sourceTest).convolutionSquare) ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction 3).sourceTest rho.1)
            (selectedOwner base correction 3).sourceTest 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False := by
  refine fourPointContradictionRowBWired2721C base correction rho hNorm hIm
      hvanish hsupport ?_ ?_ ?_ hgate24 hprefix
  · rw [hbase]
    exact hcontractOfCardinalPin nodesB seed yB hcontractPin
  · rw [hbase]
    exact hquarticOfCardinalPin nodesB seed yB hquarticPin
  · rw [hcorr]
    exact hquadraticOfCardinalPin nodesC seed yC hquadraticPin

end

end C1StripTransport2722C
end Source
end ConnesWeilRH
