/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SemilocalFourierProjectionUnitaryBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24ReflectedCompactRoot

/-!
# C1: finite-S detector second-support bridge

This leaf transfers one *detector-level* compact-root owner from the
archimedean second support to the actual finite-S second support.

The transfer is exact.  If `H_S = T_S H_infinity T_S^{-1}` and `D` is the
selected convolution detector, then the Euler-transport covariance of `D`
and the Hardy--Titchmarsh covariance of `T_S` imply

```text
H_S D H_S = H_infinity D H_infinity.
```

Consequently the existing reflected compact-root pair can be sandwiched by
`H_S` and owns the target oriented second-support crossing.

This is deliberately narrower than F1'.  It proves neither the active-order
Hilbert--Schmidt factor nor the signed root-commutator ledger
`C† [C, K_S]`; those still require separate analytic producers.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SemilocalDetectorSecondSupportBridge

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactConvolutionSupport
open CC20Concrete.CompactRootHalfLinePair
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24RadialBoundaryPairTransport
open CCM25Concrete.CCM24ReflectedCompactRoot
open C1SemilocalFourierProjectionUnitaryBridge
open C1SemilocalHardyTitchmarshUnitarityReduction
open MeasureTheory
open scoped InnerProduct

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-! ## Euler-invariant detector conjugation -/

/-- Conjugating the selected detector by the finite-S Hardy--Titchmarsh
involution gives exactly the same reflected detector as in the source case.
The proof is finite Euler algebra, not a spectral approximation. -/
theorem semilocalHardyTitchmarsh_detector_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap ∘L
        detectorOperator owner ∘L
          (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
      archimedeanHardyTitchmarshOperator ∘L detectorOperator owner ∘L
        archimedeanHardyTitchmarshOperator := by
  let T : Op := (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap
  let Ti : Op := (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap
  let Harch : Op := archimedeanHardyTitchmarshOperator
  let D : Op := detectorOperator owner
  have hfactor :
      (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap =
        (T ∘L Harch) ∘L Ti := by
    dsimp only [T, Harch, Ti, archimedeanHardyTitchmarshOperator]
    exact ccm24SemilocalHardyTitchmarsh_toContinuousLinearMap S
  have hDT : D * T = T * D := by
    dsimp only [D, T]
    change detectorOperator owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        detectorOperator owner
    exact detectorOperator_comp_finiteEulerTransport owner S
  have hTiT : Ti * T = 1 := by
    dsimp only [Ti, T]
    change (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (1 : Op)
    exact ccm24FiniteEulerTransport_symm_comp_toContinuousLinearMap S
  have hTTi : T * Ti = 1 := by
    dsimp only [Ti, T]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap =
      (1 : Op)
    exact ccm24FiniteEulerTransport_comp_symm_toContinuousLinearMap S
  have hHT : Harch * T = T.adjoint * Harch := by
    dsimp only [Harch, T, archimedeanHardyTitchmarshOperator]
    change (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        (ccm24ArchimedeanHardyTitchmarsh : Op)
    exact archimedeanHardyTitchmarsh_comp_finiteEulerTransport S
  have hTH : T * Harch = Harch * T.adjoint := by
    dsimp only [Harch, T, archimedeanHardyTitchmarshOperator]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        (ccm24ArchimedeanHardyTitchmarsh : Op) =
      (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint
    exact ccm24FiniteEulerTransport_comp_archimedeanHardyTitchmarsh S
  have hTadjD : T.adjoint * D = D * T.adjoint := by
    dsimp only [T, D]
    change (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        detectorOperator owner =
      detectorOperator owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint
    exact finiteEulerTransportAdjoint_comp_detector owner S
  have hDTAt (u : finiteSCarrier) : D (T u) = T (D u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hDT
  have hTiTAt (u : finiteSCarrier) : Ti (T u) = u := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun operator : Op => operator u) hTiT
  have hTTiAt (u : finiteSCarrier) : T (Ti u) = u := by
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
      congrArg (fun operator : Op => operator u) hTTi
  have hHTAt (u : finiteSCarrier) : Harch (T u) = T.adjoint (Harch u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hHT
  have hTHAt (u : finiteSCarrier) : T (Harch u) = Harch (T.adjoint u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hTH
  have hTadjDAt (u : finiteSCarrier) : T.adjoint (D u) = D (T.adjoint u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun operator : Op => operator u) hTadjD
  have hTiDTAt (u : finiteSCarrier) : Ti (D (T u)) = D u := by
    calc
      Ti (D (T u)) = Ti (T (D u)) := congrArg Ti (hDTAt u)
      _ = D u := hTiTAt (D u)
  have hBcommAt (u : finiteSCarrier) :
      Harch (D (Harch (T u))) = T (Harch (D (Harch u))) := by
    calc
      Harch (D (Harch (T u))) =
          Harch (D (T.adjoint (Harch u))) := by
        exact congrArg (fun v => Harch (D v)) (hHTAt u)
      _ = Harch (T.adjoint (D (Harch u))) := by
        exact congrArg Harch (hTadjDAt (Harch u)).symm
      _ = T (Harch (D (Harch u))) := (hTHAt (D (Harch u))).symm
  rw [hfactor]
  apply ContinuousLinearMap.ext
  intro u
  change T (Harch (Ti (D (T (Harch (Ti u)))))) = Harch (D (Harch u))
  calc
    T (Harch (Ti (D (T (Harch (Ti u)))))) =
        T (Harch (D (Harch (Ti u)))) := by
      exact congrArg (fun v => T (Harch v)) (hTiDTAt (Harch (Ti u)))
    _ = Harch (D (Harch (T (Ti u)))) := (hBcommAt (Ti u)).symm
    _ = Harch (D (Harch u)) := by
      exact congrArg (fun v => Harch (D (Harch v))) (hTTiAt u)

/-! ## Target second-support compact-root owner -/

/-- The target oriented second-support crossing is the semilocal
Hardy--Titchmarsh sandwich of the same radial reflected-detector crossing used
on the source side. -/
theorem targetSecondSupportOrientedCrossing_eq_semilocalHardyTitchmarsh_conjugation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    cc20OrientedBoundaryCrossing
        (targetFourierSupportProjection lambda family) (detectorOperator owner) =
      (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap ∘L
        cc20OrientedBoundaryCrossing (radialSupportProjection lambda)
          (hardyTitchmarshConjugatedDetector owner) ∘L
        (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap := by
  let HS : Op :=
    (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap
  let E : Op := radialSupportProjection lambda
  let D : Op := detectorOperator owner
  let B : Op := hardyTitchmarshConjugatedDetector owner
  have hQ : targetFourierSupportProjection lambda family = HS * E * HS := by
    dsimp only [HS, E]
    simpa only [ContinuousLinearMap.mul_def] using
      targetFourierSupportProjection_eq_unitary_conjugate lambda family
  have hHSsq : HS * HS = 1 := by
    dsimp only [HS]
    simpa only [ContinuousLinearMap.mul_def] using
      ccm24SemilocalHardyTitchmarsh_comp_self family.visiblePrimes
  have hB : HS * D * HS = B := by
    dsimp only [HS, D, B]
    simpa only [ContinuousLinearMap.mul_def] using
      semilocalHardyTitchmarsh_detector_conjugation owner family.visiblePrimes
  rw [hQ]
  unfold cc20OrientedBoundaryCrossing
  change (1 - HS * E * HS) * D * (HS * E * HS) =
    HS * ((1 - E) * B * E) * HS
  calc
    (1 - HS * E * HS) * D * (HS * E * HS) =
        D * HS * E * HS - HS * E * HS * D * HS * E * HS := by
      noncomm_ring
    _ = (HS * HS) * D * HS * E * HS -
        HS * E * HS * D * HS * E * HS := by
      rw [hHSsq]
      simp
    _ = HS * ((1 - E) * (HS * D * HS) * E) * HS := by
      noncomm_ring
    _ = HS * ((1 - E) * B * E) * HS := by rw [hB]

/-- The existing reflected compact-root pair, now sandwiched by the actual
finite-S unitary, is a Hilbert--Schmidt-pair owner for the target oriented
second-support crossing. -/
noncomputable def targetSecondSupportCompactRootPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))
      globalBasis :=
  (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis).boundedSandwich outputBasis
      (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap
      (ccm24SemilocalHardyTitchmarsh family.visiblePrimes).toContinuousLinearMap

/-- The target compact-root pair has exactly the target oriented
second-support crossing as its trace product. -/
theorem targetSecondSupportCompactRootPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (targetSecondSupportCompactRootPairData owner lambda family a c negativeBasis
      positiveBasis outputBasis globalBasis).traceProduct =
      cc20OrientedBoundaryCrossing
        (targetFourierSupportProjection lambda family) (detectorOperator owner) := by
  unfold targetSecondSupportCompactRootPairData
  rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  rw [reflectedTranslatedCompactRootPairData_traceProduct_eq_radialCrossing
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis]
  exact (targetSecondSupportOrientedCrossing_eq_semilocalHardyTitchmarsh_conjugation
    owner lambda family).symm

/-- The target oriented second-support crossing is trace-class along every
named global basis, with an explicit compact-root pair owner.  This is a
detector-level legality result only; it is not the root-commutator S2 claim. -/
theorem targetSecondSupportOrientedCrossing_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    IsTraceClassAlong globalBasis
      (cc20OrientedBoundaryCrossing
        (targetFourierSupportProjection lambda family) (detectorOperator owner)) := by
  rw [← targetSecondSupportCompactRootPairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis]
  exact (targetSecondSupportCompactRootPairData owner lambda family a c negativeBasis
    positiveBasis outputBasis globalBasis).traceProduct_isTraceClassAlong

/-- Both orientations of the detector-level target second-support boundary are
trace-class.  This does not decompose or close the signed root-commutator
ledger needed by F1'. -/
theorem targetSecondSupportCommutator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    IsTraceClassAlong globalBasis
      (cc20Commutator (targetFourierSupportProjection lambda family)
        (detectorOperator owner)) := by
  let crossing := cc20OrientedBoundaryCrossing
    (targetFourierSupportProjection lambda family) (detectorOperator owner)
  have hcrossing : IsTraceClassAlong globalBasis crossing :=
    targetSecondSupportOrientedCrossing_isTraceClassAlong owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (targetFourierSupportProjection lambda family) (detectorOperator owner)
    (targetFourierSupportProjection_isStarProjection lambda family).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  exact isTraceClassAlong_sub globalBasis _ _
    (isTraceClassAlong_adjoint globalBasis crossing hcrossing) hcrossing

end C1SemilocalDetectorSecondSupportBridge
end Source
end ConnesWeilRH
