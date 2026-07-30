/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle

/-!
# Balanced polar first-jet recurrence

Proof 665 leaves a physical cocycle with one unpolarized detector compression.
This module removes that last mixed gauge before any estimate is taken.

Write

```text
R_S = G_S^(-1/2),
L_S = R_S G_S,
D_S = U_S^dagger W U_S,
F_S = FirstJetPhysical_S,
B_0 = J^dagger W J.
```

The unpolarized frame is `K_S = U_S L_S`, so

```text
K_S^dagger W K_S = L_S D_S L_S
```

and the two inverse identities for `L_S` and `R_S` turn the first gauge
commutator into `[L_S,D_S]`.  Hence Proof 665's five-term kernel is exactly

```text
Z_S = F_S L_S + [L_S,D_S+B_0].
```

For an adjacent suffix define

```text
H_(p,S) = L_(p::S) R_S = (1+q_p) T_(p,S),
P_S = B_0 + D_S - F_S.
```

Both endpoint gauges then cancel inside the complete column:

```text
[Z_(p::S)-H_(p,S)Z_S]R_S
  = H_(p,S)P_S-P_(p::S)H_(p,S)
    +L_(p::S)(D_(p::S)-D_S)R_S.
```

This is an exact old-carrier recurrence.  It does not bound the three terms
on the right separately and does not close Bone 1A.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarFirstJetRecurrence

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPhysicalCocycle
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedProjectionRawLedger
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarGaugeNormalForm
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

/-! ## Polar compression of the unnormalized frame -/

/-- The frame gauge `L_S` is self-adjoint.  The proof uses only that it is
the two-sided inverse of the self-adjoint coframe square root `R_S`; it does
not unfold the continuous functional calculus square root. -/
theorem suffixActualBandMetricFrameGauge_adjoint_eq
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixActualBandMetricFrameGauge lambda S)† =
      suffixActualBandMetricFrameGauge lambda S := by
  have hcoframeSelf := parameterizedSoninGramInvSqrt_isSelfAdjoint
    lambda 1 S (by norm_num)
  have hadjointInverse :
      (suffixActualBandMetricFrameGauge lambda S)† ∘L
          suffixActualBandMetricCoframeSqrt lambda S =
        ContinuousLinearMap.id ℂ
          (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) := by
    have h := congrArg ContinuousLinearMap.adjoint
      (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id,
      suffixActualBandMetricCoframeSqrt,
      hcoframeSelf.adjoint_eq] using h
  apply ContinuousLinearMap.ext
  intro x
  have hcoframeFrameAt := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  have hadjointAt := congrArg
    (fun operator : SourceOp lambda =>
      operator (suffixActualBandMetricFrameGauge lambda S x))
    hadjointInverse
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hcoframeFrameAt hadjointAt
  rw [hcoframeFrameAt] at hadjointAt
  exact hadjointAt

/-- The unnormalized detector compression is the polar detector compression
with one frame gauge on each side: `A_S=L_S D_S L_S`. -/
theorem
    suffixActualBandFrameDetectorCompression_eq_frameGauge_polar_frameGauge
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFrameDetectorCompression owner lambda S =
      suffixActualBandMetricFrameGauge lambda S ∘L
        suffixPolarDetectorCompression owner lambda S ∘L
          suffixActualBandMetricFrameGauge lambda S := by
  have hframe :
      suffixActualBandFrame lambda S =
        newSuffixFrame lambda S ∘L
          suffixActualBandMetricFrameGauge lambda S := by
    change parameterizedSoninFrame lambda 1 S = _
    exact
      (newSuffixFrame_comp_metricFrameGauge_eq_parameterizedSoninFrame
        lambda S).symm
  rw [suffixActualBandFrameDetectorCompression, hframe,
    ContinuousLinearMap.adjoint_comp,
    suffixActualBandMetricFrameGauge_adjoint_eq,
    suffixPolarDetectorCompression]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The mixed unpolarized/coframe commutator from Proof 665 is exactly the
polar gauge commutator `[L_S,D_S]`. -/
theorem
    suffixActualBandFrameCoframeCommutator_eq_polarGaugeCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFrameDetectorCompression owner lambda S ∘L
          suffixActualBandMetricCoframeSqrt lambda S -
        suffixActualBandMetricCoframeSqrt lambda S ∘L
          suffixActualBandFrameDetectorCompression owner lambda S =
      suffixActualBandMetricFrameGauge lambda S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda S ∘L
          suffixActualBandMetricFrameGauge lambda S := by
  rw [suffixActualBandFrameDetectorCompression_eq_frameGauge_polar_frameGauge]
  apply ContinuousLinearMap.ext
  intro x
  have hframeCoframeAt := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  have hcoframeFrameAt := congrArg
    (fun operator : SourceOp lambda =>
      operator
        (suffixPolarDetectorCompression owner lambda S
          (suffixActualBandMetricFrameGauge lambda S x)))
    (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframeCoframeAt
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hcoframeFrameAt
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply]
  rw [hframeCoframeAt, hcoframeFrameAt]

/-! ## Reduced physical cocycle -/

/-- The polar first-jet form of Proof 665's physical cocycle. -/
noncomputable def suffixActualBandBalancedPolarFirstJetKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandPhysicalFirstJetResponse owner lambda S ∘L
      suffixActualBandMetricFrameGauge lambda S +
    (suffixActualBandMetricFrameGauge lambda S ∘L
        (suffixPolarDetectorCompression owner lambda S +
          suffixActualBandFixedSourceDetectorCompression owner lambda) -
      (suffixPolarDetectorCompression owner lambda S +
          suffixActualBandFixedSourceDetectorCompression owner lambda) ∘L
        suffixActualBandMetricFrameGauge lambda S)

/-- Proof 665's five-term kernel equals the physical first jet plus the
single combined polar commutator `[L_S,D_S+B_0]`. -/
theorem suffixActualBandBalancedPhysicalCocycleKernel_eq_polarFirstJet
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPhysicalCocycleKernel owner lambda S =
      suffixActualBandBalancedPolarFirstJetKernel owner lambda S := by
  rw [suffixActualBandBalancedPhysicalCocycleKernel,
    suffixActualBandBalancedGaugeCommutatorResponse,
    suffixActualBandBalancedPolarFirstJetKernel,
    suffixActualBandFrameCoframeCommutator_eq_polarGaugeCommutator]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    map_add]
  abel

/-- The defect `P_S=B_0+D_S-F_S` which participates in the adjacent
old-carrier coboundary. -/
noncomputable def suffixActualBandPolarFirstJetDefectKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandFixedSourceDetectorCompression owner lambda +
    suffixPolarDetectorCompression owner lambda S -
      suffixActualBandPhysicalFirstJetResponse owner lambda S

/-- A one-suffix factorization adapted to the adjacent recurrence:
`Z_S=L_S(D_S+B_0)-P_S L_S`. -/
theorem suffixActualBandBalancedPhysicalCocycleKernel_eq_frameGauge_sub_defect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPhysicalCocycleKernel owner lambda S =
      suffixActualBandMetricFrameGauge lambda S ∘L
          (suffixPolarDetectorCompression owner lambda S +
            suffixActualBandFixedSourceDetectorCompression owner lambda) -
        suffixActualBandPolarFirstJetDefectKernel owner lambda S ∘L
          suffixActualBandMetricFrameGauge lambda S := by
  rw [suffixActualBandBalancedPhysicalCocycleKernel_eq_polarFirstJet,
    suffixActualBandBalancedPolarFirstJetKernel,
    suffixActualBandPolarFirstJetDefectKernel]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    map_add]
  abel

/-! ## Adjacent old-carrier recurrence -/

/-- The complete old-carrier transition gauge
`H_(p,S)=L_(p::S)R_S`. -/
noncomputable def suffixActualBandOldCarrierTransitionGauge
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
    suffixActualBandMetricCoframeSqrt lambda S

/-- The old-carrier transition gauge is exactly the actual compressed Schur
transition before division by its upper Euler scalar. -/
theorem suffixActualBandOldCarrierTransitionGauge_eq_smul_transition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandOldCarrierTransitionGauge lambda p S =
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        suffixEulerFrameTransition lambda p S := by
  have hscalar :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (add_pos_of_pos_of_nonneg zero_lt_one
        (ccm24PrimeEulerCoefficient_nonneg p))
  rw [suffixActualBandOldCarrierTransitionGauge,
    suffixEulerFrameTransition_eq_polarGauge]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, smul_smul]
  rw [mul_inv_cancel₀ hscalar, one_smul]

/-- The transition gauge sends the old frame gauge to the new one exactly:
`H_(p,S)L_S=L_(p::S)`. -/
theorem suffixActualBandOldCarrierTransitionGauge_comp_frameGauge
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
        suffixActualBandMetricFrameGauge lambda S =
      suffixActualBandMetricFrameGauge lambda (p :: S) := by
  rw [suffixActualBandOldCarrierTransitionGauge,
    ContinuousLinearMap.comp_assoc,
    suffixActualBandMetricCoframeSqrt_comp_frameGauge,
    ContinuousLinearMap.comp_id]

private theorem oldCarrierRecurrence_identity
    {A : Type*} [Ring A]
    (newGauge oldGauge oldCoframe newDetector oldDetector base
      newDefect oldDefect : A)
    (hcoframeFrame : oldCoframe * oldGauge = 1)
    (hframeCoframe : oldGauge * oldCoframe = 1) :
    ((newGauge * (newDetector + base) - newDefect * newGauge) -
          (newGauge * oldCoframe) *
            (oldGauge * (oldDetector + base) - oldDefect * oldGauge)) *
        oldCoframe =
      (newGauge * oldCoframe) * oldDefect -
        newDefect * (newGauge * oldCoframe) +
        newGauge * (newDetector - oldDetector) * oldCoframe := by
  calc
    ((newGauge * (newDetector + base) - newDefect * newGauge) -
          (newGauge * oldCoframe) *
            (oldGauge * (oldDetector + base) - oldDefect * oldGauge)) *
        oldCoframe =
      newGauge * (newDetector + base) * oldCoframe -
        newDefect * (newGauge * oldCoframe) -
        newGauge * (oldCoframe * oldGauge) *
          (oldDetector + base) * oldCoframe +
        (newGauge * oldCoframe) * oldDefect *
          (oldGauge * oldCoframe) := by
      noncomm_ring
    _ = (newGauge * oldCoframe) * oldDefect -
          newDefect * (newGauge * oldCoframe) +
          newGauge * (newDetector - oldDetector) * oldCoframe := by
      rw [hcoframeFrame, hframeCoframe]
      noncomm_ring

/-- The complete adjacent physical column after both old endpoint gauges
have been cancelled.  The polar detector increment remains signed and inside
the same column. -/
theorem suffixActualBandBalancedPhysicalCocycle_oldCarrierRecurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandBalancedPhysicalCocycleKernel
          owner lambda (p :: S) -
        suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixActualBandBalancedPhysicalCocycleKernel owner lambda S) ∘L
        suffixActualBandMetricCoframeSqrt lambda S =
      suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixActualBandPolarFirstJetDefectKernel owner lambda S -
        suffixActualBandPolarFirstJetDefectKernel
            owner lambda (p :: S) ∘L
          suffixActualBandOldCarrierTransitionGauge lambda p S +
        suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
          (suffixPolarDetectorCompression owner lambda (p :: S) -
            suffixPolarDetectorCompression owner lambda S) ∘L
          suffixActualBandMetricCoframeSqrt lambda S := by
  rw [suffixActualBandBalancedPhysicalCocycleKernel_eq_frameGauge_sub_defect,
    suffixActualBandBalancedPhysicalCocycleKernel_eq_frameGauge_sub_defect]
  have hcoframeFrame :
      suffixActualBandMetricCoframeSqrt lambda S *
          suffixActualBandMetricFrameGauge lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricCoframeSqrt_comp_frameGauge lambda S)
  have hframeCoframe :
      suffixActualBandMetricFrameGauge lambda S *
          suffixActualBandMetricCoframeSqrt lambda S = 1 := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.one_def] using
        (suffixActualBandMetricFrameGauge_comp_coframeSqrt lambda S)
  simpa only [suffixActualBandOldCarrierTransitionGauge,
    ContinuousLinearMap.mul_def] using
      (oldCarrierRecurrence_identity
        (newGauge := suffixActualBandMetricFrameGauge lambda (p :: S))
        (oldGauge := suffixActualBandMetricFrameGauge lambda S)
        (oldCoframe := suffixActualBandMetricCoframeSqrt lambda S)
        (newDetector := suffixPolarDetectorCompression owner lambda (p :: S))
        (oldDetector := suffixPolarDetectorCompression owner lambda S)
        (base := suffixActualBandFixedSourceDetectorCompression owner lambda)
        (newDefect :=
          suffixActualBandPolarFirstJetDefectKernel owner lambda (p :: S))
        (oldDefect := suffixActualBandPolarFirstJetDefectKernel owner lambda S)
        hcoframeFrame hframeCoframe)

/-- The named right side of the old-carrier recurrence. -/
noncomputable def suffixActualBandPolarFirstJetRecurrenceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
      suffixActualBandPolarFirstJetDefectKernel owner lambda S -
    suffixActualBandPolarFirstJetDefectKernel owner lambda (p :: S) ∘L
      suffixActualBandOldCarrierTransitionGauge lambda p S +
    suffixActualBandMetricFrameGauge lambda (p :: S) ∘L
      (suffixPolarDetectorCompression owner lambda (p :: S) -
        suffixPolarDetectorCompression owner lambda S) ∘L
      suffixActualBandMetricCoframeSqrt lambda S

/-- Proof 665's complete source column is exactly the old-carrier polar
first-jet recurrence column. -/
theorem suffixActualBandBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandBalancedPhysicalCocycleColumn owner lambda p S =
      suffixActualBandPolarFirstJetRecurrenceColumn owner lambda p S := by
  have htransport :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
          (suffixEulerFrameTransition lambda p S ∘L
            suffixActualBandBalancedPhysicalCocycleKernel owner lambda S) =
        suffixActualBandOldCarrierTransitionGauge lambda p S ∘L
          suffixActualBandBalancedPhysicalCocycleKernel owner lambda S := by
    rw [suffixActualBandOldCarrierTransitionGauge_eq_smul_transition]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply]
  rw [suffixActualBandBalancedPhysicalCocycleColumn,
    suffixActualBandAdjacentPhysicalCocycleKernel,
    suffixActualBandPolarFirstJetRecurrenceColumn,
    htransport]
  exact suffixActualBandBalancedPhysicalCocycle_oldCarrierRecurrence
    owner lambda p S

/-! ## Route-scaled same-constant readback -/

/-- The route-scaled old-carrier polar first-jet recurrence column. -/
noncomputable def routeScaledBalancedPolarFirstJetRecurrenceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) : SourceOp unitSoninScale :=
  ((Real.sqrt (ccm24PrimeEulerCoefficient index.prime) : ℂ)⁻¹) •
    suffixActualBandPolarFirstJetRecurrenceColumn
      owner unitSoninScale index.prime index.suffix

/-- The Proof 665 route column and the old-carrier recurrence column are the
same operator, not merely norm comparable. -/
theorem routeScaledBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routeScaledBalancedPhysicalCocycleColumn owner index =
      routeScaledBalancedPolarFirstJetRecurrenceColumn owner index := by
  rw [routeScaledBalancedPhysicalCocycleColumn,
    routeScaledBalancedPolarFirstJetRecurrenceColumn,
    suffixActualBandBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence]

/-- One bound for all route-valid old-carrier recurrence columns. -/
def SuffixBalancedPolarFirstJetRecurrenceRouteUniformScaledBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledBalancedPolarFirstJetRecurrenceColumn owner index‖ ≤ bound

/-- Proof 665's physical-cocycle bound and the old-carrier recurrence bound
are the same statement with the same constant. -/
theorem physicalCocycleRouteUniformScaledBound_iff_polarFirstJetRecurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixBalancedPhysicalCocycleRouteUniformScaledBound owner bound ↔
      SuffixBalancedPolarFirstJetRecurrenceRouteUniformScaledBound
        owner bound := by
  constructor
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [← routeScaledBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence]
    exact data.2 index
  · intro data
    refine ⟨data.1, ?_⟩
    intro index
    rw [routeScaledBalancedPhysicalCocycleColumn_eq_polarFirstJetRecurrence]
    exact data.2 index

/-- Bone 1A is same-constant equivalent to the route-uniform old-carrier
polar first-jet recurrence.  The theorem is a reduction, not its producer. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_polarFirstJetRecurrence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixBalancedPolarFirstJetRecurrenceRouteUniformScaledBound
          owner bound := by
  rw [exists_routeUniformScaledCompleteTargetBound_iff_physicalCocycle]
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (physicalCocycleRouteUniformScaledBound_iff_polarFirstJetRecurrence
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (physicalCocycleRouteUniformScaledBound_iff_polarFirstJetRecurrence
        owner bound).mpr data⟩

/-! ## Harmless transition factor -/

/-- The complete old-carrier transition gauge has a uniform norm bound of
two.  The remaining difficulty is therefore the signed recurrence, not this
adjacent transport factor. -/
theorem suffixActualBandOldCarrierTransitionGauge_norm_le_two
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandOldCarrierTransitionGauge lambda p S‖ ≤ 2 := by
  have hdenom : 0 ≤ 1 + ccm24PrimeEulerCoefficient p :=
    add_nonneg zero_le_one (ccm24PrimeEulerCoefficient_nonneg p)
  have hcast :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) =
        ((1 + ccm24PrimeEulerCoefficient p : ℝ) : ℂ) := by
    norm_num
  rw [suffixActualBandOldCarrierTransitionGauge_eq_smul_transition]
  calc
    ‖(1 + (ccm24PrimeEulerCoefficient p : ℂ)) •
        suffixEulerFrameTransition lambda p S‖ ≤
        ‖(1 + (ccm24PrimeEulerCoefficient p : ℂ))‖ *
          ‖suffixEulerFrameTransition lambda p S‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = (1 + ccm24PrimeEulerCoefficient p) *
          ‖suffixEulerFrameTransition lambda p S‖ := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdenom]
    _ ≤ (1 + ccm24PrimeEulerCoefficient p) * 1 :=
      mul_le_mul_of_nonneg_left
        (suffixEulerFrameTransition_norm_le_one lambda p S) hdenom
    _ = 1 + ccm24PrimeEulerCoefficient p := by ring
    _ ≤ 2 := by
      linarith [ccm24PrimeEulerCoefficient_lt_one p]

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBalancedPolarFirstJetRecurrence
end CCM25Concrete
end Source
end ConnesWeilRH
