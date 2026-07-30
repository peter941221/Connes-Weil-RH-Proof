/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawDouglasReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientLossKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor

/-!
# Old-carrier reduction for the raw physical row

Proof 574 makes the first concrete reduction for the physical producer.  Both
the packed physical analysis and the raw four-term row have the old suffix
frame as a common right factor.  The remaining source estimate can therefore
be stated on the ambient finite-S carrier.

This module supplies the reduction and a sufficient full old-carrier Douglas
producer.  It does not assert that the full old-carrier estimate holds.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientLossKernel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSDouglasFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open RCLike

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The old-carrier physical analysis -/

/-- The packed physical analysis before the old suffix frame is applied. -/
noncomputable def suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] suffixEulerFrameAmbientBoundaryCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      finiteSCarrier finiteSCarrier).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)).prod
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transport))

@[simp]
theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier) :
    suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y =
      WithLp.toLp 2
        ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) y,
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) y) := by
  rfl

/-! The old-carrier map keeps the two physical channels orthogonal. -/

theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_normSq_eq_channels
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier) :
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) y‖ ^ 2 +
        ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transport) y‖ ^ 2 := by
  rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_oldFrame_normSq_eq_actual_channels
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
        ((suffixEulerFrameSchurStep lambda p S).oldFrame x)‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x)‖ ^ 2 +
        ‖ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary x‖ ^ 2 := by
  rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_normSq_eq_channels]
  have hboundary := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => T x)
    (suffixEulerFrameSchurStep lambda p S).boundaryDagger_eq_adjoint
  have hboundaryPoint :
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transport)
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x) =
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary x := by
    simpa only [rectangularBoundaryCompressionDagger,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] using hboundary
  rw [hboundaryPoint]

/-! The old-carrier Gram operator -/

/-- The two-channel old-carrier analysis has an exact Gram normal form.  The
ambient loss is the one-prime ambient co-defect, while the second channel is
the orthogonal complement of the new suffix-frame range. -/
theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_adjoint_comp_self_eq_id_sub_transport_newProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
      ContinuousLinearMap.id ℂ finiteSCarrier -
        normalizedPrimeEulerFrameTransport p ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          (ContinuousLinearMap.adjoint
            (normalizedPrimeEulerFrameTransport p)) := by
  let transport := normalizedPrimeEulerFrameTransport p
  let newFrame := (suffixEulerFrameSchurStep lambda p S).newFrame
  let projection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    newFrame ∘L ContinuousLinearMap.adjoint newFrame
  let complement : finiteSCarrier →L[ℂ] finiteSCarrier :=
    ContinuousLinearMap.id ℂ finiteSCarrier - projection
  have hnewIsometry :
      ContinuousLinearMap.adjoint newFrame ∘L newFrame =
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [newFrame] using
      (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hprojectionAdj : (projection)† = projection := by
    simp only [projection, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hprojectionSq : projection ∘L projection = projection := by
    apply ContinuousLinearMap.ext
    intro z
    have h := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        newFrame (T (ContinuousLinearMap.adjoint newFrame z))) hnewIsometry
    simpa only [projection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hcomplementAdj : (complement)† = complement := by
    have hadjointSub (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
        (A - B)† = A† - B† := by
      apply ContinuousLinearMap.ext
      intro z
      exact ext_inner_right ℂ fun w => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    change (ContinuousLinearMap.id ℂ finiteSCarrier - projection)† =
      ContinuousLinearMap.id ℂ finiteSCarrier - projection
    rw [hadjointSub, ContinuousLinearMap.adjoint_id, hprojectionAdj]
  have hcomplementSq : complement ∘L complement = complement := by
    apply ContinuousLinearMap.ext
    intro z
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T z)
      hprojectionSq
    simp only [complement, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub] at h ⊢
    rw [h]
    abel
  have hambient :
      primeEulerAmbientLossFactor p ∘L
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) =
        ContinuousLinearMap.id ℂ finiteSCarrier -
          transport ∘L ContinuousLinearMap.adjoint transport := by
    rw [← normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_factor]
    rfl
  have hgram :
      (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
        primeEulerAmbientLossFactor p ∘L
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) +
          transport ∘L complement ∘L ContinuousLinearMap.adjoint transport := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hambientInner :
        ⟪(ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) y,
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) x⟫_ℂ =
          ⟪y, (primeEulerAmbientLossFactor p ∘L
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) x⟫_ℂ := by
      simpa only [ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_apply] using
        (ContinuousLinearMap.adjoint_inner_right
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) y
          ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) x)).symm
    have hcomplementInner :
        ⟪complement (ContinuousLinearMap.adjoint transport y),
            complement (ContinuousLinearMap.adjoint transport x)⟫_ℂ =
          ⟪y, (transport ∘L complement ∘L
            ContinuousLinearMap.adjoint transport) x⟫_ℂ := by
      calc
        ⟪complement (ContinuousLinearMap.adjoint transport y),
            complement (ContinuousLinearMap.adjoint transport x)⟫_ℂ =
            ⟪ContinuousLinearMap.adjoint transport y,
              (ContinuousLinearMap.adjoint complement)
                (complement (ContinuousLinearMap.adjoint transport x))⟫_ℂ := by
          exact (ContinuousLinearMap.adjoint_inner_right complement
            (ContinuousLinearMap.adjoint transport y)
            (complement (ContinuousLinearMap.adjoint transport x))).symm
        _ = ⟪ContinuousLinearMap.adjoint transport y,
              complement (complement (ContinuousLinearMap.adjoint transport x))⟫_ℂ := by
          rw [hcomplementAdj]
        _ = ⟪ContinuousLinearMap.adjoint transport y,
              complement (ContinuousLinearMap.adjoint transport x)⟫_ℂ := by
          have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
              T (ContinuousLinearMap.adjoint transport x)) hcomplementSq
          simpa only [ContinuousLinearMap.comp_apply] using congrArg
            (fun z : finiteSCarrier =>
              ⟪ContinuousLinearMap.adjoint transport y, z⟫_ℂ) h
        _ = ⟪y, (transport ∘L complement ∘L
              ContinuousLinearMap.adjoint transport) x⟫_ℂ := by
          simpa only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.adjoint_adjoint] using
            (ContinuousLinearMap.adjoint_inner_right
              (ContinuousLinearMap.adjoint transport) y
              (complement (ContinuousLinearMap.adjoint transport x))).symm
    calc
      ⟪y, ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
            suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) x⟫_ℂ =
          ⟪suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y,
            suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S x⟫_ℂ := by
        rw [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪(ContinuousLinearMap.adjoint
            (primeEulerAmbientLossFactor p)) y,
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) x⟫_ℂ +
          ⟪complement (ContinuousLinearMap.adjoint transport y),
            complement (ContinuousLinearMap.adjoint transport x)⟫_ℂ := by
        simp only [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply,
          suffixEulerFrameSchurStep, transport, newFrame, complement, projection,
          ContinuousLinearMap.comp_apply, WithLp.prod_inner_apply]
      _ = ⟪y, (primeEulerAmbientLossFactor p ∘L
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) x⟫_ℂ +
          ⟪y, (transport ∘L complement ∘L
            ContinuousLinearMap.adjoint transport) x⟫_ℂ := by
        rw [hambientInner, hcomplementInner]
      _ = ⟪y, (primeEulerAmbientLossFactor p ∘L
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) +
          transport ∘L complement ∘L ContinuousLinearMap.adjoint transport) x⟫_ℂ := by
        simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rw [hgram, hambient]
  apply ContinuousLinearMap.ext
  intro x
  simp only [complement, projection, transport,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    map_sub]
  abel

/-- The closed-form old-carrier Gram operator is positive because it is the
Gram operator of the packed analysis itself. -/
theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_id_sub_transport_newProjection_nonneg
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    0 ≤ ContinuousLinearMap.id ℂ finiteSCarrier -
      normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p)) := by
  rw [← suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_adjoint_comp_self_eq_id_sub_transport_newProjection]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self
      (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S))

/-- Pointwise energy readback from the closed-form old-carrier Gram
operator. -/
theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_normSq_eq_id_sub_transport_newProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier) :
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 =
      re ⟪(ContinuousLinearMap.id ℂ finiteSCarrier -
        normalizedPrimeEulerFrameTransport p ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          (ContinuousLinearMap.adjoint
            (normalizedPrimeEulerFrameTransport p))) y, y⟫_ℂ := by
  calc
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 =
        re ⟪((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) y,
          y⟫_ℂ := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = re ⟪(ContinuousLinearMap.id ℂ finiteSCarrier -
        normalizedPrimeEulerFrameTransport p ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          (ContinuousLinearMap.adjoint
            (normalizedPrimeEulerFrameTransport p))) y, y⟫_ℂ := by
      rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_adjoint_comp_self_eq_id_sub_transport_newProjection]

/-! ## The old-carrier kernel -/

theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_eq_zero_iff_channels_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier) :
    suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y = 0 ↔
      ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) y = 0 ∧
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transport) y = 0 := by
  rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply]
  let equiv := WithLp.prodContinuousLinearEquiv 2 ℂ
    finiteSCarrier finiteSCarrier
  constructor
  · intro hzero
    have hpair := congrArg equiv hzero
    have hpair' :
        ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) y,
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) y) =
          (0, 0) := by
      simpa only [equiv, WithLp.prodContinuousLinearEquiv_symm_apply,
        map_zero, ContinuousLinearEquiv.apply_symm_apply] using hpair
    exact Prod.ext_iff.mp hpair'
  · rintro ⟨hambient, hboundary⟩
    have hpair :
        ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)) y,
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).newFrame) ∘L
            ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) y) =
          (0, 0) := by
      exact Prod.ext hambient hboundary
    have hzero := congrArg equiv.symm hpair
    simpa only [equiv, WithLp.prodContinuousLinearEquiv_symm_apply] using hzero

theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_injective
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    Function.Injective
      (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S) := by
  intro y₁ y₂ hxy
  have hzero :
      suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S (y₁ - y₂) = 0 := by
    simpa only [map_sub] using sub_eq_zero.mpr hxy
  have hchannels :=
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_eq_zero_iff_channels_eq_zero
      lambda p S (y₁ - y₂)).mp hzero
  have hambient :
      ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
          (y₁ - y₂) = 0 := hchannels.1
  have htransportFixed :
      normalizedPrimeEulerFrameTransport p
          (ContinuousLinearMap.adjoint
            (normalizedPrimeEulerFrameTransport p) (y₁ - y₂)) =
        y₁ - y₂ := by
    have hgram := normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_factor p
    have hgramPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T (y₁ - y₂)) hgram
    have hfactorPoint := congrArg
      (fun z : finiteSCarrier => primeEulerAmbientLossFactor p z) hambient
    have hfactorZero :
        primeEulerAmbientLossFactor p
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
              (y₁ - y₂)) = 0 := by
      simpa only [map_zero] using hfactorPoint
    simp only [rectangularAmbientCoDefect, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at hgramPoint
    rw [hfactorZero] at hgramPoint
    exact (sub_eq_zero.mp hgramPoint).symm
  have hboundary :
      (((ContinuousLinearMap.id ℂ finiteSCarrier -
          newSuffixFrame lambda S ∘L
            ContinuousLinearMap.adjoint (newSuffixFrame lambda S)) ∘L
        ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p)) (y₁ - y₂)) = 0 := by
    simpa only [suffixEulerFrameSchurStep, newSuffixFrame] using hchannels.2
  have hnewRange :
      ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p) (y₁ - y₂) =
        newSuffixFrame lambda S
          (ContinuousLinearMap.adjoint (newSuffixFrame lambda S)
            (ContinuousLinearMap.adjoint
              (normalizedPrimeEulerFrameTransport p) (y₁ - y₂))) := by
    have h := hboundary
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] at h
    exact sub_eq_zero.mp h
  let q : sourceSoninCarrier lambda :=
    ContinuousLinearMap.adjoint (newSuffixFrame lambda S)
      (ContinuousLinearMap.adjoint
        (normalizedPrimeEulerFrameTransport p) (y₁ - y₂))
  have holdRange :
      y₁ - y₂ = oldSuffixFrame lambda p S
        (suffixEulerFrameTransition lambda p S q) := by
    have hnewRange' := congrArg
      (fun z : finiteSCarrier => normalizedPrimeEulerFrameTransport p z)
      hnewRange
    have hintertwining := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => T q)
      (suffixEulerFrameSchurStep lambda p S).transport_intertwining
    calc
      y₁ - y₂ = normalizedPrimeEulerFrameTransport p
          (ContinuousLinearMap.adjoint
            (normalizedPrimeEulerFrameTransport p) (y₁ - y₂)) :=
        htransportFixed.symm
      _ = normalizedPrimeEulerFrameTransport p (newSuffixFrame lambda S q) := by
        simpa only [q] using hnewRange'
      _ = oldSuffixFrame lambda p S
          (suffixEulerFrameTransition lambda p S q) := by
        simpa only [suffixEulerFrameSchurStep, oldSuffixFrame,
          newSuffixFrame, suffixEulerFrameTransition,
          ContinuousLinearMap.comp_apply] using hintertwining
  have hcolumn :
      suffixEulerFrameAmbientLossColumn lambda p S
          (suffixEulerFrameTransition lambda p S q) = 0 := by
    rw [suffixEulerFrameAmbientLossColumn]
    change ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
        (oldSuffixFrame lambda p S
          (suffixEulerFrameTransition lambda p S q)) = 0
    rw [← holdRange]
    exact hambient
  have hframeZero :=
    suffixEulerFrameAmbientLossColumn_eq_zero_imp_oldFrame_eq_zero
      lambda p S (suffixEulerFrameTransition lambda p S q) hcolumn
  rw [hframeZero] at holdRange
  exact sub_eq_zero.mp holdRange

/-- The actual two-channel analysis is the old-carrier analysis followed by the
old suffix frame.  The boundary orientation is supplied by the actual
rectangular adjoint field, not by an oblique projection identity. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_eq_oldCarrier_comp_oldFrame
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  apply ContinuousLinearMap.ext
  intro x
  rw [suffixEulerFrameAmbientBoundaryAnalysis_apply]
  change WithLp.toLp 2
      ((ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p))
        ((suffixEulerFrameSchurStep lambda p S).oldFrame x),
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x) =
    suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
      ((suffixEulerFrameSchurStep lambda p S).oldFrame x)
  rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · rfl
  · have hboundary := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => T x)
      (suffixEulerFrameSchurStep lambda p S).boundaryDagger_eq_adjoint
    simpa only [rectangularBoundaryCompressionDagger,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] using hboundary.symm

/-! ## The reduced raw row -/

/-- The raw four-term row pulled back to the old finite-S carrier. -/
noncomputable def suffixActualBandRawPhysicalReducedRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  suffixActualBandRawPhysicalFourTermRow owner lambda p S ∘L
    ContinuousLinearMap.adjoint
      (suffixEulerFrameSchurStep lambda p S).oldFrame

theorem suffixActualBandRawPhysicalReducedRow_eq_zero_of_oldCarrierAnalysis_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier)
    (hy : suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y = 0) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S y = 0 := by
  have hyzero : y = 0 := by
    apply (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_injective
      lambda p S)
    simpa only [map_zero] using hy
  rw [hyzero]
  simp

/-- The raw row is exactly its old-carrier reduction followed by the old
suffix frame.  This uses only the old-frame isometry. -/
theorem suffixActualBandRawPhysicalFourTermRow_eq_reducedRow_comp_oldFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRawPhysicalFourTermRow owner lambda p S =
      suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  rw [suffixActualBandRawPhysicalReducedRow]
  rw [ContinuousLinearMap.comp_assoc,
    (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry,
    ContinuousLinearMap.comp_id]

/-! ## The lower-level Douglas gate -/

/-- A full all-vector Douglas estimate on the old finite-S carrier.  This is a
strong sufficient source theorem for the original physical readout. -/
def SuffixRawOldCarrierDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ y : finiteSCarrier,
      ‖suffixActualBandRawPhysicalReducedRow owner lambda p S y‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2

/-! The estimate is exactly the bounded quotient/readout condition on the
old-carrier range.  This is an equivalence, not an additional source bound. -/

theorem suffixRawOldCarrierDomination_iff_exists_bounded_oldCarrierReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixRawOldCarrierDomination owner lambda p S bound ↔
      (0 ≤ bound ∧
        ∃ readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
            sourceSoninCarrier lambda,
          ‖readout‖ ≤ bound ∧
            readout ∘L suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
              lambda p S =
            suffixActualBandRawPhysicalReducedRow owner lambda p S) := by
  constructor
  · intro hdom
    refine ⟨hdom.1, ?_⟩
    obtain ⟨readout, hnorm, hfactor⟩ :=
      exists_factor_of_norm_sq_le
        (suffixActualBandRawPhysicalReducedRow owner lambda p S)
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
        bound hdom.1 hdom.2
    exact ⟨readout, hnorm, hfactor⟩
  · rintro ⟨hbound, readout, hnorm, hfactor⟩
    refine ⟨hbound, ?_⟩
    intro y
    have hpoint :
        suffixActualBandRawPhysicalReducedRow owner lambda p S y =
          readout
            (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
              lambda p S y) := by
      have h := congrArg
        (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => T y)
        hfactor.symm
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hnormPoint :
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S y‖ ≤
          bound *
            ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
              lambda p S y‖ := by
      rw [hpoint]
      calc
        ‖readout
            (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
              lambda p S y)‖ ≤
            ‖readout‖ *
              ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
                lambda p S y‖ := readout.le_opNorm _
        _ ≤ bound *
            ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
              lambda p S y‖ := by
          exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    have hsq := (sq_le_sq₀ (norm_nonneg
      (suffixActualBandRawPhysicalReducedRow owner lambda p S y))
      (mul_nonneg hbound (norm_nonneg
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y)))).mpr
      hnormPoint
    simpa only [mul_pow] using hsq

/-- The full old-carrier estimate implies the original raw physical Douglas
estimate, with the signed two-channel energy kept packed. -/
theorem suffixRawOldCarrierDomination_implies_rawDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixRawOldCarrierDomination owner lambda p S bound) :
    SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  refine ⟨hdom.1, ?_⟩
  intro x
  have hraw := hdom.2
    ((suffixEulerFrameSchurStep lambda p S).oldFrame x)
  have hrow :
      suffixActualBandRawPhysicalReducedRow owner lambda p S
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x) =
        suffixActualBandRawPhysicalFourTermRow owner lambda p S x := by
    have h := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda => T x)
      (suffixActualBandRawPhysicalFourTermRow_eq_reducedRow_comp_oldFrame
        owner lambda p S)
    simpa only [ContinuousLinearMap.comp_apply] using h.symm
  have hanalysis :
      suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
          ((suffixEulerFrameSchurStep lambda p S).oldFrame x) =
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S x := by
    have h := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ]
          suffixEulerFrameAmbientBoundaryCarrier => T x)
      (suffixEulerFrameAmbientBoundaryAnalysis_eq_oldCarrier_comp_oldFrame
        lambda p S)
    simpa only [ContinuousLinearMap.comp_apply] using h.symm
  rw [hrow, hanalysis] at hraw
  rw [suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow]
  rw [← suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels]
  exact hraw

/-! ## Douglas construction on the reduced carrier -/

/-- A full old-carrier estimate constructs a bounded raw readout on the actual
packed physical carrier. -/
noncomputable def suffixRawAmbientBoundaryReadoutDataOfOldCarrierDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixRawOldCarrierDomination owner lambda p S bound) :
    SuffixRawAmbientBoundaryReadoutData owner lambda p S bound := by
  let witness := exists_factor_of_norm_sq_le
    (suffixActualBandRawPhysicalReducedRow owner lambda p S)
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
    bound hdom.1 hdom.2
  let readout := Classical.choose witness
  have readoutSpec := Classical.choose_spec witness
  refine
    { bound_nonneg := hdom.1
      readout := readout
      readout_norm_le := readoutSpec.1
      factorization := ?_ }
  calc
    readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
        readout ∘L
          (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S ∘L
            (suffixEulerFrameSchurStep lambda p S).oldFrame) := by
      rw [suffixEulerFrameAmbientBoundaryAnalysis_eq_oldCarrier_comp_oldFrame]
    _ = suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          (suffixEulerFrameSchurStep lambda p S).oldFrame := by
      rw [← ContinuousLinearMap.comp_assoc, readoutSpec.2]
    _ = suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
      rw [suffixActualBandRawPhysicalFourTermRow_eq_reducedRow_comp_oldFrame]
    _ = (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† := by
      rw [suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
end CCM25Concrete
end Source
end ConnesWeilRH
