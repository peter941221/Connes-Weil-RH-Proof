/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CC20Concrete.ThreeBranchCommutatorLedger

/-!
# Centered Gram response for the finite-S Sonin projection

The finite-S orthogonal projection is a Gram-corrected frame projection, not
an oblique similarity.  This module centers its detector response before the
Gram inverse is applied.  Because the selected convolution detector commutes
with every Euler translation, the centered numerator reduces to one fixed
source-Sonin boundary commutator.

No trace estimate or Gate 3U bound is asserted here.  The identities expose
the exact source operator that the uniform estimate must control.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGramResponse

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open SelectedCrossingOperatorBridge
open CCM24FiniteSProjectionTrace
open scoped InnerProduct

noncomputable abbrev sourceSoninCarrier (lambda : CCM24SoninScale) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The isometric inclusion `J` of the source Sonin space. -/
noncomputable def sourceInclusion (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.subtypeL

/-- `J†J=I` on the source Sonin carrier. -/
theorem sourceInclusion_adjoint_comp_self (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L sourceInclusion lambda =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [sourceInclusion, Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  exact (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule
    |>.starProjection_mem_subspace_eq_self u

/-- `JJ†` is the source Sonin orthogonal projection on the ambient carrier. -/
theorem sourceInclusion_comp_adjoint
    (lambda : CCM24SoninScale) :
    sourceInclusion lambda ∘L (sourceInclusion lambda)† =
      sourceSoninProjection lambda := by
  rw [sourceInclusion, Submodule.adjoint_subtypeL]
  rfl

/-- The source Sonin projection has the actual CC20 three-branch owner
`R_0=E Q_0 E-K_0`. -/
theorem sourceSoninProjection_eq_compression_sub_prolate
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda =
      radialSupportProjection lambda ∘L
          sourceFourierSupportProjection lambda ∘L
          radialSupportProjection lambda - sourceProlateRemainder lambda := by
  rw [sourceProlateRemainder]
  abel

/-- Projecting before the inclusion adjoint does nothing: `J†P_0=J†`. -/
theorem sourceInclusionAdjoint_comp_sourceProjection
    (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L sourceSoninProjection lambda =
      (sourceInclusion lambda)† := by
  rw [← sourceInclusion_comp_adjoint]
  calc
    (sourceInclusion lambda)† ∘L
          (sourceInclusion lambda ∘L (sourceInclusion lambda)†) =
        ((sourceInclusion lambda)† ∘L sourceInclusion lambda) ∘L
          (sourceInclusion lambda)† := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) ∘L
          (sourceInclusion lambda)† := by
      rw [sourceInclusion_adjoint_comp_self]
    _ = (sourceInclusion lambda)† := by
      apply ContinuousLinearMap.ext
      intro u
      rfl

/-- The finite Euler transport restricted to the source Sonin carrier. -/
noncomputable def finiteEulerFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  restrictedClosedTransport
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

theorem finiteEulerFrame_eq_transport_comp_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerFrame lambda family =
      (ccm24FiniteEulerTransportEquiv family.visiblePrimes).toContinuousLinearMap ∘L
        sourceInclusion lambda :=
  rfl

/-- The source-carrier Gram covariance `A†A`. -/
noncomputable def finiteEulerGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (finiteEulerFrame lambda family)† ∘L finiteEulerFrame lambda family

/-- The canonical inverse Gram covariance supplied by the restricted
continuous linear equivalence. -/
noncomputable def finiteEulerGramInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  restrictedTransportGramInv
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

theorem finiteEulerGramInv_comp_gram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerGramInv lambda family ∘L finiteEulerGram lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  exact restrictedTransportGramInv_leftInverse
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

theorem finiteEulerGram_isSelfAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerGram lambda family) := by
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (finiteEulerFrame lambda family)).isSelfAdjoint

theorem finiteEulerGramInv_isSelfAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerGramInv lambda family) := by
  exact restrictedTransportGramInv_isSelfAdjoint
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

/-- Self-adjointness turns the constructed left inverse into a right inverse. -/
theorem finiteEulerGram_comp_inv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerGram lambda family ∘L finiteEulerGramInv lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have h := congrArg (fun operator => ContinuousLinearMap.adjoint operator)
    (finiteEulerGramInv_comp_gram lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (finiteEulerGram_isSelfAdjoint lambda family).adjoint_eq,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq,
    ContinuousLinearMap.adjoint_id] using h

/-- The canonical dual frame `F=A(A†A)⁻¹`. -/
noncomputable def finiteEulerDualFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  finiteEulerFrame lambda family ∘L finiteEulerGramInv lambda family

/-- The dual-frame covariance is the inverse Gram covariance: `F†F=G⁻¹`. -/
theorem dualFrameAdjoint_comp_dualFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerDualFrame lambda family)† ∘L
        finiteEulerDualFrame lambda family =
      finiteEulerGramInv lambda family := by
  rw [finiteEulerDualFrame, ContinuousLinearMap.adjoint_comp,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  change finiteEulerGramInv lambda family
      (finiteEulerGram lambda family (finiteEulerGramInv lambda family u)) =
    finiteEulerGramInv lambda family u
  rw [show finiteEulerGram lambda family
      (finiteEulerGramInv lambda family u) = u by
    have h := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
      (finiteEulerGram_comp_inv lambda family)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h]

theorem frameAdjoint_comp_dualFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerFrame lambda family)† ∘L
        finiteEulerDualFrame lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [finiteEulerDualFrame]
  calc
    (finiteEulerFrame lambda family)† ∘L
          (finiteEulerFrame lambda family ∘L
            finiteEulerGramInv lambda family) =
        finiteEulerGram lambda family ∘L
          finiteEulerGramInv lambda family := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = _ := finiteEulerGram_comp_inv lambda family

theorem dualFrame_adjoint_comp_frame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerDualFrame lambda family)† ∘L
        finiteEulerFrame lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have h := congrArg (fun operator => ContinuousLinearMap.adjoint operator)
    (frameAdjoint_comp_dualFrame lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id] using h

/-- The target Sonin projection is the dual-frame/frame-adjoint product. -/
theorem targetSoninProjection_eq_dualFrame_comp_frameAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      finiteEulerDualFrame lambda family ∘L
        (finiteEulerFrame lambda family)† := by
  rw [targetSoninProjection_eq_gramCorrected]
  rfl

/-- Exact dual-frame factorization of the projection difference.  It is a
fixed-S trace-legality factorization; no triangle inequality is licensed by
this identity. -/
theorem bandDifference_eq_dualFrame_twoCrossing
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    bandDifference lambda family =
      (finiteEulerDualFrame lambda family - sourceInclusion lambda) ∘L
          (finiteEulerFrame lambda family)† +
        sourceInclusion lambda ∘L
          ((finiteEulerFrame lambda family)† -
            (sourceInclusion lambda)†) := by
  rw [bandDifference, targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    ← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  rw [(sourceInclusion lambda).map_sub]
  abel

/-- The selected convolution detector is self-adjoint and positive. -/
theorem detectorOperator_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    IsSelfAdjoint (detectorOperator owner) := by
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (cc20GlobalLogConvolution owner.sourceTest.involution.test)).isSelfAdjoint

/-- The selected detector commutes with every global logarithmic translation. -/
theorem detectorOperator_comp_translation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (b : ℝ) :
    detectorOperator owner ∘L
        (cc20GlobalLogTranslation b).toContinuousLinearMap =
      (cc20GlobalLogTranslation b).toContinuousLinearMap ∘L
        detectorOperator owner := by
  let C := cc20GlobalLogConvolution owner.sourceTest.involution.test
  let U := (cc20GlobalLogTranslation b).toContinuousLinearMap
  let Uinv := (cc20GlobalLogTranslation (-b)).toContinuousLinearMap
  have hC : C ∘L U = U ∘L C := by
    simpa only [neg_neg] using
      (cc20GlobalLogConvolution_comp_translation_neg_eq
        owner.sourceTest (-b))
  have hCinv : C ∘L Uinv = Uinv ∘L C := by
    exact cc20GlobalLogConvolution_comp_translation_neg_eq
      owner.sourceTest b
  have hCadj : C† ∘L U = U ∘L C† := by
    have h := congrArg (fun operator => ContinuousLinearMap.adjoint operator)
      hCinv
    simpa [U, Uinv, ContinuousLinearMap.adjoint_comp,
      cc20GlobalLogTranslation_neg_adjoint] using h.symm
  change C† ∘L C ∘L U = U ∘L (C† ∘L C)
  calc
    C† ∘L C ∘L U = C† ∘L (C ∘L U) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = C† ∘L (U ∘L C) := by rw [hC]
    _ = (C† ∘L U) ∘L C := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = (U ∘L C†) ∘L C := by rw [hCadj]
    _ = U ∘L (C† ∘L C) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl

/-- The detector commutes with one concrete Euler factor. -/
theorem detectorOperator_comp_primeEulerTransport
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    detectorOperator owner ∘L
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap ∘L
        detectorOperator owner := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change detectorOperator owner (ccm24PrimeEulerTransportEquiv p u) =
    ccm24PrimeEulerTransportEquiv p (detectorOperator owner u)
  rw [ccm24PrimeEulerTransportEquiv_apply p u,
    ccm24PrimeEulerTransportEquiv_apply p (detectorOperator owner u),
    map_sub, map_smul]
  rw [show detectorOperator owner
      (cc20GlobalLogTranslation (-Real.log p) u) =
        cc20GlobalLogTranslation (-Real.log p) (detectorOperator owner u) by
    have h := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
      (detectorOperator_comp_translation owner (-Real.log p))
    simpa only [ContinuousLinearMap.comp_apply] using h]

/-- The detector commutes with the complete finite Euler product. -/
theorem detectorOperator_comp_finiteEulerTransport
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    detectorOperator owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap ∘L
        detectorOperator owner := by
  induction S with
  | nil =>
      rw [ccm24FiniteEulerTransportEquiv_nil]
      apply ContinuousLinearMap.ext
      intro u
      rfl
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro u
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      change detectorOperator owner
          (ccm24FiniteEulerTransportEquiv (p :: S) u) =
        ccm24FiniteEulerTransportEquiv (p :: S) (detectorOperator owner u)
      rw [ccm24FiniteEulerTransportEquiv_cons_apply p S u,
        ccm24FiniteEulerTransportEquiv_cons_apply p S
          (detectorOperator owner u)]
      have hp := congrArg
        (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
          operator (ccm24FiniteEulerTransportEquiv S u))
        (detectorOperator_comp_primeEulerTransport owner p)
      have hS := congrArg
        (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u) ih
      simp only [ContinuousLinearMap.comp_apply] at hp hS
      change detectorOperator owner
          (ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S u)) =
        ccm24PrimeEulerTransportEquiv p
          (detectorOperator owner (ccm24FiniteEulerTransportEquiv S u)) at hp
      calc
        detectorOperator owner
            (ccm24PrimeEulerTransportEquiv p
              (ccm24FiniteEulerTransportEquiv S u)) =
          ccm24PrimeEulerTransportEquiv p
            (detectorOperator owner
              (ccm24FiniteEulerTransportEquiv S u)) := hp
        _ = ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S
              (detectorOperator owner u)) := congrArg
                (ccm24PrimeEulerTransportEquiv p) hS

/-- The adjoint Euler transport commutes with the self-adjoint detector. -/
theorem finiteEulerTransportAdjoint_comp_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (S : List CCM24VisiblePrime) :
    (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint ∘L
        detectorOperator owner =
      detectorOperator owner ∘L
        (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun operator => ContinuousLinearMap.adjoint operator)
    (detectorOperator_comp_finiteEulerTransport owner S)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq] using h

/-- The ambient positive covariance `T†T`. -/
noncomputable def finiteEulerAmbientGram (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24FiniteEulerTransportEquiv family.visiblePrimes).toContinuousLinearMap.adjoint ∘L
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes).toContinuousLinearMap

theorem finiteEulerGram_eq_compressedAmbientGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerGram lambda family =
      (sourceInclusion lambda)† ∘L finiteEulerAmbientGram family ∘L
        sourceInclusion lambda := by
  rw [finiteEulerGram, finiteEulerFrame_eq_transport_comp_inclusion,
    finiteEulerAmbientGram, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The numerator is centered before applying the inverse Gram covariance. -/
noncomputable def centeredGramNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
      finiteEulerFrame lambda family -
    ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda) ∘L finiteEulerGram lambda family

/-- Commutation with the Euler transport moves the first Gram numerator to
the fixed detector followed by the ambient covariance. -/
theorem frameAdjoint_detector_frame_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
        finiteEulerFrame lambda family =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda := by
  rw [finiteEulerFrame_eq_transport_comp_inclusion,
    finiteEulerAmbientGram, ContinuousLinearMap.adjoint_comp]
  have h := finiteEulerTransportAdjoint_comp_detector owner
    family.visiblePrimes
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator ((ccm24FiniteEulerTransportEquiv family.visiblePrimes)
        (sourceInclusion lambda u))) h
  simpa only [ContinuousLinearMap.comp_apply] using congrArg
    ((sourceInclusion lambda)†) hu

/-- Exact fixed-boundary form of the centered numerator. -/
theorem centeredGramNumerator_eq_fixedBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    centeredGramNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda := by
  rw [centeredGramNumerator, frameAdjoint_detector_frame_eq,
    finiteEulerGram_eq_compressedAmbientGram,
    ← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_sub]

/-- The fixed source-Sonin detector commutator `[W,P_0]`. -/
noncomputable def sourceBoundaryCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L sourceSoninProjection lambda -
    sourceSoninProjection lambda ∘L detectorOperator owner

/-- Our boundary orientation `[W,P_0]` is the negative of the CC20 ledger
orientation `[P_0,W]`. -/
theorem sourceBoundaryCommutator_eq_neg_cc20Commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceBoundaryCommutator owner lambda =
      -cc20Commutator (sourceSoninProjection lambda)
        (detectorOperator owner) := by
  unfold sourceBoundaryCommutator cc20Commutator
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply]
  abel

/-- The actual source commutator is the completed outer, second-support,
reflected-outer, and prolate ledger. -/
theorem sourceSoninCommutator_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    cc20Commutator (sourceSoninProjection lambda) (detectorOperator owner) =
      cc20ThreeBranchCommutator
        (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda)
        (detectorOperator owner) := by
  exact cc20Commutator_eq_threeBranch_of_eq
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceSoninProjection lambda)
    (sourceProlateRemainder lambda)
    (detectorOperator owner)
    (sourceSoninProjection_eq_compression_sub_prolate lambda)

/-- The fixed boundary commutator in the Gram numerator is the negative of
the completed three-branch source operator. -/
theorem sourceBoundaryCommutator_eq_neg_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceBoundaryCommutator owner lambda =
      -cc20ThreeBranchCommutator
        (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda)
        (detectorOperator owner) := by
  rw [sourceBoundaryCommutator_eq_neg_cc20Commutator,
    sourceSoninCommutator_eq_threeBranch]

/-- The completed complement leg is exactly the negative fixed commutator
after applying `J†`. -/
theorem inclusionAdjoint_detector_complement_eq_neg_commutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) =
      -((sourceInclusion lambda)† ∘L
        sourceBoundaryCommutator owner lambda) := by
  apply ContinuousLinearMap.ext
  intro u
  have hprojection := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner u))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [ContinuousLinearMap.comp_apply] at hprojection
  simp only [sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hprojection]
  abel

/-- Final exact source reduction: the centered numerator is the fixed
detector commutator followed by the complete Euler covariance. -/
theorem centeredGramNumerator_eq_fixedCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    centeredGramNumerator owner lambda family =
      -((sourceInclusion lambda)† ∘L
          sourceBoundaryCommutator owner lambda) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda := by
  rw [centeredGramNumerator_eq_fixedBoundary]
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (finiteEulerAmbientGram family (sourceInclusion lambda u)))
    (inclusionAdjoint_detector_complement_eq_neg_commutator owner lambda)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply] using h

/-- After the exact sign cancellation, the centered numerator is the
completed physical three-branch source operator followed by the complete
Euler covariance. -/
theorem centeredGramNumerator_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    centeredGramNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)
          (detectorOperator owner) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda := by
  rw [centeredGramNumerator_eq_fixedCommutator,
    sourceBoundaryCommutator_eq_neg_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    map_neg, neg_neg]

/-- The response after legal rectangular cycling is the centered numerator
times the common inverse Gram covariance.  The theorem is operator algebra;
it does not assert that such cycling is trace-legal. -/
noncomputable def sourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
      finiteEulerFrame lambda family) ∘L finiteEulerGramInv lambda family -
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
      sourceInclusion lambda

theorem sourceGramResponse_eq_centered
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGramResponse owner lambda family =
      centeredGramNumerator owner lambda family ∘L
        finiteEulerGramInv lambda family := by
  rw [sourceGramResponse, centeredGramNumerator]
  have hright := finiteEulerGram_comp_inv lambda family
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u) hright
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply] at hu ⊢
  rw [hu]

/-- The complete source response contains one fixed boundary commutator and
the ordered Euler covariance/Gram-inverse leg. -/
theorem sourceGramResponse_eq_fixedCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGramResponse owner lambda family =
      -((sourceInclusion lambda)† ∘L
          sourceBoundaryCommutator owner lambda) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [sourceGramResponse_eq_centered,
    centeredGramNumerator_eq_fixedCommutator]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- Complete three-branch source owner of the cycled Gram response.  This is
the exact operator to which compact root support must be applied before one
absolute value. -/
theorem sourceGramResponse_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGramResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)
          (detectorOperator owner) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [sourceGramResponse_eq_centered,
    centeredGramNumerator_eq_threeBranch]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The scalar lower factor of the complete Euler product. -/
noncomputable def finiteEulerLowerFactor (S : List CCM24VisiblePrime) : ℝ :=
  (S.map fun p => 1 - ccm24PrimeEulerCoefficient p).prod

theorem primeEulerLowerFactor_pos (p : CCM24VisiblePrime) :
    0 < 1 - ccm24PrimeEulerCoefficient p := by
  exact sub_pos.mpr (ccm24PrimeEulerCoefficient_lt_one p)

theorem finiteEulerLowerFactor_pos (S : List CCM24VisiblePrime) :
    0 < finiteEulerLowerFactor S := by
  induction S with
  | nil => simp [finiteEulerLowerFactor]
  | cons p S ih =>
      simpa [finiteEulerLowerFactor] using
        mul_pos (primeEulerLowerFactor_pos p) ih

/-- One Euler factor is bounded below by `1-p⁻¹/²`. -/
theorem primeEulerTransport_lower_bound
    (p : CCM24VisiblePrime) (u : finiteSCarrier) :
    (1 - ccm24PrimeEulerCoefficient p) * ‖u‖ ≤
      ‖ccm24PrimeEulerTransportEquiv p u‖ := by
  rw [ccm24PrimeEulerTransportEquiv_apply]
  have hnorm :
      ‖(ccm24PrimeEulerCoefficient p : ℂ) •
          cc20GlobalLogTranslation (-Real.log p) u‖ =
        ccm24PrimeEulerCoefficient p * ‖u‖ := by
    rw [norm_smul, norm_cc20GlobalLogTranslation,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
  calc
    (1 - ccm24PrimeEulerCoefficient p) * ‖u‖ =
        ‖u‖ - ccm24PrimeEulerCoefficient p * ‖u‖ := by ring
    _ = ‖u‖ - ‖(ccm24PrimeEulerCoefficient p : ℂ) •
          cc20GlobalLogTranslation (-Real.log p) u‖ := by rw [hnorm]
    _ ≤ ‖u - (ccm24PrimeEulerCoefficient p : ℂ) •
          cc20GlobalLogTranslation (-Real.log p) u‖ :=
      norm_sub_norm_le _ _

/-- The complete Euler product has the product lower bound. -/
theorem finiteEulerTransport_lower_bound
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    finiteEulerLowerFactor S * ‖u‖ ≤
      ‖ccm24FiniteEulerTransportEquiv S u‖ := by
  induction S with
  | nil =>
      simp [finiteEulerLowerFactor, ccm24FiniteEulerTransportEquiv_nil]
  | cons p S ih =>
      rw [ccm24FiniteEulerTransportEquiv_cons_apply]
      change (1 - ccm24PrimeEulerCoefficient p) *
          finiteEulerLowerFactor S * ‖u‖ ≤ _
      calc
        (1 - ccm24PrimeEulerCoefficient p) *
              finiteEulerLowerFactor S * ‖u‖ =
            (1 - ccm24PrimeEulerCoefficient p) *
              (finiteEulerLowerFactor S * ‖u‖) := by ring
        _ ≤ (1 - ccm24PrimeEulerCoefficient p) *
              ‖ccm24FiniteEulerTransportEquiv S u‖ := by
          exact mul_le_mul_of_nonneg_left ih
            (le_of_lt (primeEulerLowerFactor_pos p))
        _ ≤ ‖ccm24PrimeEulerTransportEquiv p
              (ccm24FiniteEulerTransportEquiv S u)‖ :=
          primeEulerTransport_lower_bound p _

/-- After multiplying the inverse transport by the lower factor, it is a
pointwise contraction.  This is the condition-number-free Markov
normalization used by the Gate 3U route. -/
theorem norm_lowerFactor_smul_finiteEulerInverse_le
    (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        (ccm24FiniteEulerTransportEquiv S).symm u‖ ≤ ‖u‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (finiteEulerLowerFactor_pos S)]
  have h := finiteEulerTransport_lower_bound S
    ((ccm24FiniteEulerTransportEquiv S).symm u)
  simpa only [(ccm24FiniteEulerTransportEquiv S).apply_symm_apply] using h

/-- The normalized inverse transport is a contraction in operator norm. -/
theorem norm_lowerFactor_smul_finiteEulerInverseOperator_le_one
    (S : List CCM24VisiblePrime) :
    ‖(finiteEulerLowerFactor S : ℂ) •
        (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [ContinuousLinearMap.smul_apply, one_mul] using
    norm_lowerFactor_smul_finiteEulerInverse_le S u

end CCM24FiniteSGramResponse
end CCM25Concrete
end Source
end ConnesWeilRH
