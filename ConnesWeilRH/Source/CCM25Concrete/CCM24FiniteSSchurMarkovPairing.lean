/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBiSchurRelative
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping

/-!
# Actual forward Schur and reverse Markov pairing

The upper-normalized Euler factor gives the genuine forward contraction
between consecutive polar Sonin frames.  The probability-normalized inverse
Euler factor gives the reverse contraction between the same two frames.
This module constructs that reverse transition on the literal fixed source
carrier and proves that the two transitions multiply, in both orders, to the
exact scalar

```text
rho_p = (1 - p^(-1/2)) / (1 + p^(-1/2)).
```

The complete forward and reverse products therefore form an actual
bi-Schur pair.  This is the inverse-free owner required by a signed relative
numerator.  No norm of an inverse Gram operator, physical readout, Gate 3U
estimate, sign theorem, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurMarkovPairing

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBiSchurRelative
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCausal
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSSchurCascade
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## One reverse Markov transition -/

/-- The scalar pair of the upper-normalized forward Euler factor and the
probability-normalized reverse Euler factor. -/
noncomputable def primeSchurMarkovScalar
    (p : CCM24VisiblePrime) : ℝ :=
  (1 - ccm24PrimeEulerCoefficient p) /
    (1 + ccm24PrimeEulerCoefficient p)

theorem primeSchurMarkovScalar_pos (p : CCM24VisiblePrime) :
    0 < primeSchurMarkovScalar p := by
  exact div_pos (CCM24FiniteSGramResponse.primeEulerLowerFactor_pos p)
    (primeEulerUpperFactor_pos p)

/-- The reverse source transition is the probability-normalized inverse
Euler factor compressed between the same consecutive polar frames as the
forward Schur transition. -/
noncomputable def suffixEulerFrameReverseTransition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
    oldSuffixFrame lambda p S

/-- The probability-normalized inverse Euler factor maps the old suffix
Sonin carrier into the adjacent new suffix carrier. -/
theorem normalizedPrimeEulerInverse_mem_newSuffix
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    normalizedPrimeEulerInverse p (oldSuffixFrame lambda p S x) ∈
      (parameterizedSoninClosedSubspace lambda 1 S
        (by norm_num)).toSubmodule := by
  let oldT := parameterizedFiniteEulerEquiv 1 (p :: S) (by norm_num)
  let newT := parameterizedFiniteEulerEquiv 1 S (by norm_num)
  let source := ccm24ArchimedeanSoninClosedSubspace lambda
  have hold := newSuffixFrame_mem lambda (p :: S) x
  have holdMap : oldSuffixFrame lambda p S x ∈
      ClosedSubmodule.mapEquiv oldT source := by
    rw [parameterizedFiniteEulerEquiv_maps_sonin]
    simpa only [oldSuffixFrame, newSuffixFrame] using hold
  have hpre : oldT.symm (oldSuffixFrame lambda p S x) ∈ source :=
    (ClosedSubmodule.mem_mapEquiv_iff oldT source
      (oldSuffixFrame lambda p S x)).1 holdMap
  have hnewMap :
      newT (oldT.symm (oldSuffixFrame lambda p S x)) ∈
        ClosedSubmodule.mapEquiv newT source := by
    apply (ClosedSubmodule.mem_mapEquiv_iff newT source _).2
    simpa using hpre
  have hnew :
      newT (oldT.symm (oldSuffixFrame lambda p S x)) ∈
        (parameterizedSoninClosedSubspace lambda 1 S
          (by norm_num)).toSubmodule := by
    rw [parameterizedFiniteEulerEquiv_maps_sonin] at hnewMap
    exact hnewMap
  have holdRepr : oldSuffixFrame lambda p S x =
      ccm24FiniteEulerTransportEquiv (p :: S)
        (oldT.symm (oldSuffixFrame lambda p S x)) := by
    calc
      oldSuffixFrame lambda p S x =
          oldT (oldT.symm (oldSuffixFrame lambda p S x)) :=
        (oldT.apply_symm_apply _).symm
      _ = ccm24FiniteEulerTransportEquiv (p :: S)
          (oldT.symm (oldSuffixFrame lambda p S x)) := by
        rw [show oldT = ccm24FiniteEulerTransportEquiv (p :: S) by
          simpa only [oldT] using
            parameterizedFiniteEulerEquiv_one (p :: S)]
  have hinverse :
      (ccm24PrimeEulerTransportEquiv p).symm
          (oldSuffixFrame lambda p S x) =
        newT (oldT.symm (oldSuffixFrame lambda p S x)) := by
    calc
      (ccm24PrimeEulerTransportEquiv p).symm
          (oldSuffixFrame lambda p S x) =
          (ccm24PrimeEulerTransportEquiv p).symm
            (ccm24FiniteEulerTransportEquiv (p :: S)
              (oldT.symm (oldSuffixFrame lambda p S x))) := by
        exact congrArg (ccm24PrimeEulerTransportEquiv p).symm holdRepr
      _ = ccm24FiniteEulerTransportEquiv S
          (oldT.symm (oldSuffixFrame lambda p S x)) := by
        rw [ccm24FiniteEulerTransportEquiv_cons_apply,
          (ccm24PrimeEulerTransportEquiv p).symm_apply_apply]
      _ = newT (oldT.symm (oldSuffixFrame lambda p S x)) := by
        rw [show newT = ccm24FiniteEulerTransportEquiv S by
          simpa only [newT] using parameterizedFiniteEulerEquiv_one S]
  change (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (ccm24PrimeEulerTransportEquiv p).symm
        (oldSuffixFrame lambda p S x)) ∈
    (parameterizedSoninClosedSubspace lambda 1 S
      (by norm_num)).toSubmodule
  rw [hinverse]
  exact (parameterizedSoninClosedSubspace lambda 1 S
    (by norm_num)).toSubmodule.smul_mem _ hnew

theorem suffixEulerFrameReverseTransition_norm_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixEulerFrameReverseTransition lambda p S‖ ≤ 1 := by
  have hold : ‖oldSuffixFrame lambda p S‖ ≤ 1 :=
    norm_le_one_of_isometric_inclusion (oldSuffixFrame lambda p S) (by
      intro x
      exact parameterizedSoninPolarFrame_isometry lambda 1 (p :: S)
        (by norm_num) x)
  have hnew : ‖newSuffixFrame lambda S‖ ≤ 1 :=
    norm_le_one_of_isometric_inclusion (newSuffixFrame lambda S) (by
      intro x
      exact parameterizedSoninPolarFrame_isometry lambda 1 S
        (by norm_num) x)
  have hinverse : ‖normalizedPrimeEulerInverse p‖ ≤ 1 :=
    norm_normalizedPrimeEulerInverse_le_one p
  simpa only [suffixEulerFrameReverseTransition] using
    (rectangular_frame_transport_norm_le_one
      (newSuffixFrame lambda S) (oldSuffixFrame lambda p S)
      (normalizedPrimeEulerInverse p) hnew hinverse hold)

/-- Exact reverse intertwining between the adjacent polar frames. -/
theorem normalizedPrimeEulerInverse_comp_oldFrame
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedPrimeEulerInverse p ∘L oldSuffixFrame lambda p S =
      newSuffixFrame lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  let y := normalizedPrimeEulerInverse p (oldSuffixFrame lambda p S x)
  have hy : y ∈ (newSuffixFrame lambda S).range := by
    rw [show (newSuffixFrame lambda S).range =
        (parameterizedSoninClosedSubspace lambda 1 S
          (by norm_num)).toSubmodule by
      exact parameterizedSoninPolarFrame_range lambda 1 S (by norm_num)]
    exact normalizedPrimeEulerInverse_mem_newSuffix lambda p S x
  have hframe := frame_comp_adjoint_eq_of_mem_range
    (newSuffixFrame lambda S)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
      (by norm_num)) hy
  change y = newSuffixFrame lambda S
    (ContinuousLinearMap.adjoint (newSuffixFrame lambda S) y)
  exact hframe.symm

/-! ## Exact one-step scalar pairing -/

theorem normalizedPrimeEulerFrameTransport_comp_inverse
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L normalizedPrimeEulerInverse p =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro x
  change (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ •
      ccm24PrimeEulerTransportEquiv p
        ((((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
          (ccm24PrimeEulerTransportEquiv p).symm x)) =
    (primeSchurMarkovScalar p : ℂ) • x
  rw [map_smul, (ccm24PrimeEulerTransportEquiv p).apply_symm_apply,
    smul_smul]
  congr 1
  simp only [primeSchurMarkovScalar]
  push_cast
  field_simp [ne_of_gt (primeEulerUpperFactor_pos p)]

theorem normalizedPrimeEulerInverse_comp_frameTransport
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerInverse p ∘L normalizedPrimeEulerFrameTransport p =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro x
  change ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (ccm24PrimeEulerTransportEquiv p).symm
        (((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
          ccm24PrimeEulerTransportEquiv p x) =
    (primeSchurMarkovScalar p : ℂ) • x
  rw [map_smul, (ccm24PrimeEulerTransportEquiv p).symm_apply_apply,
    smul_smul]
  congr 1
  simp only [primeSchurMarkovScalar]
  push_cast
  field_simp [ne_of_gt (primeEulerUpperFactor_pos p)]

theorem suffixEulerFrameTransition_comp_reverse
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameTransition lambda p S ∘L
        suffixEulerFrameReverseTransition lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpair := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (oldSuffixFrame lambda p S x))
    (normalizedPrimeEulerFrameTransport_comp_inverse p)
  have hy : normalizedPrimeEulerInverse p
      (oldSuffixFrame lambda p S x) ∈ (newSuffixFrame lambda S).range := by
    rw [show (newSuffixFrame lambda S).range =
        (parameterizedSoninClosedSubspace lambda 1 S
          (by norm_num)).toSubmodule by
      exact parameterizedSoninPolarFrame_range lambda 1 S (by norm_num)]
    exact normalizedPrimeEulerInverse_mem_newSuffix lambda p S x
  have hproject := frame_comp_adjoint_eq_of_mem_range
    (newSuffixFrame lambda S)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
      (by norm_num)) hy
  have hold := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator x)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 (p :: S)
      (by norm_num))
  have hold' : ContinuousLinearMap.adjoint (oldSuffixFrame lambda p S)
      (oldSuffixFrame lambda p S x) = x := by
    simpa only [oldSuffixFrame, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hold
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hpair hold
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  simp only [suffixEulerFrameTransition,
    suffixEulerFrameReverseTransition, ContinuousLinearMap.comp_apply]
  rw [hproject, hpair, map_smul, hold']

theorem suffixEulerFrameReverse_comp_transition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameReverseTransition lambda p S ∘L
        suffixEulerFrameTransition lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpair := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (newSuffixFrame lambda S x))
    (normalizedPrimeEulerInverse_comp_frameTransport p)
  have hy : normalizedPrimeEulerFrameTransport p
      (newSuffixFrame lambda S x) ∈ (oldSuffixFrame lambda p S).range := by
    rw [show (oldSuffixFrame lambda p S).range =
        (parameterizedSoninClosedSubspace lambda 1 (p :: S)
          (by norm_num)).toSubmodule by
      simpa only [oldSuffixFrame] using
        parameterizedSoninPolarFrame_range lambda 1 (p :: S) (by norm_num)]
    exact normalizedPrimeEulerFrameTransport_mem_oldSuffix lambda p S x
  have hproject := frame_comp_adjoint_eq_of_mem_range
    (oldSuffixFrame lambda p S)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 (p :: S)
      (by norm_num)) hy
  have hnew := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator x)
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
      (by norm_num))
  have hnew' : ContinuousLinearMap.adjoint (newSuffixFrame lambda S)
      (newSuffixFrame lambda S x) = x := by
    simpa only [newSuffixFrame, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hnew
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hpair hnew
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  simp only [suffixEulerFrameTransition,
    suffixEulerFrameReverseTransition, ContinuousLinearMap.comp_apply]
  rw [hproject, hpair, map_smul, hnew']

/-! ## Complete paired products -/

/-- Reverse transitions occur in the inverse chronological order. -/
noncomputable def suffixEulerReverseTransitionProduct
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime →
      sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [] => ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)
  | p :: S => suffixEulerReverseTransitionProduct lambda S ∘L
      suffixEulerFrameReverseTransition lambda p S

/-- Product of all one-step scalar pairs. -/
noncomputable def suffixEulerSchurMarkovScalar :
    List CCM24VisiblePrime → ℝ
  | [] => 1
  | p :: S => primeSchurMarkovScalar p *
      suffixEulerSchurMarkovScalar S

theorem suffixEulerSchurMarkovScalar_pos
    (S : List CCM24VisiblePrime) :
    0 < suffixEulerSchurMarkovScalar S := by
  induction S with
  | nil => norm_num [suffixEulerSchurMarkovScalar]
  | cons p S ih =>
      exact mul_pos (primeSchurMarkovScalar_pos p) ih

/-- The complete Schur--Markov scalar is the literal lower Euler
normalization divided by the upper normalization. -/
theorem suffixEulerSchurMarkovScalar_eq_lower_div_upper
    (S : List CCM24VisiblePrime) :
    suffixEulerSchurMarkovScalar S =
      CCM24FiniteSGramResponse.finiteEulerLowerFactor S /
        finiteEulerUpperFactor S := by
  induction S with
  | nil =>
      simp [suffixEulerSchurMarkovScalar,
        CCM24FiniteSGramResponse.finiteEulerLowerFactor,
        finiteEulerUpperFactor]
  | cons p S ih =>
      change ((1 - ccm24PrimeEulerCoefficient p) /
          (1 + ccm24PrimeEulerCoefficient p)) *
          suffixEulerSchurMarkovScalar S =
        ((1 - ccm24PrimeEulerCoefficient p) *
            CCM24FiniteSGramResponse.finiteEulerLowerFactor S) /
          ((1 + ccm24PrimeEulerCoefficient p) *
            finiteEulerUpperFactor S)
      rw [ih]
      exact div_mul_div_comm
        (a := (1 - ccm24PrimeEulerCoefficient p : ℝ))
        (b := (1 + ccm24PrimeEulerCoefficient p : ℝ))
        (c := CCM24FiniteSGramResponse.finiteEulerLowerFactor S)
        (d := finiteEulerUpperFactor S)

theorem suffixEulerTransitionProduct_comp_reverse
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerTransitionProduct lambda S ∘L
        suffixEulerReverseTransitionProduct lambda S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [suffixEulerTransitionProduct,
        suffixEulerReverseTransitionProduct,
        suffixEulerSchurMarkovScalar]
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro x
      have ihx := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda =>
            operator (suffixEulerFrameReverseTransition lambda p S x)) ih
      have hp := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda => operator x)
        (suffixEulerFrameTransition_comp_reverse lambda p S)
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at ihx hp
      simp only [suffixEulerTransitionProduct,
        suffixEulerReverseTransitionProduct,
        suffixEulerSchurMarkovScalar, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      rw [ihx, map_smul, hp]
      push_cast
      rw [mul_comm]
      simp only [smul_smul]

theorem suffixEulerReverseProduct_comp_transition
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerReverseTransitionProduct lambda S ∘L
        suffixEulerTransitionProduct lambda S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [suffixEulerTransitionProduct,
        suffixEulerReverseTransitionProduct,
        suffixEulerSchurMarkovScalar]
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro x
      have hp := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda =>
            operator (suffixEulerTransitionProduct lambda S x))
        (suffixEulerFrameReverse_comp_transition lambda p S)
      have ihx := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda => operator x) ih
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hp ihx
      simp only [suffixEulerTransitionProduct,
        suffixEulerReverseTransitionProduct,
        suffixEulerSchurMarkovScalar, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      rw [hp, map_smul, ihx]
      push_cast
      simp only [smul_smul]

/-! ## Actual detector relative numerator -/

/-- Compression of the selected detector through one actual suffix polar
frame. -/
noncomputable def suffixPolarDetectorCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (newSuffixFrame lambda S)† ∘L
    CCM24FiniteSProjectionTrace.detectorOperator owner ∘L
      newSuffixFrame lambda S

/-- The one-step scalar pair as an endomorphism of the fixed source carrier. -/
noncomputable def primeSchurMarkovScaleOperator
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (primeSchurMarkovScalar p : ℂ) •
    ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)

/-- The genuine local bi-Schur relative numerator.  The old compression is
the larger suffix `p :: S`; the new compression is the adjacent suffix `S`. -/
noncomputable def suffixEulerDetectorRelativeNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  relativeNumerator
    (suffixPolarDetectorCompression owner lambda (p :: S))
    (suffixEulerFrameTransition lambda p S)
    (suffixPolarDetectorCompression owner lambda S)
    (suffixEulerFrameReverseTransition lambda p S)
    (primeSchurMarkovScaleOperator lambda p)

/-- The normalized forward Euler factor commutes with the selected detector.
The scalar normalization is kept inside the operator identity. -/
theorem normalizedPrimeEulerFrameTransport_comp_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L
        CCM24FiniteSProjectionTrace.detectorOperator owner =
      CCM24FiniteSProjectionTrace.detectorOperator owner ∘L
        normalizedPrimeEulerFrameTransport p := by
  apply ContinuousLinearMap.ext
  intro x
  have hcommute := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
    (CCM24FiniteSGramResponse.detectorOperator_comp_primeEulerTransport
      owner p)
  simp only [ContinuousLinearMap.comp_apply] at hcommute
  simp only [normalizedPrimeEulerFrameTransport,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
  rw [hcommute]

/-- The physical moving-boundary factor in the local detector
intertwinement.  It keeps the new polar projection intact. -/
noncomputable def suffixEulerDetectorBoundaryDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -((oldSuffixFrame lambda p S)† ∘L
      normalizedPrimeEulerFrameTransport p ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        newSuffixFrame lambda S ∘L (newSuffixFrame lambda S)†) ∘L
      CCM24FiniteSProjectionTrace.detectorOperator owner ∘L
      newSuffixFrame lambda S)

/-- Exact source-specific insertion of the complete moving detector crossing
into the forward Schur intertwinement defect. -/
theorem suffixEulerDetectorIntertwiningDefect_eq_boundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S =
      suffixEulerDetectorBoundaryDefect owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  let oldFrame := oldSuffixFrame lambda p S
  let newFrame := newSuffixFrame lambda S
  let transport := normalizedPrimeEulerFrameTransport p
  let transition := suffixEulerFrameTransition lambda p S
  let detector := CCM24FiniteSProjectionTrace.detectorOperator owner
  have htransport : transport ∘L newFrame =
      oldFrame ∘L transition := by
    simpa only [oldFrame, newFrame, transport, transition] using
      (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  have hcommute : transport ∘L detector = detector ∘L transport := by
    simpa only [transport, detector] using
      normalizedPrimeEulerFrameTransport_comp_detector owner p
  have htransition (y : sourceSoninCarrier lambda) :
      ContinuousLinearMap.adjoint oldFrame
        (transport (newFrame y)) = transition y := by
    rfl
  have hdetector : transport (detector (newFrame x)) =
      detector (transport (newFrame x)) := by
    exact congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
        operator (newFrame x)) hcommute
  have htransportApply : transport (newFrame x) =
      oldFrame (transition x) := by
    exact congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x) htransport
  change transition
        (ContinuousLinearMap.adjoint newFrame (detector (newFrame x))) -
      ContinuousLinearMap.adjoint oldFrame
        (detector (oldFrame (transition x))) =
    -(ContinuousLinearMap.adjoint oldFrame
      (transport
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          newFrame ∘L ContinuousLinearMap.adjoint newFrame)
          (detector (newFrame x)))))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  rw [hdetector, htransportApply, htransition]
  abel

/-- The local relative numerator contains no inverse transition: it is the
complete moving-boundary defect followed by the reverse Markov contraction. -/
theorem suffixEulerDetectorRelativeNumerator_eq_boundary_comp_reverse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerDetectorRelativeNumerator owner lambda p S =
      suffixEulerDetectorBoundaryDefect owner lambda p S ∘L
        suffixEulerFrameReverseTransition lambda p S := by
  have hpair : suffixEulerFrameTransition lambda p S *
        suffixEulerFrameReverseTransition lambda p S =
      primeSchurMarkovScaleOperator lambda p := by
    simpa only [ContinuousLinearMap.mul_def,
      primeSchurMarkovScaleOperator] using
        suffixEulerFrameTransition_comp_reverse lambda p S
  have hrelative := relativeNumerator_eq_intertwiningDefect_mul
    (suffixPolarDetectorCompression owner lambda (p :: S))
    (suffixEulerFrameTransition lambda p S)
    (suffixPolarDetectorCompression owner lambda S)
    (suffixEulerFrameReverseTransition lambda p S)
    (primeSchurMarkovScaleOperator lambda p) hpair
  rw [suffixEulerDetectorRelativeNumerator]
  calc
    relativeNumerator
        (suffixPolarDetectorCompression owner lambda (p :: S))
        (suffixEulerFrameTransition lambda p S)
        (suffixPolarDetectorCompression owner lambda S)
        (suffixEulerFrameReverseTransition lambda p S)
        (primeSchurMarkovScaleOperator lambda p) =
      (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S) ∘L
        suffixEulerFrameReverseTransition lambda p S := by
      simpa only [intertwiningDefect, ContinuousLinearMap.mul_def] using
        hrelative
    _ = suffixEulerDetectorBoundaryDefect owner lambda p S ∘L
        suffixEulerFrameReverseTransition lambda p S := by
      rw [suffixEulerDetectorIntertwiningDefect_eq_boundary]

theorem suffixEulerReverseTransitionProduct_norm_le_one
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖suffixEulerReverseTransitionProduct lambda S‖ ≤ 1 := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simp only [suffixEulerReverseTransitionProduct,
        ContinuousLinearMap.id_apply, one_mul, le_refl]
  | cons p S ih =>
      calc
        ‖suffixEulerReverseTransitionProduct lambda (p :: S)‖ ≤
            ‖suffixEulerReverseTransitionProduct lambda S‖ *
              ‖suffixEulerFrameReverseTransition lambda p S‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := mul_le_mul ih
          (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
          (norm_nonneg (suffixEulerFrameReverseTransition lambda p S))
          zero_le_one
        _ = 1 := by norm_num

/-! ## Complete signed detector cocycle -/

/-- The scalar operator carried by a complete reverse Markov suffix.  Keeping
the scalar as an endomorphism makes the noncommutative order explicit. -/
noncomputable def suffixEulerSchurMarkovScaleOperator
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (suffixEulerSchurMarkovScalar S : ℂ) •
    ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)

/-- The complete relative numerator on the fixed source carrier.  It is the
actual ordered product `Gamma_S alpha_empty Lambda_S - rho_S alpha_S`; no
inverse transition is present in this definition. -/
noncomputable def suffixEulerDetectorRelativeNumeratorProduct
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  relativeNumerator
    (suffixPolarDetectorCompression owner lambda S)
    (suffixEulerTransitionProduct lambda S)
    (suffixPolarDetectorCompression owner lambda [])
    (suffixEulerReverseTransitionProduct lambda S)
    (suffixEulerSchurMarkovScaleOperator lambda S)

/-- Recursive signed cocycle of the local moving-boundary numerators.  The
reverse factor stays on the right of each local term, and the suffix scalar is
inserted only after the signed product has been formed. -/
noncomputable def suffixEulerDetectorSignedCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime →
      sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [] => 0
  | p :: S =>
      suffixEulerFrameTransition lambda p S ∘L
          suffixEulerDetectorSignedCocycle owner lambda S ∘L
            suffixEulerFrameReverseTransition lambda p S +
        suffixEulerDetectorRelativeNumerator owner lambda p S ∘L
          suffixEulerSchurMarkovScaleOperator lambda S

theorem suffixEulerSchurMarkovScaleOperator_comm
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (A : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerSchurMarkovScaleOperator lambda S ∘L A =
      A ∘L suffixEulerSchurMarkovScaleOperator lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixEulerSchurMarkovScaleOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul]

theorem suffixEulerSchurMarkovScaleOperator_cons
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerSchurMarkovScaleOperator lambda (p :: S) =
      primeSchurMarkovScaleOperator lambda p ∘L
        suffixEulerSchurMarkovScaleOperator lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixEulerSchurMarkovScaleOperator,
    suffixEulerSchurMarkovScalar, primeSchurMarkovScaleOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_smul]
  push_cast
  rfl

/-- One complete suffix is the preceding local relative numerator followed by
the reverse Markov scalar, plus the transported signed tail. -/
theorem suffixEulerDetectorRelativeNumeratorProduct_cons
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerDetectorRelativeNumeratorProduct owner lambda (p :: S) =
      suffixEulerFrameTransition lambda p S ∘L
          suffixEulerDetectorRelativeNumeratorProduct owner lambda S ∘L
            suffixEulerFrameReverseTransition lambda p S +
        suffixEulerDetectorRelativeNumerator owner lambda p S ∘L
          suffixEulerSchurMarkovScaleOperator lambda S := by
  have hscale :
      suffixEulerSchurMarkovScaleOperator lambda S ∘L
          suffixEulerFrameReverseTransition lambda p S =
        suffixEulerFrameReverseTransition lambda p S ∘L
          suffixEulerSchurMarkovScaleOperator lambda S :=
    suffixEulerSchurMarkovScaleOperator_comm lambda S _
  have h := relativeNumerator_two_step
    (suffixPolarDetectorCompression owner lambda (p :: S))
    (suffixPolarDetectorCompression owner lambda S)
    (suffixPolarDetectorCompression owner lambda [])
    (suffixEulerFrameTransition lambda p S)
    (suffixEulerTransitionProduct lambda S)
    (suffixEulerReverseTransitionProduct lambda S)
    (suffixEulerFrameReverseTransition lambda p S)
    (primeSchurMarkovScaleOperator lambda p)
    (suffixEulerSchurMarkovScaleOperator lambda S)
    (by simpa only [ContinuousLinearMap.mul_def] using hscale)
  have hscaleCons :
      primeSchurMarkovScaleOperator lambda p *
          suffixEulerSchurMarkovScaleOperator lambda S =
        suffixEulerSchurMarkovScaleOperator lambda (p :: S) := by
    simpa only [ContinuousLinearMap.mul_def] using
      (suffixEulerSchurMarkovScaleOperator_cons lambda p S).symm
  rw [hscaleCons] at h
  simpa only [suffixEulerDetectorRelativeNumeratorProduct,
    suffixEulerDetectorRelativeNumerator, suffixEulerTransitionProduct,
    suffixEulerReverseTransitionProduct,
    ContinuousLinearMap.mul_def] using h

/-- The recursively defined signed cocycle is exactly the complete relative
numerator.  This is the finite, same-object telescope; no primewise norm or
inverse Gram estimate is used. -/
theorem suffixEulerDetectorSignedCocycle_eq_relativeNumeratorProduct
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerDetectorSignedCocycle owner lambda S =
      suffixEulerDetectorRelativeNumeratorProduct owner lambda S := by
  induction S with
  | nil =>
      simp [suffixEulerDetectorSignedCocycle,
        suffixEulerDetectorRelativeNumeratorProduct,
        suffixEulerSchurMarkovScaleOperator,
        suffixEulerTransitionProduct, suffixEulerReverseTransitionProduct,
        suffixEulerSchurMarkovScalar, relativeNumerator,
        ContinuousLinearMap.mul_def]
  | cons p S ih =>
      rw [suffixEulerDetectorSignedCocycle,
        suffixEulerDetectorRelativeNumeratorProduct_cons, ih]

/-- The complete product has the promised ordered form, with the positive
scalar `rho_S` kept inside the subtraction. -/
theorem suffixEulerDetectorRelativeNumeratorProduct_eq_ordered
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerDetectorRelativeNumeratorProduct owner lambda S =
      suffixEulerTransitionProduct lambda S ∘L
          suffixPolarDetectorCompression owner lambda [] ∘L
            suffixEulerReverseTransitionProduct lambda S -
        suffixPolarDetectorCompression owner lambda S ∘L
          suffixEulerSchurMarkovScaleOperator lambda S := by
  rfl

end CCM24FiniteSSchurMarkovPairing
end CCM25Concrete
end Source
end ConnesWeilRH
