/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovCompletedReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPolarTraceBridge

/-!
# Local completed Schur--Markov cocycle

The endpoint Schur--Markov numerator is only the projection increment.  Gate
3U concerns the raw quadratic remainder, so the matching first-jet increment
must be combined with that endpoint increment before any absolute value is
taken.  This module constructs that local completed defect on the literal
source Sonin carrier.

The construction is list-level.  Its recursive cocycle is exactly the
Schur--Markov scalar times the existing raw quadratic cycle.  A separate
ring theorem records the finite trace-collapse contract: a cyclic linear
trace removes every completed forward/reverse prefix and leaves the weighted
sum of the local completed defects.

No ordinary-trace cyclicity, local trace-class factorization, energy bound,
Gate 3U estimate, sign statement, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRawCompletedSchurCocycle

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalMarkov
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovPolarTraceBridge

/-! ## Abstract finite trace-collapse contract -/

variable {A I : Type*} [Ring A]

/-- A paired cocycle with the forward and reverse histories kept on their
literal sides of every local completed defect. -/
def pairedCompletedCocycle
    (base : A) (forward reverse localTerm : I -> List I -> A) : List I -> A
  | [] => base
  | item :: suffix =>
      forward item suffix *
          pairedCompletedCocycle base forward reverse localTerm suffix *
            reverse item suffix +
        localTerm item suffix

/-- Scalar recurrence obtained after a legal cyclic trace has removed the
paired history around every local completed defect. -/
def pairedCompletedCollapsedTrace
    (traceLike : A -> ℂ) (base : A) (weight : I -> ℂ)
    (localTerm : I -> List I -> A) : List I -> ℂ
  | [] => traceLike base
  | item :: suffix =>
      weight item *
          pairedCompletedCollapsedTrace traceLike base weight localTerm suffix +
        traceLike (localTerm item suffix)

/-- Complete list-level trace collapse.  Analytic use with an ordinary trace
must first prove the required local trace-class and cyclicity statements; the
unrestricted hypotheses here are an algebraic contract, not stored analytic
data. -/
theorem traceLike_pairedCompletedCocycle_eq_collapsed
    (traceLike : A -> ℂ)
    (hadd : forall x y, traceLike (x + y) = traceLike x + traceLike y)
    (hcyclic : forall x y, traceLike (x * y) = traceLike (y * x))
    (base : A) (forward reverse localTerm : I -> List I -> A)
    (scale : I -> A) (weight : I -> ℂ)
    (hpair : forall item suffix,
      reverse item suffix * forward item suffix = scale item)
    (hscale : forall item x,
      traceLike (x * scale item) = weight item * traceLike x) :
    forall items,
      traceLike
          (pairedCompletedCocycle base forward reverse localTerm items) =
        pairedCompletedCollapsedTrace traceLike base weight localTerm items := by
  intro items
  induction items with
  | nil => rfl
  | cons item suffix ih =>
      rw [pairedCompletedCocycle, pairedCompletedCollapsedTrace, hadd]
      congr 1
      calc
        traceLike
            (forward item suffix *
                pairedCompletedCocycle base forward reverse localTerm suffix *
                  reverse item suffix) =
            traceLike
              (forward item suffix *
                (pairedCompletedCocycle base forward reverse localTerm suffix *
                  reverse item suffix)) := by rw [mul_assoc]
        _ = traceLike
            ((pairedCompletedCocycle base forward reverse localTerm suffix *
                reverse item suffix) * forward item suffix) :=
          hcyclic _ _
        _ = traceLike
            (pairedCompletedCocycle base forward reverse localTerm suffix *
              (reverse item suffix * forward item suffix)) := by
          rw [mul_assoc]
        _ = traceLike
            (pairedCompletedCocycle base forward reverse localTerm suffix *
              scale item) := by rw [hpair]
        _ = weight item * traceLike
            (pairedCompletedCocycle base forward reverse localTerm suffix) :=
          hscale _ _
        _ = weight item *
            pairedCompletedCollapsedTrace traceLike base weight localTerm suffix :=
          by rw [ih]

/-! ## Actual list-level quadratic cycle -/

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The normalized-inverse root leg for an arbitrary visible-prime list. -/
noncomputable def suffixActualBandJetRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceBandProjection lambda ∘L
    normalizedFiniteEulerInverseList S ∘L sourceInclusion lambda

/-- The target frame root leg for an arbitrary visible-prime list. -/
noncomputable def suffixActualBandTargetFrameRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L
    CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame lambda 1 S

/-- The corresponding route-ordered target dual root leg. -/
noncomputable def suffixActualBandTargetDualRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L
      CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame lambda 1 S ∘L
    CCM24FiniteSGramInverseCalculus.parameterizedSoninGramInv
      lambda 1 S (by norm_num)

/-- The actual paired first jet, defined before a prime-power family wrapper
is chosen. -/
noncomputable def suffixActualBandFirstJetCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (actualBandBaseRootLeg owner lambda)† ∘L
      suffixActualBandJetRootLeg owner lambda S +
    (suffixActualBandJetRootLeg owner lambda S)† ∘L
      actualBandBaseRootLeg owner lambda

/-- The route-ordered endpoint cycle for an arbitrary visible-prime list. -/
noncomputable def suffixActualBandEndpointCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (actualBandBaseRootLeg owner lambda)† ∘L
      actualBandBaseRootLeg owner lambda -
    (suffixActualBandTargetFrameRootLeg owner lambda S)† ∘L
      suffixActualBandTargetDualRootLeg owner lambda S

/-- The raw first-jet-minus-endpoint response on a literal suffix list. -/
noncomputable def suffixActualBandRawQuadraticCycledResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  suffixActualBandFirstJetCycledResponse owner lambda S -
    suffixActualBandEndpointCycledResponse owner lambda S

theorem suffixActualBandJetRootLeg_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandJetRootLeg owner lambda family.visiblePrimes =
      actualBandJetRootLeg owner lambda family := by
  rw [suffixActualBandJetRootLeg, actualBandJetRootLeg,
    normalizedFiniteEulerInverse_eq_causalAverage,
    finiteEulerCausalAverage_eq_normalizedInverse]

theorem suffixActualBandTargetFrameRootLeg_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandTargetFrameRootLeg owner lambda family.visiblePrimes =
      actualBandTargetFrameRootLeg owner lambda family := by
  rw [suffixActualBandTargetFrameRootLeg, actualBandTargetFrameRootLeg,
    parameterizedSoninFrame_one_eq_finiteEulerFrame]

theorem suffixActualBandTargetDualRootLeg_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandTargetDualRootLeg owner lambda family.visiblePrimes =
      actualBandTargetDualRootLeg owner lambda family := by
  rw [suffixActualBandTargetDualRootLeg, actualBandTargetDualRootLeg,
    finiteEulerDualFrame, parameterizedSoninFrame_one_eq_finiteEulerFrame,
    parameterizedSoninGramInv_one_eq_finiteEulerGramInv]

theorem suffixActualBandRawQuadraticCycledResponse_eq_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandRawQuadraticCycledResponse owner lambda
        family.visiblePrimes =
      sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [suffixActualBandRawQuadraticCycledResponse,
    suffixActualBandFirstJetCycledResponse,
    suffixActualBandEndpointCycledResponse,
    suffixActualBandJetRootLeg_eq_actual,
    suffixActualBandTargetFrameRootLeg_eq_actual,
    suffixActualBandTargetDualRootLeg_eq_actual]
  change actualBandQuadraticCycledResponse owner lambda family =
    sourceActualBandFiniteEulerRemainderResponse owner lambda family
  exact
    (sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle
      owner lambda family).symm

/-- The raw quadratic cycle has no base term.  At the empty visible-prime
list the normalized inverse is the identity, the quotient-band jet vanishes,
and the target frame and dual frame are both the fixed source inclusion. -/
theorem suffixActualBandRawQuadraticCycledResponse_nil_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    suffixActualBandRawQuadraticCycledResponse owner lambda [] = 0 := by
  have hInverse :
      normalizedFiniteEulerInverseList [] =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
    have h := finiteEulerCausalAverage_eq_normalizedInverse []
    simpa only [finiteEulerCausalAverage] using h.symm
  have hJet : suffixActualBandJetRootLeg owner lambda [] = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hBand := DFunLike.congr_fun
      (sourceBandProjection_comp_sourceInclusion_eq_zero lambda) u
    simp only [suffixActualBandJetRootLeg, ContinuousLinearMap.comp_apply,
      hInverse, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply] at hBand ⊢
    rw [hBand, map_zero]
  have hFrame : suffixActualBandTargetFrameRootLeg owner lambda [] =
      actualBandBaseRootLeg owner lambda := by
    rw [suffixActualBandTargetFrameRootLeg, actualBandBaseRootLeg,
      parameterizedSoninFrame_one_nil_eq_sourceInclusion]
  have hDual : suffixActualBandTargetDualRootLeg owner lambda [] =
      actualBandBaseRootLeg owner lambda := by
    rw [suffixActualBandTargetDualRootLeg, actualBandBaseRootLeg,
      parameterizedSoninFrame_one_nil_eq_sourceInclusion,
      parameterizedSoninGramInv_one_nil_eq_id,
      ContinuousLinearMap.comp_id]
  have hAdjointZero :
      ContinuousLinearMap.adjoint
          (0 : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  have hJetAdjoint :
      (suffixActualBandJetRootLeg owner lambda [])† = 0 := by
    rw [hJet, hAdjointZero]
  rw [suffixActualBandRawQuadraticCycledResponse,
    suffixActualBandFirstJetCycledResponse,
    suffixActualBandEndpointCycledResponse, hJetAdjoint, hJet, hFrame, hDual]
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
    zero_add, sub_self]

/-! ## Local completed defects -/

/-- The Schur--Markov-scaled raw quadratic response. -/
noncomputable def suffixActualBandScaledRawResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    SourceOp lambda :=
  (suffixEulerSchurMarkovScalar S : ℂ) •
    suffixActualBandRawQuadraticCycledResponse owner lambda S

@[simp]
theorem suffixActualBandScaledRawResponse_nil_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    suffixActualBandScaledRawResponse owner lambda [] = 0 := by
  rw [suffixActualBandScaledRawResponse,
    suffixActualBandRawQuadraticCycledResponse_nil_eq_zero, smul_zero]

/-- The one-step raw defect after only the one-prime Schur--Markov scalar has
been inserted.  The complete suffix scalar is deliberately absent. -/
noncomputable def suffixActualBandLocalRawDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (primeSchurMarkovScalar p : ℂ) •
      suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S

/-- The one-step completed defect.  The complete first jet and the complete
route-ordered endpoint are already combined inside each scaled raw response. -/
noncomputable def suffixActualBandLocalCompletedDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandScaledRawResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandScaledRawResponse owner lambda S ∘L
        suffixEulerFrameReverseTransition lambda p S

/-- Every local completed defect contains the exact scalar of its remaining
suffix.  This is the tail factor which combines with the cyclic prefix
weights to recover the full Schur--Markov scalar. -/
theorem suffixActualBandLocalCompletedDefect_eq_suffixScalar_smul_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalCompletedDefect owner lambda p S =
      (suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandLocalRawDefect owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandLocalCompletedDefect,
    suffixActualBandScaledRawResponse, suffixActualBandLocalRawDefect,
    suffixEulerSchurMarkovScalar, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_smul, smul_sub, smul_smul]
  push_cast
  rw [mul_comm (primeSchurMarkovScalar p : ℂ)
    (suffixEulerSchurMarkovScalar S : ℂ)]

/-- The matching local first-jet defect. -/
noncomputable def suffixActualBandLocalFirstJetDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
      suffixActualBandFirstJetCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      ((suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandFirstJetCycledResponse owner lambda S) ∘L
          suffixEulerFrameReverseTransition lambda p S

/-- The matching local ordered-endpoint defect. -/
noncomputable def suffixActualBandLocalEndpointDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (suffixEulerSchurMarkovScalar (p :: S) : ℂ) •
      suffixActualBandEndpointCycledResponse owner lambda (p :: S) -
    suffixEulerFrameTransition lambda p S ∘L
      ((suffixEulerSchurMarkovScalar S : ℂ) •
        suffixActualBandEndpointCycledResponse owner lambda S) ∘L
          suffixEulerFrameReverseTransition lambda p S

/-- Each local raw term is completed before it enters the cocycle: it is the
local paired first jet minus the local route-ordered endpoint. -/
theorem suffixActualBandLocalCompletedDefect_eq_firstJet_sub_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalCompletedDefect owner lambda p S =
      suffixActualBandLocalFirstJetDefect owner lambda p S -
        suffixActualBandLocalEndpointDefect owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [suffixActualBandLocalCompletedDefect,
    suffixActualBandScaledRawResponse,
    suffixActualBandRawQuadraticCycledResponse,
    suffixActualBandLocalFirstJetDefect,
    suffixActualBandLocalEndpointDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, map_sub, smul_sub]
  abel

/-- Recursive assembly of the local completed defects. -/
noncomputable def suffixActualBandCompletedDefectCocycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime -> SourceOp lambda :=
  pairedCompletedCocycle
    (suffixActualBandScaledRawResponse owner lambda [])
    (suffixEulerFrameTransition lambda)
    (suffixEulerFrameReverseTransition lambda)
    (suffixActualBandLocalCompletedDefect owner lambda)

/-- Scalar trace recurrence for the actual local completed defects.  This is
only a target shape: applying it to an ordinary infinite-dimensional trace
still requires the relevant trace-class and cyclicity theorems. -/
noncomputable def suffixActualBandCompletedCollapsedTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (traceLike : (SourceOp lambda) -> ℂ) :
    List CCM24VisiblePrime -> ℂ :=
  pairedCompletedCollapsedTrace traceLike 0
    (fun p => (primeSchurMarkovScalar p : ℂ))
    (suffixActualBandLocalCompletedDefect owner lambda)

/-- The relative scalar recurrence left after the complete Schur--Markov
factor is extracted.  Each local raw defect is divided only by its one-prime
positive scalar, never by the complete finite-family product. -/
noncomputable def suffixActualBandRelativeCollapsedTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (traceLike : (SourceOp lambda) -> ℂ) :
    List CCM24VisiblePrime -> ℂ
  | [] => 0
  | p :: S =>
      suffixActualBandRelativeCollapsedTrace owner lambda traceLike S +
        (primeSchurMarkovScalar p : ℂ)⁻¹ *
          traceLike (suffixActualBandLocalRawDefect owner lambda p S)

/-- The complete recursive cocycle is exactly the scaled raw quadratic
response.  This is an operator identity; no trace cycle is used. -/
theorem suffixActualBandCompletedDefectCocycle_eq_scaledRaw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandCompletedDefectCocycle owner lambda S =
      suffixActualBandScaledRawResponse owner lambda S := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      have ih' :
          pairedCompletedCocycle
              (suffixActualBandScaledRawResponse owner lambda [])
              (suffixEulerFrameTransition lambda)
              (suffixEulerFrameReverseTransition lambda)
              (suffixActualBandLocalCompletedDefect owner lambda) S =
            suffixActualBandScaledRawResponse owner lambda S := by
        simpa only [suffixActualBandCompletedDefectCocycle] using ih
      rw [suffixActualBandCompletedDefectCocycle,
        pairedCompletedCocycle, ih',
        suffixActualBandLocalCompletedDefect]
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      abel

/-- Under an explicitly supplied cyclic linear trace contract, the actual
scaled raw remainder collapses to the scalar recurrence of its local
first-jet-minus-endpoint defects.  No unrestricted ordinary-trace cyclicity
is asserted by this theorem. -/
theorem traceLike_suffixActualBandScaledRawResponse_eq_collapsed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (traceLike : (SourceOp lambda) -> ℂ)
    (hadd : forall x y, traceLike (x + y) = traceLike x + traceLike y)
    (hcyclic : forall x y, traceLike (x * y) = traceLike (y * x))
    (hsmul : forall z x, traceLike (z • x) = z * traceLike x)
    (S : List CCM24VisiblePrime) :
    traceLike (suffixActualBandScaledRawResponse owner lambda S) =
      suffixActualBandCompletedCollapsedTrace owner lambda traceLike S := by
  have hpair : forall p suffix,
      suffixEulerFrameReverseTransition lambda p suffix *
          suffixEulerFrameTransition lambda p suffix =
        (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    intro p suffix
    simpa only [ContinuousLinearMap.mul_def] using
      suffixEulerFrameReverse_comp_transition lambda p suffix
  have hscale : forall p (x : SourceOp lambda),
      traceLike
          (x * ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda))) =
        (primeSchurMarkovScalar p : ℂ) * traceLike x := by
    intro p x
    have hx :
        x * ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)) =
          (primeSchurMarkovScalar p : ℂ) • x := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul]
    rw [hx]
    exact hsmul _ _
  have hcollapse :
      traceLike (suffixActualBandCompletedDefectCocycle owner lambda S) =
        pairedCompletedCollapsedTrace traceLike
          (suffixActualBandScaledRawResponse owner lambda [])
          (fun p => (primeSchurMarkovScalar p : ℂ))
          (suffixActualBandLocalCompletedDefect owner lambda) S := by
    simpa only [suffixActualBandCompletedDefectCocycle] using
      (traceLike_pairedCompletedCocycle_eq_collapsed traceLike hadd hcyclic
        (suffixActualBandScaledRawResponse owner lambda [])
        (suffixEulerFrameTransition lambda)
        (suffixEulerFrameReverseTransition lambda)
        (suffixActualBandLocalCompletedDefect owner lambda)
        (fun p => (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda))
        (fun p => (primeSchurMarkovScalar p : ℂ)) hpair hscale S)
  rw [suffixActualBandCompletedDefectCocycle_eq_scaledRaw] at hcollapse
  simpa only [suffixActualBandCompletedCollapsedTrace,
    suffixActualBandScaledRawResponse_nil_eq_zero] using hcollapse

/-- A complex-linear trace readout extracts the complete Schur--Markov scalar
from the collapsed recurrence.  The remaining object is the signed relative
sum of the normalized local raw defects. -/
theorem suffixActualBandCompletedCollapsedTrace_eq_scalar_mul_relative
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (traceLike : (SourceOp lambda) -> ℂ)
    (hsmul : forall z x, traceLike (z • x) = z * traceLike x)
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompletedCollapsedTrace owner lambda traceLike S =
      (suffixEulerSchurMarkovScalar S : ℂ) *
        suffixActualBandRelativeCollapsedTrace owner lambda traceLike S := by
  induction S with
  | nil =>
      have hzero : traceLike 0 = 0 := by
        simpa only [zero_smul, zero_mul] using
          hsmul (0 : ℂ) (0 : SourceOp lambda)
      simp only [suffixActualBandCompletedCollapsedTrace,
        pairedCompletedCollapsedTrace, suffixEulerSchurMarkovScalar,
        suffixActualBandRelativeCollapsedTrace, hzero, Complex.ofReal_one,
        one_mul]
  | cons p S ih =>
      have ih' :
          pairedCompletedCollapsedTrace traceLike 0
              (fun p => (primeSchurMarkovScalar p : ℂ))
              (suffixActualBandLocalCompletedDefect owner lambda) S =
            (suffixEulerSchurMarkovScalar S : ℂ) *
              suffixActualBandRelativeCollapsedTrace
                owner lambda traceLike S := by
        simpa only [suffixActualBandCompletedCollapsedTrace] using ih
      rw [suffixActualBandCompletedCollapsedTrace,
        pairedCompletedCollapsedTrace,
        suffixActualBandRelativeCollapsedTrace,
        suffixEulerSchurMarkovScalar, ih',
        suffixActualBandLocalCompletedDefect_eq_suffixScalar_smul_raw,
        hsmul]
      push_cast
      have hp : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
      field_simp [hp]

/-- The cyclic trace contract therefore reads the raw quadratic response as
the relative sum of its local completed defects.  The positive complete
scalar is cancelled only after it has been produced on both sides. -/
theorem traceLike_suffixActualBandRawResponse_eq_relativeCollapsed
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (traceLike : (SourceOp lambda) -> ℂ)
    (hadd : forall x y, traceLike (x + y) = traceLike x + traceLike y)
    (hcyclic : forall x y, traceLike (x * y) = traceLike (y * x))
    (hsmul : forall z x, traceLike (z • x) = z * traceLike x)
    (S : List CCM24VisiblePrime) :
    traceLike (suffixActualBandRawQuadraticCycledResponse owner lambda S) =
      suffixActualBandRelativeCollapsedTrace owner lambda traceLike S := by
  have h := traceLike_suffixActualBandScaledRawResponse_eq_collapsed
    owner lambda traceLike hadd hcyclic hsmul S
  rw [suffixActualBandCompletedCollapsedTrace_eq_scalar_mul_relative
    owner lambda traceLike hsmul S] at h
  rw [suffixActualBandScaledRawResponse, hsmul] at h
  exact mul_left_cancel₀
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (suffixEulerSchurMarkovScalar_pos S))) h

/-- Readback on the exact prime list derived from an arithmetic family. -/
theorem suffixActualBandCompletedDefectCocycle_eq_scaledSourceRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixActualBandCompletedDefectCocycle owner lambda
        family.visiblePrimes =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
        sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [suffixActualBandCompletedDefectCocycle_eq_scaledRaw,
    suffixActualBandScaledRawResponse,
    suffixActualBandRawQuadraticCycledResponse_eq_actual]

end CCM24FiniteSRawCompletedSchurCocycle
end CCM25Concrete
end Source
end ConnesWeilRH
