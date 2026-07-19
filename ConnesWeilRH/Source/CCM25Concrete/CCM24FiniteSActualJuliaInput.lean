/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaSchur
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedSoninProjection
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualMovingProjection

/-!
# Actual projection adapters for the Julia Schur input

The Julia Schur algebra can derive its complementary resolvent from an
orthogonal projection.  This module supplies the route-facing projection
source on the already constructed synchronized finite-S carrier.

The constructor below is a single time-slice adapter.  It does not claim that
an arbitrary list of such slices is the legal chronological Schur cascade;
that order and the physical-column Douglas estimate remain separate source
obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaInput

open CC20Concrete
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaSchur
open CCM24FiniteSJuliaCausal
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSGramProjectionCalculus

noncomputable local instance parameterizedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    CompleteSpace
      ((parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule) :=
  (parameterizedSoninClosedSubspace lambda alpha S halpha).isClosed.completeSpace_coe

/-! The projection used by the synchronized parameterized Sonin slice. -/
noncomputable def parameterizedPrimeEulerProjectedJuliaInput
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    PrimeEulerProjectedJuliaInput :=
  PrimeEulerProjectedJuliaInput.ofStarProjection p
    (parameterizedSoninProjection lambda alpha S halpha)
    (parameterizedSoninProjection_isStarProjection
      lambda alpha S halpha)

@[simp]
theorem parameterizedPrimeEulerProjectedJuliaInput_prime
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    (parameterizedPrimeEulerProjectedJuliaInput lambda alpha S halpha p).prime =
      p :=
  rfl

@[simp]
theorem parameterizedPrimeEulerProjectedJuliaInput_projection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    (parameterizedPrimeEulerProjectedJuliaInput lambda alpha S halpha p).projection =
      parameterizedSoninProjection lambda alpha S halpha :=
  rfl

@[simp]
theorem parameterizedPrimeEulerProjectedJuliaInput_resolvent
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    (parameterizedPrimeEulerProjectedJuliaInput lambda alpha S halpha p).resolvent =
      primeEulerProjectedComplementResolvent p
        (parameterizedSoninProjection lambda alpha S halpha) :=
  rfl

theorem parameterizedPrimeEulerProjectedJuliaInput_projection_eq_canonicalGram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    (parameterizedPrimeEulerProjectedJuliaInput lambda alpha S halpha p).projection =
      parameterizedCanonicalGramProjection lambda alpha S := by
  rw [parameterizedPrimeEulerProjectedJuliaInput_projection,
    parameterizedCanonicalGramProjection_eq_soninProjection]

/-!
The same construction at the endpoint is the existing finite-S projection.
This is the exact finite-S object; no new projection or resolvent witness is
introduced by the adapter.
-/
noncomputable def finiteSPrimeEulerProjectedJuliaInput
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) :
    PrimeEulerProjectedJuliaInput :=
  parameterizedPrimeEulerProjectedJuliaInput lambda 1 family.visiblePrimes
    (by norm_num) p

theorem finiteSPrimeEulerProjectedJuliaInput_projection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) :
    (finiteSPrimeEulerProjectedJuliaInput lambda family p).projection =
      targetSoninProjection lambda family := by
  unfold finiteSPrimeEulerProjectedJuliaInput
  rw [parameterizedPrimeEulerProjectedJuliaInput_projection]
  exact parameterizedSoninProjection_one lambda family.visiblePrimes

/-!
For a chosen ordered prime list, the suffix-oriented schedule below gives each
prime the actual synchronized Sonin projection of the remaining suffix.  This
is the concrete schedule needed by a reverse Schur traversal.  The theorem
does not identify this order with the final route order; that identification
is a separate transport equation, not a definitional simplification.
-/
noncomputable def suffixPrimeEulerProjectedJuliaInputs
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime → List PrimeEulerProjectedJuliaInput
  | [] => []
  | p :: S =>
      parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p ::
        suffixPrimeEulerProjectedJuliaInputs lambda S

@[simp]
theorem suffixPrimeEulerProjectedJuliaInputs_nil
    (lambda : CCM24SoninScale) :
    suffixPrimeEulerProjectedJuliaInputs lambda [] = [] :=
  rfl

@[simp]
theorem suffixPrimeEulerProjectedJuliaInputs_cons
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixPrimeEulerProjectedJuliaInputs lambda (p :: S) =
      parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p ::
        suffixPrimeEulerProjectedJuliaInputs lambda S :=
  rfl

theorem suffixPrimeEulerProjectedJuliaInputs_primes
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaInputs lambda S).map
        PrimeEulerProjectedJuliaInput.prime = S := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      simp only [suffixPrimeEulerProjectedJuliaInputs, List.map_cons,
        parameterizedPrimeEulerProjectedJuliaInput_prime, ih]

theorem suffixPrimeEulerProjectedJuliaInputs_projection_cons
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaInputs lambda (p :: S)).head?.map
        PrimeEulerProjectedJuliaInput.projection =
      some (parameterizedSoninProjection lambda 1 S (by norm_num)) := by
  simp only [suffixPrimeEulerProjectedJuliaInputs, List.head?_cons,
    Option.map_some, parameterizedPrimeEulerProjectedJuliaInput_projection]

/-! The corresponding colligation list is now fully source-owned. -/
noncomputable def suffixPrimeEulerProjectedJuliaColligations
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    List (ProjectedUnitaryColligation
      (finiteSCarrier →L[ℂ] finiteSCarrier)) :=
  (suffixPrimeEulerProjectedJuliaInputs lambda S).map
    PrimeEulerProjectedJuliaInput.toColligation

theorem suffixPrimeEulerProjectedJuliaColligations_primes
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaColligations lambda S).length = S.length := by
  simpa only [suffixPrimeEulerProjectedJuliaColligations, List.length_map] using
    congrArg List.length (suffixPrimeEulerProjectedJuliaInputs_primes lambda S)

theorem suffixPrimeEulerProjectedJuliaColligations_head_projection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaColligations lambda (p :: S)).head?.map
        ProjectedUnitaryColligation.projection =
      some (parameterizedSoninProjection lambda 1 S (by norm_num)) := by
  rfl

/-!
The source-owned colligation list can now carry the physical Schur-frame
range rows as well.  Every field below is indexed by the same prime and the
same remaining suffix as the projection itself.  This prevents a range row
from being paired with a different chronological carrier.
-/
structure SuffixPrimeEulerProjectedJuliaSchurFrameStepData
    (lambda : CCM24SoninScale) (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) where
  rangeSine : finiteSCarrier →L[ℂ] G
  /-- The independent readout on the fixed output carrier used by the
  fixed-source Julia cascade.  It is not inferred from the finite-S Schur
  readout below, whose domain is `finiteSCarrier`. -/
  fixedSourceReadout : G →L[ℂ] G
  readout : finiteSCarrier →L[ℂ] G
  transfer_contract :
    ContinuousLinearMap.adjoint
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).normalizedSchurFrame ∘L
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).normalizedSchurFrame ≤
      ContinuousLinearMap.id ℂ finiteSCarrier
  rangeSine_weighted_le : ∀ x : finiteSCarrier,
    primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
      ‖canonicalJuliaDefect
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).normalizedSchurFrame
        transfer_contract x‖ ^ 2
  rangeSine_readback :
    rangeSine = readout ∘L
      (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).toColligation.graphSine
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).toColligation.graphCosine

noncomputable def SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toSchurFrameStep
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    SchurFrameJuliaRangeStepData finiteSCarrier G :=
  (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).toPrimeSchurFrameJuliaRangeStepData
    data.rangeSine data.readout data.transfer_contract
    data.rangeSine_weighted_le data.rangeSine_readback

@[simp]
theorem SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toSchurFrameStep_colligation
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    data.toSchurFrameStep.colligation =
      (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S (by norm_num) p).toColligation :=
  rfl

/-!
The synchronized Schur row has an honest current-range realization at one
suffix.  Its frame is the subtype inclusion of the actual complete Sonin
intersection, and its ambient transfer is the normalized Schur frame.  This
is intentionally a single-step adapter: suffix carriers vary with the
remaining prime list and therefore cannot yet be assembled into the fixed-
carrier cascade consumed by the Bessel theorem.
-/
noncomputable def SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toCurrentRangeStepData
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    CurrentRangeJuliaStepData
      ((parameterizedSoninClosedSubspace lambda 1 S (by norm_num)).toSubmodule)
      finiteSCarrier G := by
  let range := parameterizedSoninClosedSubspace lambda 1 S (by norm_num)
  let frame := range.toSubmodule.subtypeL
  let input := parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
    (by norm_num) p
  let hnorm : ‖input.normalizedSchurFrame‖ ≤ 1 :=
    CCM24FiniteSJuliaCausal.norm_le_one_of_adjoint_comp_self_le_id
      input.normalizedSchurFrame
      data.transfer_contract
  refine
    { currentRange := range
      frame := frame
      frame_isometry := by
        intro x
        rfl
      frame_range := by
        intro y
        constructor
        · intro hy
          exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact x.property
      ambientTransfer := input.normalizedSchurFrame
      ambientTransfer_norm_le_one := hnorm
      ambientRangeSine := data.rangeSine
      weight := primeJuliaWeight p
      weight_nonneg := primeJuliaWeight_nonneg p
      rangeSine_weighted_le := ?_ }
  intro x
  have hambient := data.rangeSine_weighted_le (frame x)
  have hdefect := canonicalJuliaDefect_comp_frame_normSq_le
    frame input.normalizedSchurFrame (fun y => rfl) hnorm x
  simpa only [input, frame, range] using hambient.trans hdefect

theorem parameterizedPrimeEulerProjectedJuliaInput_projection_range
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (p : CCM24VisiblePrime) :
    (parameterizedPrimeEulerProjectedJuliaInput lambda alpha S halpha p).projection.range =
      (parameterizedSoninClosedSubspace lambda alpha S halpha).toSubmodule := by
  change (parameterizedSoninProjection lambda alpha S halpha).range = _
  unfold parameterizedSoninProjection
  rw [Submodule.range_starProjection]

noncomputable def suffixPrimeEulerProjectedJuliaSchurFrameSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime → List (SchurFrameJuliaRangeStepData
      finiteSCarrier G)
  | [] => []
  | p :: S =>
      (stepData p S).toSchurFrameStep ::
        suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData S

@[simp]
theorem suffixPrimeEulerProjectedJuliaSchurFrameSteps_nil
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData [] = [] :=
  rfl

@[simp]
theorem suffixPrimeEulerProjectedJuliaSchurFrameSteps_cons
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData (p :: S) =
      (stepData p S).toSchurFrameStep ::
        suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData S :=
  rfl

theorem suffixPrimeEulerProjectedJuliaSchurFrameSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData S).length =
      S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [ih]

theorem suffixPrimeEulerProjectedJuliaSchurFrameSteps_head_projection
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (suffixPrimeEulerProjectedJuliaSchurFrameSteps lambda stepData (p :: S)).head?.map
        (fun step => step.colligation.projection) =
      some (parameterizedSoninProjection lambda 1 S (by norm_num)) := by
  simp only [suffixPrimeEulerProjectedJuliaSchurFrameSteps,
    List.head?_cons, Option.map_some,
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData.toSchurFrameStep_colligation]
  rfl

end CCM24FiniteSActualJuliaInput
end CCM25Concrete
end Source
end ConnesWeilRH
