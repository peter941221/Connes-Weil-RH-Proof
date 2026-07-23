/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovUniformBound

/-!
# Orthogonal completed Julia synthesis

The rectangular Schur history is only a contractive image of the genuine
Julia co-defect history.  This module keeps the two objects separate.

The completed Julia analysis column is

```text
x |-> (terminal survivor, complete Julia co-defect column).
```

The Julia Pythagorean telescope makes this column an isometry.  Its Hilbert
adjoint is therefore a genuine synthesis map and is a left inverse of the
analysis.  The existing completed rectangular boundary column factors through
this analysis by a contraction; it is not declared orthogonal or invertible.

The final section lifts Proof 500's literal local raw defects through the
actual suffix Julia analysis and reads them back through the adjoint
synthesis.  This is an exact same-object connection.  It does not estimate
the resulting signed synthesis, prove Gate 3U, or assert a finite-S sign.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaSynthesis

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSGramResponse
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovCompletedReadout
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound
open CCM24SourceProlateTrace

/-! ## Generic orthogonal analysis and synthesis -/

/-- Hilbert carrier containing the terminal Julia survivor and every Julia
co-defect coordinate. -/
noncomputable abbrev completedJuliaCarrier
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :=
  WithLp 2
    (H × PiLp 2 (fun _ : Fin steps.length => H))

/-- The orthogonal completed Julia analysis column. -/
noncomputable def completedJuliaAnalysis
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    H →L[ℂ] completedJuliaCarrier steps :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H
      (PiLp 2 (fun _ : Fin steps.length => H))).symm.toContinuousLinearMap ∘L
    (juliaSurvivor steps).prod (juliaDefectColumn steps)

@[simp]
theorem completedJuliaAnalysis_apply
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    completedJuliaAnalysis steps x =
      WithLp.toLp 2
        (juliaSurvivor steps x, juliaDefectColumn steps x) := by
  rfl

/-- Exact norm-square preservation of the completed Julia column. -/
theorem completedJuliaAnalysis_normSq_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖completedJuliaAnalysis steps x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [completedJuliaAnalysis_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖juliaSurvivor steps x‖ ^ 2 +
      ‖juliaDefectColumn steps x‖ ^ 2 = ‖x‖ ^ 2
  rw [juliaDefectColumn_normSq_eq]
  simpa only [add_comm] using
    (juliaDefectEnergy_add_survivor_normSq steps x)

/-- The completed Julia analysis is an isometry. -/
theorem completedJuliaAnalysis_norm_eq
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (x : H) :
    ‖completedJuliaAnalysis steps x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact completedJuliaAnalysis_normSq_eq steps x

/-- The isometric analysis has operator norm at most one, including the
degenerate zero-carrier case. -/
theorem completedJuliaAnalysis_norm_le_one
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    ‖completedJuliaAnalysis steps‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using completedJuliaAnalysis_norm_eq steps x |>.le

/-- The completed synthesis is the Hilbert adjoint of the orthogonal
analysis column. -/
noncomputable def completedJuliaSynthesis
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    completedJuliaCarrier steps →L[ℂ] H :=
  (completedJuliaAnalysis steps)†

/-- The adjoint synthesis is a contraction. -/
theorem completedJuliaSynthesis_norm_le_one
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    ‖completedJuliaSynthesis steps‖ ≤ 1 := by
  rw [completedJuliaSynthesis, ContinuousLinearMap.adjoint.norm_map]
  exact completedJuliaAnalysis_norm_le_one steps

/-- The analysis Gram is exactly the identity. -/
theorem completedJuliaAnalysis_adjoint_comp_self
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    (completedJuliaAnalysis steps)† ∘L completedJuliaAnalysis steps =
      ContinuousLinearMap.id ℂ H := by
  simpa only [ContinuousLinearMap.one_def] using
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (completedJuliaAnalysis steps)).mp
        (completedJuliaAnalysis_norm_eq steps)

/-- Orthogonal synthesis followed by analysis recovers every source vector. -/
theorem completedJuliaSynthesis_comp_analysis_eq_id
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) :
    completedJuliaSynthesis steps ∘L completedJuliaAnalysis steps =
      ContinuousLinearMap.id ℂ H := by
  exact completedJuliaAnalysis_adjoint_comp_self steps

/-- Lift a source operator to the completed Julia carrier without changing
its source action after synthesis. -/
noncomputable def completedJuliaLift
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (operator : H →L[ℂ] H) :
    completedJuliaCarrier steps →L[ℂ] completedJuliaCarrier steps :=
  completedJuliaAnalysis steps ∘L operator ∘L
    completedJuliaSynthesis steps

/-- The lifted operator is read back exactly by the orthogonal synthesis. -/
theorem completedJuliaSynthesis_lift_analysis
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (JuliaDefectStep H G)) (operator : H →L[ℂ] H) :
    completedJuliaSynthesis steps ∘L completedJuliaLift steps operator ∘L
        completedJuliaAnalysis steps =
      operator := by
  apply ContinuousLinearMap.ext
  intro x
  have hleft := congrArg
    (fun map : H →L[ℂ] H => map (operator x))
    (completedJuliaSynthesis_comp_analysis_eq_id steps)
  have hright := congrArg
    (fun map : H →L[ℂ] H => map x)
    (completedJuliaSynthesis_comp_analysis_eq_id steps)
  have hleftPoint : completedJuliaSynthesis steps
      (completedJuliaAnalysis steps (operator x)) = operator x := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hleft
  have hrightPoint : completedJuliaSynthesis steps
      (completedJuliaAnalysis steps x) = x := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hright
  simp only [completedJuliaLift, ContinuousLinearMap.comp_apply]
  rw [hrightPoint, hleftPoint]

/-! ## The rectangular history is a contractive readout -/

/-- Apply the identity to the survivor coordinate and the Douglas contraction
to the Julia co-defect coordinates. -/
noncomputable def completedRectangularBoundaryCompression
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    completedJuliaCarrier
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) →L[ℂ]
      completedRectangularBoundaryCarrier steps :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H
      (PiLp 2 (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K))).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id ℂ H).prodMap
      (rectangularSchurCascadeBoundaryCoDefectFactor steps).factor) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ H
      (PiLp 2 (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => H))).toContinuousLinearMap

@[simp]
theorem completedRectangularBoundaryCompression_apply
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K))
    (x : completedJuliaCarrier
      (steps.map (fun step => step.toAdjointCoDefectJuliaStep))) :
    completedRectangularBoundaryCompression steps x =
      WithLp.toLp 2
        (x.fst,
          (rectangularSchurCascadeBoundaryCoDefectFactor steps).factor x.snd) := by
  rfl

/-- The physical rectangular history is a contractive image of the genuine
orthogonal Julia history. -/
theorem completedRectangularBoundaryCompression_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    ‖completedRectangularBoundaryCompression steps‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hfactorNorm :
      ‖(rectangularSchurCascadeBoundaryCoDefectFactor steps).factor x.snd‖ ≤
        ‖x.snd‖ := by
    calc
      ‖(rectangularSchurCascadeBoundaryCoDefectFactor steps).factor x.snd‖ ≤
          ‖(rectangularSchurCascadeBoundaryCoDefectFactor steps).factor‖ *
            ‖x.snd‖ :=
        (rectangularSchurCascadeBoundaryCoDefectFactor steps).factor.le_opNorm _
      _ ≤ 1 * ‖x.snd‖ := by
        exact mul_le_mul_of_nonneg_right
          (rectangularSchurCascadeBoundaryCoDefectFactor steps).factor_norm_le_one
          (norm_nonneg _)
      _ = ‖x.snd‖ := one_mul _
  have hfactorSq :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hfactorNorm
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [completedRectangularBoundaryCompression_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖x.fst‖ ^ 2 +
      ‖(rectangularSchurCascadeBoundaryCoDefectFactor steps).factor x.snd‖ ^ 2 ≤
    ‖x‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  exact add_le_add (le_refl _) hfactorSq

/-- The old rectangular column is exactly a readout of the orthogonal Julia
analysis. -/
theorem completedRectangularBoundaryCompression_comp_analysis
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    completedRectangularBoundaryCompression steps ∘L
        completedJuliaAnalysis
          (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) =
      completedRectangularBoundaryColumn steps := by
  apply ContinuousLinearMap.ext
  intro x
  have hfactor := congrArg
    (fun map : H →L[ℂ] PiLp 2
        (fun _ : Fin (steps.map
          (fun step => step.toAdjointCoDefectJuliaStep)).length => K) => map x)
      (rectangularSchurCascadeBoundaryCoDefectFactor steps).factorization
  change completedRectangularBoundaryCompression steps
      (completedJuliaAnalysis
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) x) =
    completedRectangularBoundaryColumn steps x
  rw [completedRectangularBoundaryCompression_apply,
    completedJuliaAnalysis_apply, completedRectangularBoundaryColumn_apply]
  exact congrArg (WithLp.toLp 2) (Prod.ext rfl hfactor)

/-- The adjoint rectangular column factors through the genuine Julia
synthesis. -/
theorem completedRectangularBoundaryColumn_adjoint_factorization
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    (completedRectangularBoundaryColumn steps)† =
      completedJuliaSynthesis
          (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
        (completedRectangularBoundaryCompression steps)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (completedRectangularBoundaryCompression_comp_analysis steps)
  simpa only [completedJuliaSynthesis,
    ContinuousLinearMap.adjoint_comp] using h.symm

/-! ## Actual suffix synthesis and Proof 500 readback -/

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual completed Julia analysis for a literal suffix list. -/
noncomputable def suffixEulerCompletedJuliaAnalysis
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ]
      completedJuliaCarrier (suffixEulerFrameCoDefectSteps lambda S) :=
  completedJuliaAnalysis (suffixEulerFrameCoDefectSteps lambda S)

/-- The actual orthogonal synthesis for a literal suffix list. -/
noncomputable def suffixEulerCompletedJuliaSynthesis
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    completedJuliaCarrier (suffixEulerFrameCoDefectSteps lambda S) →L[ℂ]
      sourceSoninCarrier lambda :=
  completedJuliaSynthesis (suffixEulerFrameCoDefectSteps lambda S)

theorem suffixEulerCompletedJuliaSynthesis_comp_analysis
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerCompletedJuliaSynthesis lambda S ∘L
        suffixEulerCompletedJuliaAnalysis lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  exact completedJuliaSynthesis_comp_analysis_eq_id
    (suffixEulerFrameCoDefectSteps lambda S)

/-- The concrete rectangular suffix history is a contraction image of the
orthogonal suffix Julia analysis. -/
theorem suffixEulerRectangularHistory_factors_through_completedJulia
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    completedRectangularBoundaryCompression
          (suffixEulerFrameSchurSteps lambda S) ∘L
        suffixEulerCompletedJuliaAnalysis lambda S =
      completedRectangularBoundaryColumn
        (suffixEulerFrameSchurSteps lambda S) := by
  simpa only [suffixEulerCompletedJuliaAnalysis,
    suffixEulerFrameCoDefectSteps] using
      (completedRectangularBoundaryCompression_comp_analysis
        (suffixEulerFrameSchurSteps lambda S))

/-- The local polar detector defect uses the actual rectangular boundary as
its left leg. -/
theorem suffixEulerDetectorBoundaryDefect_eq_stepBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerDetectorBoundaryDefect owner lambda p S =
      -((suffixEulerFrameSchurStep lambda p S).boundary ∘L
        detectorOperator owner ∘L newSuffixFrame lambda S) := by
  rfl

/-- The polar boundary left leg factors through the canonical Julia
co-defect of the same adjacent-frame step. -/
theorem suffixEulerDetectorBoundaryDefect_eq_juliaCoDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerDetectorBoundaryDefect owner lambda p S =
      -((suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        ((suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor.factor)† ∘L
        detectorOperator owner ∘L newSuffixFrame lambda S) := by
  rw [suffixEulerDetectorBoundaryDefect_eq_stepBoundary]
  rw [(suffixEulerFrameSchurStep lambda p S).boundaryCoDefectFactor
    |>.boundary_eq_leftCoDefect_comp_factor_adjoint]
  rfl

/-- Proof 500's local raw defect lifted to the actual orthogonal completed
Julia carrier of the larger suffix. -/
noncomputable def suffixActualBandLocalRawDefectJuliaLift
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    completedJuliaCarrier
        (suffixEulerFrameCoDefectSteps lambda (p :: S)) →L[ℂ]
      completedJuliaCarrier
        (suffixEulerFrameCoDefectSteps lambda (p :: S)) :=
  completedJuliaLift (suffixEulerFrameCoDefectSteps lambda (p :: S))
    (suffixActualBandLocalRawDefect owner lambda p S)

/-- The lifted local term is exactly Proof 500's local term after synthesis;
no surrogate trace operator is introduced. -/
theorem suffixActualBandLocalRawDefect_eq_completedJuliaReadback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerCompletedJuliaSynthesis lambda (p :: S) ∘L
        suffixActualBandLocalRawDefectJuliaLift owner lambda p S ∘L
          suffixEulerCompletedJuliaAnalysis lambda (p :: S) =
      suffixActualBandLocalRawDefect owner lambda p S := by
  exact completedJuliaSynthesis_lift_analysis
    (suffixEulerFrameCoDefectSteps lambda (p :: S))
    (suffixActualBandLocalRawDefect owner lambda p S)

/-- Relative local trace recurrence written through the genuine orthogonal
completed Julia synthesis at every suffix. -/
noncomputable def suffixActualBandCompletedJuliaRelativeTrace
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    List CCM24VisiblePrime → ℂ
  | [] => 0
  | p :: S =>
      suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis S +
        (primeSchurMarkovScalar p : ℂ)⁻¹ *
          ordinaryTraceAlong sourceBasis
            (suffixEulerCompletedJuliaSynthesis lambda (p :: S) ∘L
              suffixActualBandLocalRawDefectJuliaLift owner lambda p S ∘L
                suffixEulerCompletedJuliaAnalysis lambda (p :: S))

/-- The completed-Julia recurrence is definitionally the same relative local
trace sum proved legal in Proof 500. -/
theorem suffixActualBandCompletedJuliaRelativeTrace_eq_relativeCollapsed
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) :
    suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis S =
      suffixActualBandRelativeCollapsedTrace owner lambda
        (ordinaryTraceAlong sourceBasis) S := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      rw [suffixActualBandCompletedJuliaRelativeTrace,
        suffixActualBandRelativeCollapsedTrace, ih,
        suffixActualBandLocalRawDefect_eq_completedJuliaReadback]

/-! The following theorem is the direct connection to Proof 500.  Its long
list of bases is inherited from the complete four-branch trace-class owner. -/

section Proof500Readback

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (pairedBoundaryBasis : HilbertBasis sigma ℂ
  (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

include a c hac hsupp negativeBasis positiveBasis outputBasis
  reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
  globalBasis boundaryBasis pairedBoundaryBasis hfactor

/-- Proof 500's relative ordinary trace is exactly the trace read back from
the genuine completed Julia synthesis at every chronological suffix. -/
theorem ordinaryTraceAlong_suffixActualBandRawResponse_eq_completedJulia
    (S : List CCM24VisiblePrime) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawQuadraticCycledResponse owner lambda S) =
      suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis S := by
  rw [suffixActualBandCompletedJuliaRelativeTrace_eq_relativeCollapsed]
  exact ordinaryTraceAlong_suffixActualBandRawResponse_eq_relativeCollapsed
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor S

/-- The corrected signed cocycle is the positive complete Schur--Markov
scalar times the completed-Julia relative trace. -/
theorem ordinaryTraceAlong_completedSignedCocycle_eq_rho_mul_completedJulia
    (family : FinitePrimePowerFamily) :
    ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family) =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis
          family.visiblePrimes := by
  have hresponse :=
    lowerFactorGaugedActualBandCompletedRelativeResponse_isTraceClassAlong
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  calc
    ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family) =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family) :=
      ordinaryTraceAlong_suffixEulerCompletedSignedCocycle_eq_scaledResponse
        owner lambda family sourceBasis hresponse
    _ = (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandRawQuadraticCycledResponse owner lambda
            family.visiblePrimes) := by
      rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder,
        suffixActualBandRawQuadraticCycledResponse_eq_actual]
    _ = (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis
          family.visiblePrimes := by
      rw [ordinaryTraceAlong_suffixActualBandRawResponse_eq_completedJulia
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor]

/-- The missing Gate 3U estimate is exactly the unscaled bound on the genuine
completed-Julia relative trace. -/
theorem completedSignedCocycle_rho_bound_iff_completedJulia_bound
    (family : FinitePrimePowerFamily) (bound : ℝ) :
    ‖ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family)‖ ≤
        suffixEulerSchurMarkovScalar family.visiblePrimes * bound ↔
      ‖suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis
        family.visiblePrimes‖ ≤ bound := by
  rw [ordinaryTraceAlong_completedSignedCocycle_eq_rho_mul_completedJulia
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suffixEulerSchurMarkovScalar_pos family.visiblePrimes)]
  constructor
  · intro h
    nlinarith [suffixEulerSchurMarkovScalar_pos family.visiblePrimes]
  · intro h
    exact mul_le_mul_of_nonneg_left h
      (le_of_lt (suffixEulerSchurMarkovScalar_pos family.visiblePrimes))

/-- Proof 498 gives only the scaled completed-Julia bound.  The factor
`rho_S` remains on the left and cannot be discarded uniformly in `S`. -/
theorem rho_mul_completedJulia_trace_norm_le_supportEnergy
    (family : FinitePrimePowerFamily) :
    suffixEulerSchurMarkovScalar family.visiblePrimes *
        ‖suffixActualBandCompletedJuliaRelativeTrace owner lambda sourceBasis
          family.visiblePrimes‖ ≤
      (18 + 6 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  have hbound :=
    suffixEulerLowerFactorCompletedSignedCocycle_trace_norm_le_supportEnergy
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  rw [ordinaryTraceAlong_completedSignedCocycle_eq_rho_mul_completedJulia
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis pairedBoundaryBasis hfactor,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suffixEulerSchurMarkovScalar_pos family.visiblePrimes)] at hbound
  exact hbound

end Proof500Readback

end CCM24FiniteSCompletedJuliaSynthesis
end CCM25Concrete
end Source
end ConnesWeilRH
