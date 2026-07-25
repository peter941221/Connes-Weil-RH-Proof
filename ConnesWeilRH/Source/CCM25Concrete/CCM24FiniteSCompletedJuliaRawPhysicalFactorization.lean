/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalReadout

/-!
# Component factorization for the raw physical readout

Proof 531 reduces Gate 3U to a bounded readout of the recombined raw row from
the actual ambient-plus-boundary analysis column.  This module lowers that
readout obligation one more step: it is enough to give two component rows,
one on the antiresonant ambient-loss coordinate and one on the moving-boundary
coordinate, whose sum is the exact four-term raw physical normal form.

This is still not a producer of the family-uniform estimate.  It only records
the exact interface that a source-specific bound must satisfy.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Packing two physical component rows -/

/-- A readout from the two-coordinate physical carrier, built from an
ambient-loss row and a moving-boundary row. -/
noncomputable def suffixEulerFrameAmbientBoundaryReadoutOfRows
    {lambda : CCM24SoninScale}
    (ambientRow boundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  (ContinuousLinearMap.coprod ambientRow boundaryRow) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      finiteSCarrier finiteSCarrier).toContinuousLinearMap

@[simp]
theorem suffixEulerFrameAmbientBoundaryReadoutOfRows_apply
    {lambda : CCM24SoninScale}
    (ambientRow boundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda)
    (x : suffixEulerFrameAmbientBoundaryCarrier) :
    suffixEulerFrameAmbientBoundaryReadoutOfRows ambientRow boundaryRow x =
      ambientRow x.fst + boundaryRow x.snd := by
  change ambientRow (WithLp.fst x) + boundaryRow (WithLp.snd x) = _
  rfl

/-- The packed component readout is bounded by the sum of its two component
operator norms. -/
theorem suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add
    {lambda : CCM24SoninScale}
    (ambientRow boundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryReadoutOfRows ambientRow boundaryRow‖ ≤
      ‖ambientRow‖ + ‖boundaryRow‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg ambientRow) (norm_nonneg boundaryRow))
  intro x
  calc
    ‖suffixEulerFrameAmbientBoundaryReadoutOfRows ambientRow boundaryRow x‖ =
        ‖ambientRow x.fst + boundaryRow x.snd‖ := by
          rw [suffixEulerFrameAmbientBoundaryReadoutOfRows_apply]
    _ ≤ ‖ambientRow x.fst‖ + ‖boundaryRow x.snd‖ := norm_add_le _ _
    _ ≤ ‖ambientRow‖ * ‖x.fst‖ + ‖boundaryRow‖ * ‖x.snd‖ := by
      exact add_le_add (ambientRow.le_opNorm _) (boundaryRow.le_opNorm _)
    _ ≤ ‖ambientRow‖ * ‖x‖ + ‖boundaryRow‖ * ‖x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (WithLp.norm_fst_le
            (α := finiteSCarrier) (β := finiteSCarrier) (p := 2) x)
          (norm_nonneg ambientRow))
        (mul_le_mul_of_nonneg_left
          (WithLp.norm_snd_le
            (α := finiteSCarrier) (β := finiteSCarrier) (p := 2) x)
          (norm_nonneg boundaryRow))
    _ = (‖ambientRow‖ + ‖boundaryRow‖) * ‖x‖ := by
      ring

/-- Composing the packed readout with the actual physical analysis column
is exactly the sum of the two component rows on the actual two physical
coordinates. -/
theorem suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_analysis
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (ambientRow boundaryRow :
      finiteSCarrier →L[ℂ] sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryReadoutOfRows ambientRow boundaryRow ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      ambientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
        boundaryRow ∘L ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    suffixEulerFrameAmbientBoundaryReadoutOfRows_apply,
    suffixEulerFrameAmbientBoundaryAnalysis_apply, WithLp.toLp_fst,
    WithLp.toLp_snd]

/-! ## Recovering component rows from a packed readout -/

/-- Embed the ambient coordinate into the packed physical carrier. -/
noncomputable def suffixEulerFrameAmbientBoundaryLeftEmbedding :
    finiteSCarrier →L[ℂ] suffixEulerFrameAmbientBoundaryCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      finiteSCarrier finiteSCarrier).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id ℂ finiteSCarrier).prod
      (0 : finiteSCarrier →L[ℂ] finiteSCarrier))

/-- Embed the moving-boundary coordinate into the packed physical carrier. -/
noncomputable def suffixEulerFrameAmbientBoundaryRightEmbedding :
    finiteSCarrier →L[ℂ] suffixEulerFrameAmbientBoundaryCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      finiteSCarrier finiteSCarrier).symm.toContinuousLinearMap ∘L
    ((0 : finiteSCarrier →L[ℂ] finiteSCarrier).prod
      (ContinuousLinearMap.id ℂ finiteSCarrier))

@[simp]
theorem suffixEulerFrameAmbientBoundaryLeftEmbedding_apply
    (x : finiteSCarrier) :
    suffixEulerFrameAmbientBoundaryLeftEmbedding x =
      WithLp.toLp 2 (x, 0) := by
  rfl

@[simp]
theorem suffixEulerFrameAmbientBoundaryRightEmbedding_apply
    (x : finiteSCarrier) :
    suffixEulerFrameAmbientBoundaryRightEmbedding x =
      WithLp.toLp 2 (0, x) := by
  rfl

/-- The two coordinate embeddings add back to the original packed vector. -/
theorem suffixEulerFrameAmbientBoundary_left_add_right
    (x : suffixEulerFrameAmbientBoundaryCarrier) :
    suffixEulerFrameAmbientBoundaryLeftEmbedding x.fst +
        suffixEulerFrameAmbientBoundaryRightEmbedding x.snd =
      x := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ
    finiteSCarrier finiteSCarrier).injective
  change (WithLp.fst x, (0 : finiteSCarrier)) +
      ((0 : finiteSCarrier), WithLp.snd x) =
    (WithLp.fst x, WithLp.snd x)
  ext <;> simp

/-- The ambient-coordinate embedding is contractive. -/
theorem suffixEulerFrameAmbientBoundaryLeftEmbedding_norm_le_one :
    ‖suffixEulerFrameAmbientBoundaryLeftEmbedding‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [suffixEulerFrameAmbientBoundaryLeftEmbedding_apply,
    WithLp.norm_toLp_fst]
  simp

/-- The boundary-coordinate embedding is contractive. -/
theorem suffixEulerFrameAmbientBoundaryRightEmbedding_norm_le_one :
    ‖suffixEulerFrameAmbientBoundaryRightEmbedding‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [suffixEulerFrameAmbientBoundaryRightEmbedding_apply,
    WithLp.norm_toLp_snd]
  simp

/-- Every packed readout is exactly the packing of its two coordinate
restrictions. -/
theorem suffixEulerFrameAmbientBoundaryReadoutOfRows_components_eq
    {lambda : CCM24SoninScale}
    (readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryReadoutOfRows
        (readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding)
        (readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding) =
      readout := by
  apply ContinuousLinearMap.ext
  intro x
  rw [suffixEulerFrameAmbientBoundaryReadoutOfRows_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_add]
  rw [suffixEulerFrameAmbientBoundary_left_add_right]

/-! ## The exact four-term raw physical row -/

/-- The four-term physical normal form for the raw adjacent intertwinement
adjoint.  This is a named target for component-row factorization. -/
noncomputable def suffixActualBandRawPhysicalFourTermRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  -((suffixActualBandForwardEndpointCoframe lambda S)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda ∘L
      (suffixEulerFrameTransition lambda p S)†) +
    (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      suffixActualBandForwardCoframe lambda S ∘L
      (suffixEulerFrameTransition lambda p S)† +
    (suffixEulerFrameTransition lambda p S)† ∘L
      (suffixActualBandForwardEndpointCoframe lambda (p :: S))† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda -
    (suffixEulerFrameTransition lambda p S)† ∘L
      (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
      suffixActualBandForwardCoframe lambda (p :: S)

/-- The named four-term row is definitionally the already proved raw adjoint
normal form. -/
theorem suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
  rw [suffixActualBandRawPhysicalFourTermRow]
  exact suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTerm
    owner lambda p S

/-! ## Component-row contract and conversion to Proof 531's raw readout -/

/-- A source-specific component-row factorization of the raw four-term row.
The two coordinates are the actual ambient antiresonant loss and the actual
moving-boundary adjoint. -/
structure SuffixRawAmbientBoundaryComponentReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  ambientRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  boundaryRow : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda
  ambient_norm_le : ‖ambientRow‖ ≤ ambientBound
  boundary_norm_le : ‖boundaryRow‖ ≤ boundaryBound
  factorization :
    ambientRow ∘L suffixEulerFrameAmbientLossColumn lambda p S +
        boundaryRow ∘L ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S

/-- The packed readout associated to component rows. -/
noncomputable def SuffixRawAmbientBoundaryComponentReadoutData.readout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      sourceSoninCarrier lambda :=
  suffixEulerFrameAmbientBoundaryReadoutOfRows
    data.ambientRow data.boundaryRow

theorem SuffixRawAmbientBoundaryComponentReadoutData.readout_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound) :
    ‖data.readout‖ ≤ ambientBound + boundaryBound := by
  calc
    ‖data.readout‖ ≤ ‖data.ambientRow‖ + ‖data.boundaryRow‖ :=
      suffixEulerFrameAmbientBoundaryReadoutOfRows_norm_le_add
        data.ambientRow data.boundaryRow
    _ ≤ ambientBound + boundaryBound :=
      add_le_add data.ambient_norm_le data.boundary_norm_le

/-- Component rows are sufficient to construct Proof 531's raw readout
contract, with the component norm bounds added once. -/
noncomputable def SuffixRawAmbientBoundaryComponentReadoutData.toRawReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound) :
    SuffixRawAmbientBoundaryReadoutData owner lambda p S
      (ambientBound + boundaryBound) :=
  { bound_nonneg := add_nonneg data.ambient_bound_nonneg
      data.boundary_bound_nonneg
    readout := data.readout
    readout_norm_le := data.readout_norm_le
    factorization := by
      rw [SuffixRawAmbientBoundaryComponentReadoutData.readout,
        suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_analysis]
      rw [data.factorization,
        ← suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow
          owner lambda p S] }

/-- Conversely, any Proof 531 raw readout can be unpacked into its two
coordinate component rows.  The numerical component bounds are the actual
component operator norms, so this theorem adds no analytic estimate. -/
noncomputable def SuffixRawAmbientBoundaryReadoutData.toComponentReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryReadoutData owner lambda p S bound) :
    SuffixRawAmbientBoundaryComponentReadoutData owner lambda p S
      ‖data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding‖
      ‖data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding‖ := by
  refine
    { ambient_bound_nonneg := norm_nonneg _
      boundary_bound_nonneg := norm_nonneg _
      ambientRow := data.readout ∘L
        suffixEulerFrameAmbientBoundaryLeftEmbedding
      boundaryRow := data.readout ∘L
        suffixEulerFrameAmbientBoundaryRightEmbedding
      ambient_norm_le := le_rfl
      boundary_norm_le := le_rfl
      factorization := ?_ }
  have hcomponents := congrArg
    (fun readout : suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
        sourceSoninCarrier lambda =>
      readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S)
    (suffixEulerFrameAmbientBoundaryReadoutOfRows_components_eq data.readout)
  change
    suffixEulerFrameAmbientBoundaryReadoutOfRows
        (data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding)
        (data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding) ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      data.readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S
    at hcomponents
  rw [suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_analysis] at hcomponents
  calc
    (data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding) ∘L
          suffixEulerFrameAmbientLossColumn lambda p S +
        (data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding) ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary =
        data.readout ∘L
          suffixEulerFrameAmbientBoundaryAnalysis lambda p S := hcomponents
    _ = (suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda p S)† := data.factorization
    _ = suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
      rw [suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow]

/-- A packed raw readout with bound `C` gives component rows with the same
bound `C` on each coordinate.  This uses only the contractive coordinate
embeddings, so it adds no new source-specific estimate. -/
noncomputable def SuffixRawAmbientBoundaryReadoutData.toComponentReadoutWithBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryReadoutData owner lambda p S bound) :
    SuffixRawAmbientBoundaryComponentReadoutData owner lambda p S
      bound bound := by
  let component := SuffixRawAmbientBoundaryReadoutData.toComponentReadout
    data
  refine
    { ambient_bound_nonneg := data.bound_nonneg
      boundary_bound_nonneg := data.bound_nonneg
      ambientRow := component.ambientRow
      boundaryRow := component.boundaryRow
      ambient_norm_le := ?_
      boundary_norm_le := ?_
      factorization := component.factorization }
  · calc
      ‖component.ambientRow‖ =
          ‖data.readout ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding‖ := rfl
      _ ≤ ‖data.readout‖ * ‖suffixEulerFrameAmbientBoundaryLeftEmbedding‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 := by
        exact mul_le_mul data.readout_norm_le
          suffixEulerFrameAmbientBoundaryLeftEmbedding_norm_le_one
          (norm_nonneg _) data.bound_nonneg
      _ = bound := by simp
  · calc
      ‖component.boundaryRow‖ =
          ‖data.readout ∘L suffixEulerFrameAmbientBoundaryRightEmbedding‖ := rfl
      _ ≤ ‖data.readout‖ * ‖suffixEulerFrameAmbientBoundaryRightEmbedding‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ bound * 1 := by
        exact mul_le_mul data.readout_norm_le
          suffixEulerFrameAmbientBoundaryRightEmbedding_norm_le_one
          (norm_nonneg _) data.bound_nonneg
      _ = bound := by simp

theorem SuffixRawAmbientBoundaryComponentReadoutData.readout_comp_analysis_eq_fourTerm
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound) :
    data.readout ∘L suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      suffixActualBandRawPhysicalFourTermRow owner lambda p S := by
  rw [SuffixRawAmbientBoundaryComponentReadoutData.readout,
    suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_analysis,
    data.factorization]

/-- The raw adjoint inherits the component-row readout estimate against the
single summed physical analysis column. -/
theorem SuffixRawAmbientBoundaryComponentReadoutData.rawAdjoint_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ≤
      (ambientBound + boundaryBound) *
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
  have hraw := data.toRawReadout.factorization
  rw [← hraw]
  calc
    ‖(data.toRawReadout.readout ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S) x‖ ≤
        ‖data.toRawReadout.readout‖ *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ :=
      data.toRawReadout.readout.le_opNorm _
    _ ≤ (ambientBound + boundaryBound) *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
      exact mul_le_mul_of_nonneg_right data.toRawReadout.readout_norm_le
        (norm_nonneg _)

/-! ## Uniform component-row package -/

/-- One pair of component bounds for every adjacent visible-prime/suffix
raw four-term row. -/
structure SuffixRawAmbientBoundaryUniformComponentReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (ambientBound boundaryBound : ℝ) where
  ambient_bound_nonneg : 0 ≤ ambientBound
  boundary_bound_nonneg : 0 ≤ boundaryBound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound

/-- A uniform component-row package gives Proof 531's uniform raw readout
package, with the two component constants added once. -/
noncomputable def
    SuffixRawAmbientBoundaryUniformComponentReadoutData.toRawUniformReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda
      (ambientBound + boundaryBound) :=
  { bound_nonneg := add_nonneg data.ambient_bound_nonneg
      data.boundary_bound_nonneg
    readout := fun p S => (data.readout p S).toRawReadout }

/-- Conversely, a uniform packed raw-readout package gives a uniform
component-row package with the same raw bound on each coordinate. -/
noncomputable def
    SuffixRawAmbientBoundaryUniformReadoutData.toUniformComponentReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound) :
    SuffixRawAmbientBoundaryUniformComponentReadoutData owner lambda
      bound bound :=
  { ambient_bound_nonneg := data.bound_nonneg
    boundary_bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      SuffixRawAmbientBoundaryReadoutData.toComponentReadoutWithBound
        (data.readout p S) }

/-- Uniform component rows exist if and only if the packed raw readout exists.
The component-to-raw direction adds the two component constants; the raw-to-
component direction reuses the raw constant for each coordinate. -/
theorem exists_uniformComponentReadout_iff_exists_uniformRawReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound)) ↔
      (∃ bound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformReadoutData owner lambda bound)) := by
  constructor
  · rintro ⟨ambientBound, boundaryBound, ⟨data⟩⟩
    exact ⟨ambientBound + boundaryBound, ⟨data.toRawUniformReadout⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨bound, bound,
      ⟨SuffixRawAmbientBoundaryUniformReadoutData.toUniformComponentReadout
        data⟩⟩

/-- Uniform component rows are equivalent to the existing family-uniform
physical Douglas domination contract.  This is only a composition of the
component/raw interface equivalence with Proof 531's raw/physical equivalence.
-/
theorem exists_uniformComponentReadout_iff_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound)) ↔
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) :=
  (exists_uniformComponentReadout_iff_exists_uniformRawReadout owner lambda).trans
    (exists_uniformRawReadout_iff_exists_uniformPhysicalDomination
      owner lambda)

/-- Therefore a family-uniform component-row producer is enough for the
existing family-uniform physical Douglas contract. -/
theorem exists_uniformComponentReadout_implies_exists_uniformPhysicalDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound)) →
      (∃ bound : ℝ,
        Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound)) := by
  rintro ⟨ambientBound, boundaryBound, ⟨data⟩⟩
  exact
    (exists_uniformComponentReadout_iff_exists_uniformPhysicalDomination
      owner lambda).mp
      ⟨ambientBound, boundaryBound, ⟨data⟩⟩

end CCM24FiniteSCompletedJuliaRawPhysicalFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
