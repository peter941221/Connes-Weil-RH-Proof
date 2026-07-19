/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic.NoncommRing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCausal

/-!
# Source-owned Julia and Schur frame algebra

This module records the four genuine corner operators of one Euler step.  The
transport is unitary on the ambient carrier, while the current source range is
represented by an orthogonal idempotent `P` and its complement `Q = 1 - P`.

The graph coordinate and the Schur frame are definitions, not independent
factorization witnesses:

```text
U00 = P U P              U01 = P U Q
U10 = Q U P              U11 = Q U Q
X   = a (Q - a U11)^(-1) U10
Phi = U00 + U01 X
Z   = (P - a Phi) C
```

The analytic square-root construction of the graph cosine `C`, and the
source-specific Douglas domination of a physical boundary column by the
resulting graph sine, remain separate obligations.  No Gate 3U, trace bound,
or RH premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaSchur

open CC20Concrete
open CCM24FiniteSCausalMarkov
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open SelectedCrossingOperatorBridge

variable {A : Type*} [Ring A] [StarRing A]

/-! The orthogonal complement is kept as a named algebraic operation. -/
def complement (projection : A) : A := 1 - projection

/-!
One actual unitary colligation on a projected carrier.  The unitary data is
the ambient transport itself; the four blocks below are derived from `P` and
`Q`, so a caller cannot replace them with unrelated bookkeeping maps.
-/
structure ProjectedUnitaryColligation (A : Type*)
    [Ring A] [StarRing A] where
  projection : A
  transport : A
  scalar : A
  resolvent : A
  projection_idempotent : projection * projection = projection
  projection_selfAdjoint : star projection = projection
  transport_isometry : star transport * transport = 1
  transport_coisometry : transport * star transport = 1
  scalar_central : ∀ b : A, scalar * b = b * scalar
  resolvent_left :
    (complement projection - scalar *
        (complement projection * transport * complement projection)) *
        resolvent = complement projection
  resolvent_right :
    resolvent *
        (complement projection - scalar *
          (complement projection * transport * complement projection)) =
      complement projection
  resolvent_left_support :
    complement projection * resolvent = resolvent
  resolvent_right_support :
    resolvent * complement projection = resolvent

namespace ProjectedUnitaryColligation

variable (data : ProjectedUnitaryColligation A)

/-! The four corners are derived from the actual ambient transport. -/
def U00 : A :=
  data.projection * data.transport * data.projection

def U01 : A :=
  data.projection * data.transport * complement data.projection

def U10 : A :=
  complement data.projection * data.transport * data.projection

def U11 : A :=
  complement data.projection * data.transport * complement data.projection

/-! The complete transport is the sum of these four corners. -/
theorem transport_eq_sum_corners :
    data.transport = data.U00 + data.U01 + data.U10 + data.U11 := by
  have hsplit : data.projection + complement data.projection = 1 := by
    unfold complement
    noncomm_ring
  calc
    data.transport =
        (data.projection + complement data.projection) * data.transport *
          (data.projection + complement data.projection) := by
      rw [hsplit]
      noncomm_ring
    _ = data.U00 + data.U01 + data.U10 + data.U11 := by
      unfold U00 U01 U10 U11
      noncomm_ring

theorem complement_idempotent :
    complement data.projection * complement data.projection =
      complement data.projection := by
  unfold complement
  calc
    (1 - data.projection) * (1 - data.projection) =
        1 - data.projection - data.projection +
          data.projection * data.projection := by noncomm_ring
    _ = 1 - data.projection := by
      rw [data.projection_idempotent]
      noncomm_ring

theorem complement_mul_U10 :
    complement data.projection * data.U10 = data.U10 := by
  unfold U10
  calc
    complement data.projection *
        (complement data.projection * data.transport * data.projection) =
        (complement data.projection * complement data.projection) *
          data.transport * data.projection := by noncomm_ring
    _ = data.U10 := by
      rw [data.complement_idempotent]
      rfl

theorem projection_mul_complement :
    data.projection * complement data.projection = 0 := by
  unfold complement
  calc
    data.projection * (1 - data.projection) =
        data.projection - data.projection * data.projection := by
      noncomm_ring
    _ = 0 := by
      rw [data.projection_idempotent]
      noncomm_ring

theorem complement_mul_projection :
    complement data.projection * data.projection = 0 := by
  unfold complement
  calc
    (1 - data.projection) * data.projection =
        data.projection - data.projection * data.projection := by
      noncomm_ring
    _ = 0 := by
      rw [data.projection_idempotent]
      noncomm_ring

theorem complement_selfAdjoint :
    star (complement data.projection) = complement data.projection := by
  simp [complement, data.projection_selfAdjoint]

theorem complement_mul_U11 :
    complement data.projection * data.U11 = data.U11 := by
  unfold U11
  calc
    complement data.projection *
        (complement data.projection * data.transport *
          complement data.projection) =
      (complement data.projection * complement data.projection) *
        data.transport * complement data.projection := by noncomm_ring
    _ = data.U11 := by
      rw [data.complement_idempotent]
      rfl

theorem U11_mul_complement :
    data.U11 * complement data.projection = data.U11 := by
  unfold U11
  calc
    complement data.projection * data.transport * complement data.projection *
        complement data.projection =
      complement data.projection * data.transport *
        (complement data.projection * complement data.projection) := by
          noncomm_ring
    _ = data.U11 := by
      rw [data.complement_idempotent]
      rfl

theorem U10_mul_projection :
    data.U10 * data.projection = data.U10 := by
  unfold U10
  calc
    complement data.projection * data.transport * data.projection *
        data.projection =
      complement data.projection * data.transport *
        (data.projection * data.projection) := by noncomm_ring
    _ = data.U10 := by
      rw [data.projection_idempotent]
      rfl

theorem projection_mul_U01 :
    data.projection * data.U01 = data.U01 := by
  unfold U01
  calc
    data.projection *
        (data.projection * data.transport * complement data.projection) =
      (data.projection * data.projection) * data.transport *
        complement data.projection := by noncomm_ring
    _ = data.U01 := by
      rw [data.projection_idempotent]
      rfl

theorem U01_mul_complement :
    data.U01 * complement data.projection = data.U01 := by
  unfold U01
  calc
    data.projection * data.transport * complement data.projection *
        complement data.projection =
      data.projection * data.transport *
        (complement data.projection * complement data.projection) := by
          noncomm_ring
    _ = data.U01 := by
      rw [data.complement_idempotent]
      rfl

theorem U10_mul_complement :
    data.U10 * complement data.projection = 0 := by
  unfold U10
  calc
    complement data.projection * data.transport * data.projection *
        complement data.projection =
      complement data.projection * data.transport *
        (data.projection * complement data.projection) := by
          noncomm_ring
    _ = 0 := by rw [data.projection_mul_complement]; simp

theorem projection_mul_U00 :
    data.projection * data.U00 = data.U00 := by
  unfold U00
  calc
    data.projection *
        (data.projection * data.transport * data.projection) =
      (data.projection * data.projection) * data.transport *
        data.projection := by noncomm_ring
    _ = data.U00 := by
      rw [data.projection_idempotent]
      rfl

theorem U00_mul_projection :
    data.U00 * data.projection = data.U00 := by
  unfold U00
  calc
    data.projection * data.transport * data.projection * data.projection =
      data.projection * data.transport *
        (data.projection * data.projection) := by noncomm_ring
    _ = data.U00 := by
      rw [data.projection_idempotent]
      rfl

/-! The graph coordinate and its Julia transfer. -/
def graphCoordinate : A :=
  data.scalar * data.resolvent * data.U10

def graphTransfer : A :=
  data.U00 + data.U01 * data.graphCoordinate

theorem graphCoordinate_mul_projection :
    data.graphCoordinate * data.projection = data.graphCoordinate := by
  unfold graphCoordinate
  calc
    (data.scalar * data.resolvent * data.U10) * data.projection =
        data.scalar * data.resolvent *
          (data.U10 * data.projection) := by noncomm_ring
    _ = data.graphCoordinate := by
      rw [data.U10_mul_projection]
      rfl

theorem graphCoordinate_mul_complement :
    data.graphCoordinate * complement data.projection = 0 := by
  unfold graphCoordinate
  calc
    data.scalar * data.resolvent * data.U10 *
        complement data.projection =
      data.scalar * data.resolvent *
        (data.U10 * complement data.projection) := by noncomm_ring
    _ = 0 := by rw [data.U10_mul_complement]; simp

theorem projection_mul_graphTransfer :
    data.projection * data.graphTransfer = data.graphTransfer := by
  unfold graphTransfer
  calc
    data.projection * (data.U00 + data.U01 * data.graphCoordinate) =
        data.projection * data.U00 +
          data.projection * (data.U01 * data.graphCoordinate) := by
      noncomm_ring
    _ = data.U00 + data.U01 * data.graphCoordinate := by
      calc
        data.projection * data.U00 +
              data.projection * (data.U01 * data.graphCoordinate) =
            data.projection * data.U00 +
              (data.projection * data.U01) * data.graphCoordinate := by
                noncomm_ring
        _ = data.U00 + data.U01 * data.graphCoordinate := by
          rw [data.projection_mul_U00, data.projection_mul_U01]

theorem graphTransfer_mul_projection :
    data.graphTransfer * data.projection = data.graphTransfer := by
  unfold graphTransfer
  have hcoord := data.graphCoordinate_mul_projection
  calc
    (data.U00 + data.U01 * data.graphCoordinate) * data.projection =
        data.U00 * data.projection + data.U01 *
          (data.graphCoordinate * data.projection) := by noncomm_ring
    _ = data.U00 + data.U01 * data.graphCoordinate := by
      rw [hcoord, data.U00_mul_projection]
    _ = data.graphTransfer := rfl

def graphSine (cosine : A) : A :=
  data.graphCoordinate * cosine

def schurFrame (cosine : A) : A :=
  (data.projection - data.scalar * data.graphTransfer) * cosine

/-!
The canonical graph cosine is defined on the actual ambient operator algebra.
Its use below is deliberately separate from the algebraic Riccati identity:
the latter is valid in a ring, while this square-root construction needs the
Hilbert-space continuous functional calculus.
-/
noncomputable def graphCosine
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) : K →L[ℂ] K :=
  CFC.rpow
    (ContinuousLinearMap.id ℂ K +
      ContinuousLinearMap.adjoint data.graphCoordinate ∘L
        data.graphCoordinate)
    (-1 / 2 : ℝ)

noncomputable def graphSineCanonical
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) : K →L[ℂ] K :=
  data.graphCoordinate ∘L data.graphCosine

theorem graphSine_eq_graphSineCanonical
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) :
    data.graphSine data.graphCosine = data.graphSineCanonical := by
  unfold graphSineCanonical graphSine
  rw [ContinuousLinearMap.mul_def]

/-!
The Riccati equation is the exact range equation for
`(1 - scalar * transport)^(-1) Ran(P)`.  The proof uses the resolvent before
any norm or condition-number estimate.
-/
theorem graphCoordinate_equation :
    data.graphCoordinate - data.scalar *
        (data.U10 +
          (complement data.projection * data.transport *
            complement data.projection) * data.graphCoordinate) = 0 := by
  unfold graphCoordinate
  have hres := data.resolvent_left
  have hcorner := data.complement_mul_U10
  have hres_support := data.resolvent_left_support
  have hcentral :
      (complement data.projection * data.transport *
        complement data.projection) * data.scalar =
      data.scalar * (complement data.projection * data.transport *
        complement data.projection) :=
    (data.scalar_central
      (complement data.projection * data.transport *
        complement data.projection)).symm
  calc
    data.scalar * data.resolvent * data.U10 - data.scalar *
        (data.U10 +
            (complement data.projection * data.transport *
              complement data.projection) *
            (data.scalar * data.resolvent * data.U10)) =
        data.scalar * data.resolvent * data.U10 -
          data.scalar * data.U10 -
          data.scalar *
            ((complement data.projection * data.transport *
              complement data.projection) * data.scalar) *
            data.resolvent * data.U10 := by noncomm_ring
    _ = data.scalar * data.resolvent * data.U10 -
          data.scalar * data.U10 -
          data.scalar *
            (data.scalar * (complement data.projection * data.transport *
              complement data.projection)) *
            data.resolvent * data.U10 := by
      rw [hcentral]
    _ = data.scalar *
          ((complement data.projection * data.resolvent) * data.U10) -
          data.scalar * (complement data.projection * data.U10) -
          data.scalar *
            (data.scalar * (complement data.projection * data.transport *
              complement data.projection)) *
            data.resolvent * data.U10 := by
      rw [hres_support, hcorner]
      noncomm_ring
    _ = data.scalar *
          ((complement data.projection - data.scalar *
            (complement data.projection * data.transport *
              complement data.projection)) * data.resolvent -
            complement data.projection) * data.U10 := by noncomm_ring
    _ = 0 := by rw [hres]; noncomm_ring

theorem graphCoordinate_fixedPoint :
    data.graphCoordinate = data.scalar *
        (data.U10 +
          (complement data.projection * data.transport *
            complement data.projection) * data.graphCoordinate) := by
  exact sub_eq_zero.mp data.graphCoordinate_equation

/-!
The lower graph row vanishes after the Euler factor is applied. -/
theorem graphSine_lower_equation (cosine : A) :
    data.graphSine cosine - data.scalar *
        (data.U10 * cosine +
          (complement data.projection * data.transport *
            complement data.projection) * data.graphSine cosine) = 0 := by
  unfold graphSine
  calc
    data.graphCoordinate * cosine - data.scalar *
          (data.U10 * cosine +
            (complement data.projection * data.transport *
              complement data.projection) *
              (data.graphCoordinate * cosine)) =
        (data.graphCoordinate - data.scalar *
          (data.U10 +
            (complement data.projection * data.transport *
              complement data.projection) * data.graphCoordinate)) *
          cosine := by noncomm_ring
    _ = 0 := by rw [data.graphCoordinate_equation]; simp

/-! The upper graph row is exactly the Schur frame `Z`. -/
theorem schurFrame_upper_equation (cosine : A)
    (hcosine : data.projection * cosine = cosine) :
    cosine - data.scalar *
        (data.U00 * cosine + data.U01 * data.graphSine cosine) =
  data.schurFrame cosine := by
  unfold schurFrame graphTransfer graphSine
  rw [sub_mul, hcosine]
  noncomm_ring

/-! The Schur frame is genuinely supported on the projected old carrier. -/

theorem projection_mul_schurFrame (cosine : A) :
    data.projection * data.schurFrame cosine = data.schurFrame cosine := by
  unfold schurFrame
  calc
    data.projection *
          ((data.projection - data.scalar * data.graphTransfer) * cosine) =
        (data.projection *
          (data.projection - data.scalar * data.graphTransfer)) * cosine := by
      noncomm_ring
    _ = (data.projection - data.scalar * data.graphTransfer) * cosine := by
      have hmul :
          data.projection * (data.scalar * data.graphTransfer) =
            data.scalar * (data.projection * data.graphTransfer) := by
        calc
          data.projection * (data.scalar * data.graphTransfer) =
              (data.projection * data.scalar) * data.graphTransfer := by
                noncomm_ring
          _ = (data.scalar * data.projection) * data.graphTransfer := by
            rw [(data.scalar_central data.projection).symm]
          _ = data.scalar * (data.projection * data.graphTransfer) := by
            noncomm_ring
      rw [mul_sub, hmul, data.projection_idempotent,
        data.projection_mul_graphTransfer]

/-!
The two equations combine into the physical source-frame readback.  The pair
`(cosine, graphSine cosine)` is sent by `I - scalar * U` to `(Z, 0)`.
-/
def eulerGraphAction (cosine sine : A) : A × A :=
  (cosine - data.scalar * (data.U00 * cosine + data.U01 * sine),
    sine - data.scalar *
      (data.U10 * cosine +
        (complement data.projection * data.transport *
          complement data.projection) * sine))

theorem eulerGraphAction_on_graphFrame (cosine : A) :
    data.projection * cosine = cosine →
    data.eulerGraphAction cosine (data.graphSine cosine) =
      (data.schurFrame cosine, 0) := by
  intro hcosine
  unfold eulerGraphAction
  rw [data.schurFrame_upper_equation cosine hcosine,
    data.graphSine_lower_equation]

theorem eulerGraphAction_on_canonicalGraphFrame
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : ProjectedUnitaryColligation (K →L[ℂ] K))
    (hcosine : data.projection * data.graphCosine = data.graphCosine) :
    data.eulerGraphAction data.graphCosine data.graphSineCanonical =
      (data.schurFrame data.graphCosine, 0) := by
  rw [← data.graphSine_eq_graphSineCanonical]
  exact data.eulerGraphAction_on_graphFrame data.graphCosine hcosine

/-!
The source-owned frame is not the Julia transfer alone.  Its one-step Schur
factor is the product `(P - a Phi) C`, exactly as in Proof 390.
-/
theorem schurFrame_eq_sourceFactor (cosine : A) :
    data.schurFrame cosine =
      (data.projection - data.scalar *
        (data.U00 + data.U01 * data.graphCoordinate)) * cosine := by
  rfl

end ProjectedUnitaryColligation

/-!
The analytic step package below is the strong replacement for a free-standing
`JuliaDefectStep`.  Its transfer and graph sine are read from one actual
projected unitary colligation.  The remaining inequality is the genuine
source estimate that turns the graph sine into a detector output; it is kept
as a theorem-shaped field rather than silently inferred from a norm bound.
-/
structure SchurJuliaRangeStepData
    (K G : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  colligation : ProjectedUnitaryColligation (K →L[ℂ] K)
  cosine : K →L[ℂ] K
  rangeSine : K →L[ℂ] G
  readout : K →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  transfer_contract :
    ContinuousLinearMap.adjoint colligation.graphTransfer ∘L
      colligation.graphTransfer ≤
      ContinuousLinearMap.id ℂ K
  rangeSine_weighted_le : ∀ x : K,
    weight * ‖rangeSine x‖ ^ 2 ≤
      ‖canonicalJuliaDefect colligation.graphTransfer
        transfer_contract x‖ ^ 2
  rangeSine_readback :
    rangeSine = readout ∘L colligation.graphSine cosine

noncomputable def SchurJuliaRangeStepData.toJuliaDefectStep
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurJuliaRangeStepData K G) :
    JuliaDefectStep K G :=
  { transfer := data.colligation.graphTransfer
    defect := canonicalJuliaDefect data.colligation.graphTransfer
      data.transfer_contract
    rangeSine := data.rangeSine
    weight := data.weight
    weight_nonneg := data.weight_nonneg
    pythagorean := canonicalJuliaDefect_pythagorean
      data.colligation.graphTransfer data.transfer_contract
    rangeSine_weighted_le_defect := data.rangeSine_weighted_le }

@[simp]
theorem SchurJuliaRangeStepData.toJuliaDefectStep_transfer
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurJuliaRangeStepData K G) :
    data.toJuliaDefectStep.transfer = data.colligation.graphTransfer :=
  rfl

theorem SchurJuliaRangeStepData.rangeSine_eq_readout_comp_graphSine
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurJuliaRangeStepData K G) :
    data.rangeSine = data.readout ∘L
        data.colligation.graphSine data.cosine :=
  data.rangeSine_readback

/-!
This is the physically correct replacement for the preceding Julia-only
package.  Its transfer is the normalized Schur frame, not `graphTransfer`.
The normalization is kept as an explicit operator because it is a source
choice (for the Euler step it is the scalar factor `(1 + a)⁻¹`).
-/
structure SchurFrameJuliaRangeStepData
    (K G : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  colligation : ProjectedUnitaryColligation (K →L[ℂ] K)
  cosine : K →L[ℂ] K
  cosine_eq_graphCosine : cosine = colligation.graphCosine
  frameNormalizer : K →L[ℂ] K
  normalizedFrame : K →L[ℂ] K
  normalizedFrame_eq :
    normalizedFrame = frameNormalizer ∘L colligation.schurFrame cosine
  transfer_contract :
    ContinuousLinearMap.adjoint normalizedFrame ∘L normalizedFrame ≤
      ContinuousLinearMap.id ℂ K
  rangeSine : K →L[ℂ] G
  readout : K →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  rangeSine_weighted_le : ∀ x : K,
    weight * ‖rangeSine x‖ ^ 2 ≤
      ‖canonicalJuliaDefect normalizedFrame transfer_contract x‖ ^ 2
  rangeSine_readback :
    rangeSine = readout ∘L colligation.graphSine cosine

noncomputable def SchurFrameJuliaRangeStepData.toJuliaDefectStep
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurFrameJuliaRangeStepData K G) :
    JuliaDefectStep K G :=
  { transfer := data.normalizedFrame
    defect := canonicalJuliaDefect data.normalizedFrame
      data.transfer_contract
    rangeSine := data.rangeSine
    weight := data.weight
    weight_nonneg := data.weight_nonneg
    pythagorean := canonicalJuliaDefect_pythagorean data.normalizedFrame
      data.transfer_contract
    rangeSine_weighted_le_defect := data.rangeSine_weighted_le }

@[simp]
theorem SchurFrameJuliaRangeStepData.toJuliaDefectStep_transfer
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurFrameJuliaRangeStepData K G) :
    data.toJuliaDefectStep.transfer = data.normalizedFrame :=
  rfl

theorem SchurFrameJuliaRangeStepData.normalizedFrame_eq_sourceSchurFrame
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurFrameJuliaRangeStepData K G) :
    data.normalizedFrame = data.frameNormalizer ∘L
      data.colligation.schurFrame data.cosine :=
  data.normalizedFrame_eq

theorem SchurFrameJuliaRangeStepData.rangeSine_eq_readout_comp_graphSine
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : SchurFrameJuliaRangeStepData K G) :
    data.rangeSine = data.readout ∘L
      data.colligation.graphSine data.cosine :=
  data.rangeSine_readback

noncomputable def schurFrameJuliaSteps
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (SchurFrameJuliaRangeStepData K G)) :
    List (JuliaDefectStep K G) :=
  steps.map SchurFrameJuliaRangeStepData.toJuliaDefectStep

@[simp]
theorem schurFrameJuliaSteps_nil
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    schurFrameJuliaSteps ([] : List (SchurFrameJuliaRangeStepData K G)) = [] :=
  rfl

@[simp]
theorem schurFrameJuliaSteps_cons
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : SchurFrameJuliaRangeStepData K G)
    (steps : List (SchurFrameJuliaRangeStepData K G)) :
    schurFrameJuliaSteps (step :: steps) =
      step.toJuliaDefectStep :: schurFrameJuliaSteps steps :=
  rfl

noncomputable def schurJuliaSteps
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (SchurJuliaRangeStepData K G)) :
    List (JuliaDefectStep K G) :=
  steps.map SchurJuliaRangeStepData.toJuliaDefectStep

@[simp]
theorem schurJuliaSteps_nil
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    schurJuliaSteps ([] : List (SchurJuliaRangeStepData K G)) = [] :=
  rfl

@[simp]
theorem schurJuliaSteps_cons
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : SchurJuliaRangeStepData K G)
    (steps : List (SchurJuliaRangeStepData K G)) :
    schurJuliaSteps (step :: steps) =
      step.toJuliaDefectStep :: schurJuliaSteps steps :=
  rfl

/-!
Concrete source input for one visible prime.  The transport and scalar are
fixed to the actual CCM24 global-log Euler factor; only the current projection
and its complementary resolvent are supplied by the source geometry.
-/
structure PrimeEulerProjectedJuliaInput where
  prime : CCM24VisiblePrime
  projection :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2
  projection_idempotent : projection ∘L projection = projection
  projection_selfAdjoint : ContinuousLinearMap.adjoint projection = projection
  resolvent :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2
  resolvent_left :
    ((ContinuousLinearMap.id ℂ _ - projection -
        (ccm24PrimeEulerCoefficient prime : ℂ) •
          ((ContinuousLinearMap.id ℂ _ - projection) ∘L
            (CC20Concrete.cc20GlobalLogTranslation
              (-Real.log prime)).toContinuousLinearMap ∘L
            (ContinuousLinearMap.id ℂ _ - projection))) ∘L resolvent) =
      ContinuousLinearMap.id ℂ _ - projection
  resolvent_right :
    resolvent ∘L
        (ContinuousLinearMap.id ℂ _ - projection -
          (ccm24PrimeEulerCoefficient prime : ℂ) •
            ((ContinuousLinearMap.id ℂ _ - projection) ∘L
              (CC20Concrete.cc20GlobalLogTranslation
                (-Real.log prime)).toContinuousLinearMap ∘L
              (ContinuousLinearMap.id ℂ _ - projection))) =
      ContinuousLinearMap.id ℂ _ - projection
  resolvent_left_support :
    (ContinuousLinearMap.id ℂ _ - projection) ∘L resolvent = resolvent
  resolvent_right_support :
    resolvent ∘L (ContinuousLinearMap.id ℂ _ - projection) = resolvent

/-!
The projected resolvent is not an independent analytic witness.  Once the
current carrier is an orthogonal projection, the complementary Euler corner
is a strict contraction and its corner Neumann series supplies the unique
resolvent used by the Julia colligation.
-/
noncomputable def primeEulerProjectedComplementContraction
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2) :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2 :=
  (ccm24PrimeEulerCoefficient p : ℂ) •
    ((ContinuousLinearMap.id ℂ _ - projection) ∘L
      (CC20Concrete.cc20GlobalLogTranslation
        (-Real.log p)).toContinuousLinearMap ∘L
      (ContinuousLinearMap.id ℂ _ - projection))

noncomputable def primeEulerProjectedComplementResolvent
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2) :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2 :=
  (ContinuousLinearMap.id ℂ _ - projection) *
      (∑' n : ℕ,
        primeEulerProjectedComplementContraction p projection ^ n) *
    (ContinuousLinearMap.id ℂ _ - projection)

theorem norm_primeEulerProjectedComplementContraction_lt_one
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    ‖primeEulerProjectedComplementContraction p projection‖ < 1 := by
  let q := ContinuousLinearMap.id ℂ _ - projection
  let U := (CC20Concrete.cc20GlobalLogTranslation
    (-Real.log p)).toContinuousLinearMap
  have hcomplement :
      IsStarProjection q := by
    simpa [q] using hprojection.one_sub
  have hcomplement_norm :
      ‖q‖ ≤ 1 := IsStarProjection.norm_le _ hcomplement
  have htranslation_norm :
      ‖U‖ ≤ 1 := by
    simpa [U] using
      (CC20Concrete.cc20GlobalLogTranslation
        (-Real.log p)).norm_toContinuousLinearMap_le
  have hcorner_norm :
      ‖q ∘L U ∘L q‖ ≤ 1 := by
    calc
      ‖q ∘L U ∘L q‖ ≤ ‖q ∘L U‖ * ‖q‖ :=
        ContinuousLinearMap.opNorm_comp_le (q ∘L U) q
      _ ≤
          (‖q‖ * ‖U‖) * ‖q‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le q U)
          (norm_nonneg _)
      _ ≤ (1 * 1) * 1 := by
        calc
          (‖q‖ * ‖U‖) * ‖q‖ ≤
              (1 * ‖U‖) * ‖q‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcomplement_norm
                (norm_nonneg _))
              (norm_nonneg _)
          _ ≤ (1 * 1) * 1 := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left htranslation_norm (by norm_num))
              hcomplement_norm (by positivity) (by norm_num)
      _ = 1 := by norm_num
  change ‖(ccm24PrimeEulerCoefficient p : ℂ) • (q ∘L U ∘L q)‖ < 1
  rw [norm_smul]
  calc
    ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ *
          ‖q ∘L U ∘L q‖ ≤
        ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hcorner_norm
        (norm_nonneg _)
    _ = ccm24PrimeEulerCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
    _ < 1 := ccm24PrimeEulerCoefficient_lt_one p

theorem primeEulerProjectedComplementContraction_left_support
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    (ContinuousLinearMap.id ℂ _ - projection) *
        primeEulerProjectedComplementContraction p projection =
      primeEulerProjectedComplementContraction p projection := by
  have hq :
      (ContinuousLinearMap.id ℂ _ - projection) *
          (ContinuousLinearMap.id ℂ _ - projection) =
        ContinuousLinearMap.id ℂ _ - projection := by
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  have hmul :
      (ContinuousLinearMap.id ℂ _ - projection) *
          ((ccm24PrimeEulerCoefficient p : ℂ) •
            ((ContinuousLinearMap.id ℂ _ - projection) *
              (CC20Concrete.cc20GlobalLogTranslation
                (-Real.log p)).toContinuousLinearMap *
              (ContinuousLinearMap.id ℂ _ - projection))) =
        (ccm24PrimeEulerCoefficient p : ℂ) •
          ((ContinuousLinearMap.id ℂ _ - projection) *
            (CC20Concrete.cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap *
            (ContinuousLinearMap.id ℂ _ - projection)) := by
    rw [mul_smul_comm]
    exact congrArg (fun z => (ccm24PrimeEulerCoefficient p : ℂ) • z)
      (by
        calc
          (ContinuousLinearMap.id ℂ _ - projection) *
                ((ContinuousLinearMap.id ℂ _ - projection) *
                  (CC20Concrete.cc20GlobalLogTranslation
                    (-Real.log p)).toContinuousLinearMap *
                  (ContinuousLinearMap.id ℂ _ - projection)) =
              ((ContinuousLinearMap.id ℂ _ - projection) *
                (ContinuousLinearMap.id ℂ _ - projection)) *
                (CC20Concrete.cc20GlobalLogTranslation
                  (-Real.log p)).toContinuousLinearMap *
                (ContinuousLinearMap.id ℂ _ - projection) := by
            noncomm_ring
          _ = (ContinuousLinearMap.id ℂ _ - projection) *
                (CC20Concrete.cc20GlobalLogTranslation
                  (-Real.log p)).toContinuousLinearMap *
                (ContinuousLinearMap.id ℂ _ - projection) := by
            rw [hq])
  simpa only [primeEulerProjectedComplementContraction,
    ContinuousLinearMap.mul_def] using hmul

theorem primeEulerProjectedComplementContraction_right_support
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    primeEulerProjectedComplementContraction p projection *
        (ContinuousLinearMap.id ℂ _ - projection) =
      primeEulerProjectedComplementContraction p projection := by
  have hq :
      (ContinuousLinearMap.id ℂ _ - projection) *
          (ContinuousLinearMap.id ℂ _ - projection) =
        ContinuousLinearMap.id ℂ _ - projection := by
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  have hmul :
      ((ccm24PrimeEulerCoefficient p : ℂ) •
        ((ContinuousLinearMap.id ℂ _ - projection) *
          (CC20Concrete.cc20GlobalLogTranslation
            (-Real.log p)).toContinuousLinearMap *
          (ContinuousLinearMap.id ℂ _ - projection))) *
          (ContinuousLinearMap.id ℂ _ - projection) =
        (ccm24PrimeEulerCoefficient p : ℂ) •
          ((ContinuousLinearMap.id ℂ _ - projection) *
            (CC20Concrete.cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap *
            (ContinuousLinearMap.id ℂ _ - projection)) := by
    rw [smul_mul_assoc]
    exact congrArg (fun z => (ccm24PrimeEulerCoefficient p : ℂ) • z)
      (by
        calc
          ((ContinuousLinearMap.id ℂ _ - projection) *
              (CC20Concrete.cc20GlobalLogTranslation
                (-Real.log p)).toContinuousLinearMap *
              (ContinuousLinearMap.id ℂ _ - projection)) *
              (ContinuousLinearMap.id ℂ _ - projection) =
            (ContinuousLinearMap.id ℂ _ - projection) *
              (CC20Concrete.cc20GlobalLogTranslation
                (-Real.log p)).toContinuousLinearMap *
              ((ContinuousLinearMap.id ℂ _ - projection) *
                (ContinuousLinearMap.id ℂ _ - projection)) := by
              noncomm_ring
          _ = (ContinuousLinearMap.id ℂ _ - projection) *
              (CC20Concrete.cc20GlobalLogTranslation
                (-Real.log p)).toContinuousLinearMap *
              (ContinuousLinearMap.id ℂ _ - projection) := by
            rw [hq])
  simpa only [primeEulerProjectedComplementContraction,
    ContinuousLinearMap.mul_def] using hmul

theorem primeEulerProjectedComplementResolvent_left
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    (ContinuousLinearMap.id ℂ _ - projection -
        primeEulerProjectedComplementContraction p projection) *
        primeEulerProjectedComplementResolvent p projection =
      ContinuousLinearMap.id ℂ _ - projection := by
  let q := ContinuousLinearMap.id ℂ _ - projection
  let x := primeEulerProjectedComplementContraction p projection
  let series := ∑' n : ℕ, x ^ n
  have hq : q * q = q := by
    dsimp [q]
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  have hqx : q * x = x := by
    simpa only [q, x] using
      primeEulerProjectedComplementContraction_left_support p projection
        hprojection
  have hxq : x * q = x := by
    simpa only [q, x] using
      primeEulerProjectedComplementContraction_right_support p projection
        hprojection
  have hseries : (1 - x) * series = 1 := by
    exact mul_neg_geom_series x
      (norm_primeEulerProjectedComplementContraction_lt_one p projection
        hprojection)
  have hqminus : q - x = q * (1 - x) := by
    rw [mul_sub, mul_one, hqx]
  have hqminus_q : (q - x) * q = q - x := by
    rw [sub_mul, hq, hxq]
  have hmain : (q - x) * (q * series * q) = q := by
    calc
      (q - x) * (q * series * q) = ((q - x) * q) * series * q := by
        noncomm_ring
      _ = (q - x) * series * q := by rw [hqminus_q]
      _ = q * (1 - x) * series * q := by rw [hqminus]
      _ = q * ((1 - x) * series) * q := by noncomm_ring
      _ = q := by simpa only [hseries, mul_one]
  simpa only [q, x, series, primeEulerProjectedComplementResolvent,
    ContinuousLinearMap.mul_def] using hmain

theorem primeEulerProjectedComplementResolvent_right
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    primeEulerProjectedComplementResolvent p projection *
        (ContinuousLinearMap.id ℂ _ - projection -
          primeEulerProjectedComplementContraction p projection) =
      ContinuousLinearMap.id ℂ _ - projection := by
  let q := ContinuousLinearMap.id ℂ _ - projection
  let x := primeEulerProjectedComplementContraction p projection
  let series := ∑' n : ℕ, x ^ n
  have hq : q * q = q := by
    dsimp [q]
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  have hqx : q * x = x := by
    simpa only [q, x] using
      primeEulerProjectedComplementContraction_left_support p projection
        hprojection
  have hxq : x * q = x := by
    simpa only [q, x] using
      primeEulerProjectedComplementContraction_right_support p projection
        hprojection
  have hseries : series * (1 - x) = 1 := by
    exact geom_series_mul_neg x
      (norm_primeEulerProjectedComplementContraction_lt_one p projection
        hprojection)
  have hqminus : q - x = (1 - x) * q := by
    rw [sub_mul, one_mul, hxq]
  have hqminus_left : q * (q - x) = q - x := by
    rw [mul_sub, hq, hqx]
  have hmain : (q * series * q) * (q - x) = q := by
    calc
      (q * series * q) * (q - x) = q * series * (q * (q - x)) := by
        noncomm_ring
      _ = q * series * (q - x) := by rw [hqminus_left]
      _ = q * series * ((1 - x) * q) := by rw [hqminus]
      _ = q * (series * (1 - x)) * q := by noncomm_ring
      _ = q := by simpa only [hseries, mul_one]
  simpa only [q, x, series, primeEulerProjectedComplementResolvent,
    ContinuousLinearMap.mul_def] using hmain

theorem primeEulerProjectedComplementResolvent_left_support
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    (ContinuousLinearMap.id ℂ _ - projection) *
        primeEulerProjectedComplementResolvent p projection =
      primeEulerProjectedComplementResolvent p projection := by
  let q := ContinuousLinearMap.id ℂ _ - projection
  let series := ∑' n : ℕ,
    primeEulerProjectedComplementContraction p projection ^ n
  have hq : q * q = q := by
    dsimp [q]
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  change q * (q * series * q) = q * series * q
  calc
    q * (q * series * q) = (q * q) * series * q := by noncomm_ring
    _ = q * series * q := by rw [hq]

theorem primeEulerProjectedComplementResolvent_right_support
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    primeEulerProjectedComplementResolvent p projection *
        (ContinuousLinearMap.id ℂ _ - projection) =
      primeEulerProjectedComplementResolvent p projection := by
  let q := ContinuousLinearMap.id ℂ _ - projection
  let series := ∑' n : ℕ,
    primeEulerProjectedComplementContraction p projection ^ n
  have hq : q * q = q := by
    dsimp [q]
    simpa only [ContinuousLinearMap.mul_def] using
      hprojection.one_sub.isIdempotentElem
  change (q * series * q) * q = q * series * q
  calc
    (q * series * q) * q = q * series * (q * q) := by noncomm_ring
    _ = q * series * q := by rw [hq]

/-! The source may now supply only the actual projection. -/
noncomputable def PrimeEulerProjectedJuliaInput.ofStarProjection
    (p : CCM24VisiblePrime)
    (projection :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2)
    (hprojection : IsStarProjection projection) :
    PrimeEulerProjectedJuliaInput := by
  refine
    { prime := p
      projection := projection
      projection_idempotent := by
        simpa only [ContinuousLinearMap.mul_def] using
          hprojection.isIdempotentElem
      projection_selfAdjoint := by
        simpa only [ContinuousLinearMap.star_eq_adjoint] using
          hprojection.isSelfAdjoint
      resolvent := primeEulerProjectedComplementResolvent p projection
      resolvent_left := by
        simpa only [primeEulerProjectedComplementContraction,
          ContinuousLinearMap.mul_def] using
          primeEulerProjectedComplementResolvent_left p projection hprojection
      resolvent_right := by
        simpa only [primeEulerProjectedComplementContraction,
          ContinuousLinearMap.mul_def] using
          primeEulerProjectedComplementResolvent_right p projection hprojection
      resolvent_left_support := by
        simpa only [ContinuousLinearMap.mul_def] using
          primeEulerProjectedComplementResolvent_left_support p projection
            hprojection
      resolvent_right_support := by
        simpa only [ContinuousLinearMap.mul_def] using
          primeEulerProjectedComplementResolvent_right_support p projection
            hprojection }

/-!
The old structure remains backward-compatible for callers that already carry
a resolvent, but the field is now extensionally forced by the projection.  In
particular, it cannot be used to smuggle an unrelated complement inverse into
the Schur graph coordinate.
-/
theorem PrimeEulerProjectedJuliaInput.resolvent_eq_generated
    (data : PrimeEulerProjectedJuliaInput) :
    data.resolvent =
      primeEulerProjectedComplementResolvent data.prime data.projection := by
  have hprojection : IsStarProjection data.projection := by
    refine
      { isIdempotentElem := by
          simpa only [ContinuousLinearMap.mul_def] using
            data.projection_idempotent
        isSelfAdjoint := by
          simpa only [ContinuousLinearMap.star_eq_adjoint] using
            data.projection_selfAdjoint }
  have hdata_right :
      data.resolvent *
          (ContinuousLinearMap.id ℂ _ - data.projection -
            primeEulerProjectedComplementContraction data.prime
              data.projection) =
        ContinuousLinearMap.id ℂ _ - data.projection := by
    simpa only [primeEulerProjectedComplementContraction,
      ContinuousLinearMap.mul_def] using data.resolvent_right
  have hgenerated_left :
      (ContinuousLinearMap.id ℂ _ - data.projection -
          primeEulerProjectedComplementContraction data.prime
            data.projection) *
        primeEulerProjectedComplementResolvent data.prime data.projection =
      ContinuousLinearMap.id ℂ _ - data.projection :=
    primeEulerProjectedComplementResolvent_left data.prime data.projection
      hprojection
  have hgenerated_support :
      (ContinuousLinearMap.id ℂ _ - data.projection) *
          primeEulerProjectedComplementResolvent data.prime data.projection =
        primeEulerProjectedComplementResolvent data.prime data.projection :=
    primeEulerProjectedComplementResolvent_left_support data.prime
      data.projection hprojection
  calc
    data.resolvent = data.resolvent *
        (ContinuousLinearMap.id ℂ _ - data.projection) := by
      simpa only [ContinuousLinearMap.mul_def] using
        data.resolvent_right_support.symm
    _ = data.resolvent *
        ((ContinuousLinearMap.id ℂ _ - data.projection -
          primeEulerProjectedComplementContraction data.prime
            data.projection) *
          primeEulerProjectedComplementResolvent data.prime
            data.projection) := by
      rw [hgenerated_left]
    _ = (data.resolvent *
        (ContinuousLinearMap.id ℂ _ - data.projection -
          primeEulerProjectedComplementContraction data.prime
            data.projection)) *
          primeEulerProjectedComplementResolvent data.prime data.projection := by
      noncomm_ring
    _ = (ContinuousLinearMap.id ℂ _ - data.projection) *
          primeEulerProjectedComplementResolvent data.prime data.projection := by
      rw [hdata_right]
    _ = primeEulerProjectedComplementResolvent data.prime data.projection :=
      hgenerated_support

theorem complexScalarEnd_central
    (a : ℂ)
    (b : CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2) :
    (a • ContinuousLinearMap.id ℂ _) * b =
      b * (a • ContinuousLinearMap.id ℂ _) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul]

theorem primeEulerTranslation_isometry
    (p : CCM24VisiblePrime) :
    ContinuousLinearMap.adjoint
        (CC20Concrete.cc20GlobalLogTranslation
          (-Real.log p)).toContinuousLinearMap *
        (CC20Concrete.cc20GlobalLogTranslation
          (-Real.log p)).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.mul_apply,
    cc20GlobalLogTranslation_neg_adjoint]
  change cc20GlobalLogTranslation (Real.log p)
      (cc20GlobalLogTranslation (-Real.log p) u) = u
  rw [cc20GlobalLogTranslation_add_apply]
  simpa using cc20GlobalLogTranslation_zero_apply u

theorem primeEulerTranslation_coisometry
    (p : CCM24VisiblePrime) :
    (CC20Concrete.cc20GlobalLogTranslation
      (-Real.log p)).toContinuousLinearMap *
        ContinuousLinearMap.adjoint
          (CC20Concrete.cc20GlobalLogTranslation
            (-Real.log p)).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.mul_apply,
    cc20GlobalLogTranslation_neg_adjoint]
  change cc20GlobalLogTranslation (-Real.log p)
      (cc20GlobalLogTranslation (Real.log p) u) = u
  rw [cc20GlobalLogTranslation_add_apply]
  simpa using cc20GlobalLogTranslation_zero_apply u

/-!
This constructor freezes the ambient unitary and scalar to the real CCM24
Euler data.  It does not manufacture the projected resolvent: every support
identity on that resolvent is carried through from the source input.
-/
noncomputable def PrimeEulerProjectedJuliaInput.toColligation
    (data : PrimeEulerProjectedJuliaInput) :
    ProjectedUnitaryColligation
      (CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
        CC20Concrete.cc20GlobalLogCrossingL2) := by
  let U :=
    (CC20Concrete.cc20GlobalLogTranslation
      (-Real.log data.prime)).toContinuousLinearMap
  let a := (ccm24PrimeEulerCoefficient data.prime : ℂ) •
    (ContinuousLinearMap.id ℂ
      CC20Concrete.cc20GlobalLogCrossingL2)
  refine
    { projection := data.projection
      transport := U
      scalar := a
      resolvent := data.resolvent
      projection_idempotent := by
        simpa only [ContinuousLinearMap.mul_def] using
          data.projection_idempotent
      projection_selfAdjoint := by
        exact data.projection_selfAdjoint
      transport_isometry := by
        simpa only [U] using primeEulerTranslation_isometry data.prime
      transport_coisometry := by
        simpa only [U] using primeEulerTranslation_coisometry data.prime
      scalar_central := by
        intro b
        simpa only [a] using complexScalarEnd_central
          (ccm24PrimeEulerCoefficient data.prime : ℂ) b
      resolvent_left := by
        have hscalar :
            a * ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
              (ContinuousLinearMap.id ℂ _ - data.projection)) =
              (ccm24PrimeEulerCoefficient data.prime : ℂ) •
                ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
                  (ContinuousLinearMap.id ℂ _ - data.projection)) := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [a, ContinuousLinearMap.mul_apply,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.sub_apply, map_sub]
          module
        change
          ((ContinuousLinearMap.id ℂ _ - data.projection) -
            a * ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
              (ContinuousLinearMap.id ℂ _ - data.projection))) *
              data.resolvent = ContinuousLinearMap.id ℂ _ - data.projection
        rw [hscalar]
        simpa [U, ContinuousLinearMap.mul_def] using data.resolvent_left
      resolvent_right := by
        have hscalar :
            a * ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
              (ContinuousLinearMap.id ℂ _ - data.projection)) =
              (ccm24PrimeEulerCoefficient data.prime : ℂ) •
                ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
                  (ContinuousLinearMap.id ℂ _ - data.projection)) := by
          apply ContinuousLinearMap.ext
          intro u
          simp only [a, ContinuousLinearMap.mul_apply,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.sub_apply, map_sub]
          module
        change
          data.resolvent *
              ((ContinuousLinearMap.id ℂ _ - data.projection) -
                a * ((ContinuousLinearMap.id ℂ _ - data.projection) * U *
                  (ContinuousLinearMap.id ℂ _ - data.projection))) =
            ContinuousLinearMap.id ℂ _ - data.projection
        rw [hscalar]
        simpa [U, ContinuousLinearMap.mul_def] using data.resolvent_right
      resolvent_left_support := by
        simpa only [ContinuousLinearMap.mul_def] using
          data.resolvent_left_support
      resolvent_right_support := by
        simpa only [ContinuousLinearMap.mul_def] using
          data.resolvent_right_support }

/-!
The actual factor is recovered without changing its carrier.  This theorem
is intentionally only a readback of the existing Euler transport definition;
it does not identify the complementary resolvent with an orthogonal
projection or with a physical boundary column.
-/
theorem primeEulerTransport_eq_id_sub_translation
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ -
        (ccm24PrimeEulerCoefficient p : ℂ) •
          (CC20Concrete.cc20GlobalLogTranslation
            (-Real.log p)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  exact ccm24PrimeEulerTransportEquiv_apply p u

/-!
The source normalization used by Proof 390 is fixed here, rather than exposed
as an arbitrary factor in the route-facing constructor.  The inverse scalar is
well-defined in `ℂ`; its nonvanishing for visible primes is a separate
elementary side lemma when a concrete estimate needs it.
-/
noncomputable def primeEulerSchurNormalizer
    (p : CCM24VisiblePrime) :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2 :=
  ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
    ContinuousLinearMap.id ℂ _

theorem primeEulerSchurNormalizer_scalar_ne_zero
    (p : CCM24VisiblePrime) :
    (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
  have hreal : (0 : ℝ) < 1 + ccm24PrimeEulerCoefficient p := by
    linarith [ccm24PrimeEulerCoefficient_nonneg p]
  exact_mod_cast (ne_of_gt hreal)

noncomputable def PrimeEulerProjectedJuliaInput.normalizedSchurFrame
    (data : PrimeEulerProjectedJuliaInput) :
    CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ]
      CC20Concrete.cc20GlobalLogCrossingL2 :=
  primeEulerSchurNormalizer data.prime ∘L
    data.toColligation.schurFrame data.toColligation.graphCosine

noncomputable def PrimeEulerProjectedJuliaInput.toSchurFrameJuliaRangeStepData
    (data : PrimeEulerProjectedJuliaInput)
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (rangeSine readout :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ] G)
    (weight : ℝ) (weight_nonneg : 0 ≤ weight)
    (transfer_contract :
      ContinuousLinearMap.adjoint data.normalizedSchurFrame ∘L
        data.normalizedSchurFrame ≤
        ContinuousLinearMap.id ℂ _)
    (rangeSine_weighted_le : ∀ x,
      weight * ‖rangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect data.normalizedSchurFrame transfer_contract x‖ ^ 2)
    (rangeSine_readback :
      rangeSine = readout ∘L data.toColligation.graphSine
        data.toColligation.graphCosine) :
    SchurFrameJuliaRangeStepData
      CC20Concrete.cc20GlobalLogCrossingL2 G := by
  refine
    { colligation := data.toColligation
      cosine := data.toColligation.graphCosine
      cosine_eq_graphCosine := rfl
      frameNormalizer := primeEulerSchurNormalizer data.prime
      normalizedFrame := data.normalizedSchurFrame
      normalizedFrame_eq := rfl
      transfer_contract := transfer_contract
      rangeSine := rangeSine
      readout := readout
      weight := weight
      weight_nonneg := weight_nonneg
      rangeSine_weighted_le := rangeSine_weighted_le
      rangeSine_readback := rangeSine_readback }

noncomputable def PrimeEulerProjectedJuliaInput.toPrimeSchurFrameJuliaRangeStepData
    (data : PrimeEulerProjectedJuliaInput)
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (rangeSine readout :
      CC20Concrete.cc20GlobalLogCrossingL2 →L[ℂ] G)
    (transfer_contract :
      ContinuousLinearMap.adjoint data.normalizedSchurFrame ∘L
        data.normalizedSchurFrame ≤
        ContinuousLinearMap.id ℂ _)
    (rangeSine_weighted_le : ∀ x,
      primeJuliaWeight data.prime * ‖rangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect data.normalizedSchurFrame transfer_contract x‖ ^ 2)
    (rangeSine_readback :
      rangeSine = readout ∘L data.toColligation.graphSine
        data.toColligation.graphCosine) :
    SchurFrameJuliaRangeStepData
      CC20Concrete.cc20GlobalLogCrossingL2 G :=
  data.toSchurFrameJuliaRangeStepData rangeSine readout
    (primeJuliaWeight data.prime) (primeJuliaWeight_nonneg data.prime)
    transfer_contract rangeSine_weighted_le rangeSine_readback

end CCM24FiniteSJuliaSchur
end CCM25Concrete
end Source
end ConnesWeilRH
