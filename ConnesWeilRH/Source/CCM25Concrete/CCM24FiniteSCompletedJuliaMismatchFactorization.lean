/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm

/-!
# One-sided Julia factorization of the non-polar mismatch

Proof 504 writes the unresolved local term as the two-sided relative defect

```text
A_(p,S) = F_(p,S) M_S R_(p,S) - rho_p M_(p::S).
```

The exact Schur--Markov identity `F_(p,S) R_(p,S) = rho_p I` removes the
second boundary orientation:

```text
A_(p,S) = (F_(p,S) M_S - M_(p::S) F_(p,S)) R_(p,S).
```

This module records that one-sided intertwining defect, its adjoint readback,
and the precise Douglas domination needed to factor it through the actual
left Julia co-defect.  No domination hypothesis is asserted here: the final
source-specific estimate remains explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaMismatchFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaSynthesis
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSDouglasFactor
open CCM24FiniteSGramResponse
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The one-sided defect -/

/-- The one-sided failure of the polar/raw mismatch to intertwine the
adjacent forward source transition. -/
noncomputable def suffixActualBandRoutePolarRawMismatchIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandRoutePolarRawMismatchKernel owner lambda S -
    suffixActualBandRoutePolarRawMismatchKernel owner lambda (p :: S) ∘L
      suffixEulerFrameTransition lambda p S

/-- The two-sided Proof 504 defect is the one-sided intertwining defect
followed by the contractive reverse transition. -/
theorem suffixActualBandLocalRoutePolarRawMismatchDefect_eq_intertwining_comp_reverse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S =
      suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S ∘L
        suffixEulerFrameReverseTransition lambda p S := by
  have hpair := suffixEulerFrameTransition_comp_reverse lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpairx := congrArg
    (fun operator : SourceOp lambda => operator x) hpair
  simp only [suffixActualBandLocalRoutePolarRawMismatchDefect,
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hpairx ⊢
  rw [hpairx, map_smul]

/-- Adjoint readback of the one-sided mismatch factorization. -/
theorem suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)† =
      (suffixEulerFrameReverseTransition lambda p S)† ∘L
        (suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)† := by
  rw [suffixActualBandLocalRoutePolarRawMismatchDefect_eq_intertwining_comp_reverse]
  exact ContinuousLinearMap.adjoint_comp _ _

/-- The reverse Markov transition cannot enlarge the adjoint-side pointwise
norm.  Therefore all Douglas work may be done on the one-sided defect. -/
theorem norm_suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖((suffixActualBandLocalRoutePolarRawMismatchDefect
        owner lambda p S)†) x‖ ≤
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S)†) x‖ := by
  rw [suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_eq]
  calc
    ‖((suffixEulerFrameReverseTransition lambda p S)†)
        (((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x)‖ ≤
        ‖(suffixEulerFrameReverseTransition lambda p S)†‖ *
          ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S)†) x‖ :=
      ((suffixEulerFrameReverseTransition lambda p S)†).le_opNorm _
    _ = ‖suffixEulerFrameReverseTransition lambda p S‖ *
          ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S)†) x‖ := by
      exact congrArg
        (fun value : ℝ => value *
          ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S)†) x‖)
        (ContinuousLinearMap.adjoint.norm_map
          (suffixEulerFrameReverseTransition lambda p S))
    _ ≤ 1 * ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S)†) x‖ := by
      exact mul_le_mul_of_nonneg_right
        (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
        (norm_nonneg _)
    _ = ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ := one_mul _

/-- The scalar-normalized forward transition is a right inverse of the
reverse transition.  This retains all information discarded by the
contractive readback above. -/
theorem suffixEulerFrameReverse_comp_scaledTransition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameReverseTransition lambda p S ∘L
        ((primeSchurMarkovScalar p : ℂ)⁻¹ •
          suffixEulerFrameTransition lambda p S) =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hp : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hpair := suffixEulerFrameReverse_comp_transition lambda p S
  apply ContinuousLinearMap.ext
  intro x
  have hpairx := congrArg
    (fun operator : SourceOp lambda => operator x) hpair
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hpairx ⊢
  rw [map_smul, hpairx, ← mul_smul]
  simp only [inv_mul_cancel₀ hp, one_smul]

/-- The one-sided defect is recovered exactly from the two-sided local defect.
The price is the explicit scalar-normalized forward transition, not an
inverse of the Julia co-defect. -/
theorem suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_local_comp_recovery
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S =
      suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S ∘L
        ((primeSchurMarkovScalar p : ℂ)⁻¹ •
          suffixEulerFrameTransition lambda p S) := by
  rw [suffixActualBandLocalRoutePolarRawMismatchDefect_eq_intertwining_comp_reverse]
  apply ContinuousLinearMap.ext
  intro x
  have hrecovery := congrArg
    (fun operator : SourceOp lambda => operator x)
    (suffixEulerFrameReverse_comp_scaledTransition lambda p S)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hrecovery ⊢
  rw [hrecovery]

/-- Adjoint readback in the recovering direction. -/
theorem suffixActualBandRoutePolarRawMismatchIntertwiningDefect_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)† =
      (((primeSchurMarkovScalar p : ℂ)⁻¹ •
        suffixEulerFrameTransition lambda p S)†) ∘L
        (suffixActualBandLocalRoutePolarRawMismatchDefect
          owner lambda p S)† := by
  rw [
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_local_comp_recovery]
  exact ContinuousLinearMap.adjoint_comp _ _

/-- The local and one-sided adjoint defects have exactly the same kernel.
The contractive reverse readback loses norm, but it loses no zero modes. -/
theorem suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_eq_zero_iff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ((suffixActualBandLocalRoutePolarRawMismatchDefect
      owner lambda p S)†) x = 0 ↔
      ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S)†) x = 0 := by
  constructor
  · intro hlocal
    rw [suffixActualBandRoutePolarRawMismatchIntertwiningDefect_adjoint_eq]
    simp only [ContinuousLinearMap.comp_apply, hlocal, map_zero]
  · intro hintertwining
    rw [suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_eq]
    simp only [ContinuousLinearMap.comp_apply, hintertwining, map_zero]

/-! ## The actual co-defect ledger -/

/-- The adjacent source Julia co-defect has exactly the two physical losses:
ambient Euler loss and the moving-frame boundary crossing. -/
theorem suffixEulerFrameLeftCoDefect_adjoint_comp_self_eq_ambient_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect) ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
      (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame) ∘L
          rectangularAmbientCoDefect
            (suffixEulerFrameSchurStep lambda p S).transport
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame +
      (suffixEulerFrameSchurStep lambda p S).boundary ∘L
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) := by
  calc
    (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect) ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect =
        rectangularTransitionCoDefect
          (suffixEulerFrameSchurStep lambda p S).transition
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition) :=
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect_adjoint_comp_self
    _ = _ := (suffixEulerFrameSchurStep lambda p S).schur_coDefect_eq_ambient_add_boundary

/-- A zero mode of the left co-defect is also a zero mode of the physical
boundary adjoint. -/
theorem suffixEulerFrameBoundary_adjoint_eq_zero_of_leftCoDefect_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    (ContinuousLinearMap.adjoint
      (suffixEulerFrameSchurStep lambda p S).boundary) x = 0 := by
  apply (norm_eq_zero).mp
  have hbound :=
    (suffixEulerFrameSchurStep lambda p S).boundaryDagger_norm_le_leftCoDefect x
  rw [hx, norm_zero] at hbound
  exact le_antisymm hbound (norm_nonneg _)

/-- The polar detector intertwinement is killed on every co-defect zero mode.
This is the exact boundary part of the kernel guard; it is not a norm split
of the full mismatch. -/
theorem suffixEulerDetectorIntertwiningDefect_adjoint_apply_eq_zero_of_leftCoDefect_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixEulerFrameTransition lambda p S ∘L
        suffixPolarDetectorCompression owner lambda S -
      suffixPolarDetectorCompression owner lambda (p :: S) ∘L
        suffixEulerFrameTransition lambda p S)†) x = 0 := by
  rw [suffixEulerDetectorIntertwiningDefect_eq_boundary,
    suffixEulerDetectorBoundaryDefect_eq_stepBoundary]
  have hboundary := suffixEulerFrameBoundary_adjoint_eq_zero_of_leftCoDefect_eq_zero
    lambda p S x hx
  have hadjoint_neg (operator : SourceOp lambda) :
      (-operator)† = -(operator†) := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]
  rw [hadjoint_neg]
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    hboundary, map_zero,
    ContinuousLinearMap.neg_apply, neg_zero]

/-- The raw quadratic response has its own one-sided intertwinement.  It is
kept whole: the first jet and route ordering are already recombined inside
this response. -/
noncomputable def suffixActualBandRawQuadraticIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixEulerFrameTransition lambda p S ∘L
      suffixActualBandRawQuadraticCycledResponse owner lambda S -
    suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) ∘L
      suffixEulerFrameTransition lambda p S

/-- The complete mismatch intertwinement is the polar boundary row minus the
single recombined raw row.  This identity is for orientation only; no
termwise estimate is licensed by it. -/
theorem suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect owner lambda p S =
      (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S) -
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixActualBandRoutePolarRawMismatchIntertwiningDefect,
    suffixActualBandRoutePolarRawMismatchKernel,
    suffixActualBandRawQuadraticIntertwiningDefect,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_sub]
  abel

/-- On a co-defect zero mode, the full mismatch adjoint reduces exactly to the
adjoint of the recombined raw row.  The actual Douglas estimate must still
control the full signed row before taking a norm. -/
theorem suffixMismatchIntertwining_adjoint_on_leftCoDefectKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x =
      -((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x := by
  rw [suffixActualBandRoutePolarRawMismatchIntertwiningDefect_eq_polar_sub_raw]
  have hpolar :=
    suffixEulerDetectorIntertwiningDefect_adjoint_apply_eq_zero_of_leftCoDefect_eq_zero
      owner lambda p S x hx
  have hadjoint_sub :
      (suffixEulerFrameTransition lambda p S ∘L
          suffixPolarDetectorCompression owner lambda S -
        suffixPolarDetectorCompression owner lambda (p :: S) ∘L
          suffixEulerFrameTransition lambda p S -
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† =
        (suffixEulerFrameTransition lambda p S ∘L
            suffixPolarDetectorCompression owner lambda S -
          suffixPolarDetectorCompression owner lambda (p :: S) ∘L
            suffixEulerFrameTransition lambda p S)† -
          (suffixActualBandRawQuadraticIntertwiningDefect
            owner lambda p S)† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [hadjoint_sub]
  simp only [ContinuousLinearMap.sub_apply]
  rw [hpolar]
  simp only [zero_sub]

/-! ## Exact Douglas boundary -/

/-- The source-specific pointwise estimate which is necessary for the
current Douglas route.  It is deliberately stated on every source vector,
not merely on a Hilbert basis. -/
def SuffixMismatchAdjointDouglasDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2

/-- A right factor through the actual adjacent left Julia co-defect, with
its norm bound retained for the completed synthesis. -/
structure SuffixMismatchCoDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  rightFactor : SourceOp lambda
  rightFactor_norm_le : ‖rightFactor‖ ≤ bound
  factorization :
    suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L rightFactor

/-- Douglas turns the one-sided adjoint domination into the correctly
oriented factorization `A = leftCoDefect ∘ rightFactor`. -/
noncomputable def suffixMismatchCoDefectFactorDataOfDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixMismatchAdjointDouglasDomination
      owner lambda p S bound) :
    SuffixMismatchCoDefectFactorData owner lambda p S bound := by
  let localDefect :=
    suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S
  let leftCoDefect := (suffixEulerFrameSchurStep lambda p S).leftCoDefect
  have hlocal : ∀ x : sourceSoninCarrier lambda,
      ‖(localDefect†) x‖ ^ 2 ≤ bound ^ 2 * ‖leftCoDefect x‖ ^ 2 := by
    intro x
    calc
      ‖(localDefect†) x‖ ^ 2 ≤
          ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
            owner lambda p S)†) x‖ ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
          (norm_suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_le
            owner lambda p S x)
      _ ≤ bound ^ 2 * ‖leftCoDefect x‖ ^ 2 := hdom.2 x
  let factorWitness := exists_factor_of_norm_sq_le (localDefect†) leftCoDefect
    bound hdom.1 hlocal
  let factorAdjoint := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  let rightFactor := factorAdjoint†
  have hrightNorm : ‖rightFactor‖ ≤ bound := by
    change ‖factorAdjoint†‖ ≤ bound
    calc
      ‖factorAdjoint†‖ = ‖factorAdjoint‖ :=
        ContinuousLinearMap.adjoint.norm_map factorAdjoint
      _ ≤ bound := by
        simpa only [factorAdjoint] using factorSpec.1
  have hfactor : localDefect = leftCoDefect ∘L rightFactor := by
    have hadjoint := congrArg ContinuousLinearMap.adjoint factorSpec.2
    have hself : IsSelfAdjoint leftCoDefect := by
      simpa only [leftCoDefect,
        RectangularSchurCoDefectStepData.leftCoDefect] using
        (canonicalJuliaDefect_isSelfAdjoint
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition)
          (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
    have hadjoint' : leftCoDefect ∘L rightFactor = localDefect := by
      simpa only [rightFactor, factorAdjoint,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, hself.adjoint_eq] using hadjoint
    exact hadjoint'.symm
  exact
    { rightFactor := rightFactor
      rightFactor_norm_le := hrightNorm
      factorization := hfactor }

/-- Every successful factorization passes the exact kernel guard: a vector
annihilated by the Julia co-defect is annihilated by the adjoint mismatch. -/
theorem SuffixMismatchCoDefectFactorData.adjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchCoDefectFactorData owner lambda p S bound)
    {x : sourceSoninCarrier lambda}
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandLocalRoutePolarRawMismatchDefect
      owner lambda p S)†) x = 0 := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hmap :
      (suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)† =
        (data.rightFactor)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using hadjoint
  rw [hmap]
  simp only [ContinuousLinearMap.comp_apply, hx, map_zero]

end CCM24FiniteSCompletedJuliaMismatchFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
