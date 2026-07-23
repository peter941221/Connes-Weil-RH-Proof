/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaUniformRawReadout

/-!
# Family-uniform completed-Julia co-defect factors

Proof 509 packages a uniform physical Douglas readout for every adjacent
visible-prime/suffix pair.  The local signed trace owner consumes the
corresponding factor through the actual Julia left co-defect.  This module
performs that exact handoff for the whole family, retaining one common norm
bound and the genuine local factorization.

The construction is one-way: a physical domination producer yields these
co-defect factors.  A factor family alone is not promoted back to physical
domination, because the scalar-normalized forward transition in the reverse
direction is not contractive.  No trace estimate, Gate 3U sign, Burnol
identity, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaUniformCoDefectFactor

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The family-level local owner -/

/-- A common-bound family of genuine local Douglas factors.  Each member
factors the two-sided local mismatch through the actual adjacent Julia
left co-defect. -/
structure SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixMismatchCoDefectFactorData owner lambda p S bound

/-- Convert the physical uniform domination into the family of local factors
used by the signed trace owner. -/
noncomputable def
    SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformCoDefectFactorData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      suffixMismatchCoDefectFactorDataOfAmbientBoundaryDomination owner lambda
        p S bound (data.domination p S) }

/-- A readout family can be handed to the local owner without changing its
common numerical bound. -/
noncomputable def
    SuffixMismatchAmbientBoundaryUniformReadoutData.toCoDefectFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformCoDefectFactorData owner lambda bound :=
  SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor
    data.toDomination

/-! ## Readback for each adjacent pair -/

theorem SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S =
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        (data.factor p S).rightFactor := by
  exact (data.factor p S).factorization

theorem SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.factor_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖(data.factor p S).rightFactor‖ ≤ bound := by
  exact (data.factor p S).rightFactor_norm_le

/-- Every family member inherits the exact zero-mode consequence: the adjoint
of the local mismatch vanishes on the adjacent Julia co-defect kernel. -/
theorem SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.adjoint_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)†) x = 0 := by
  exact (data.factor p S).adjoint_eq_zero_of_leftCoDefect_eq_zero hx

/-- The physical uniform producer exports the local factor family and all its
pointwise readbacks in one theorem. -/
theorem SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor_factor_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor
      data).factor p S).rightFactor‖ ≤ bound := by
  exact SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.factor_norm_le
    (SuffixMismatchAmbientBoundaryUniformDominationData.toCoDefectFactor data)
    p S

end CCM24FiniteSCompletedJuliaUniformCoDefectFactor
end CCM25Concrete
end Source
end ConnesWeilRH
