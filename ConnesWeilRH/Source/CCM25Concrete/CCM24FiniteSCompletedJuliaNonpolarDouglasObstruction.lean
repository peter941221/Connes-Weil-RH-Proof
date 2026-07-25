/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaComponentNonpolarDouglas
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaComponentObstruction

/-!
# Direct obstruction for the non-polar Douglas gate

Proof 548 makes uniform component rows a direct entrance to Proof 547's
non-polar Douglas gate.  This module records the matching obstruction side:
a nonzero zero-mode on the actual packed physical-analysis kernel rules out
the direct non-polar Douglas producer and therefore the component-row route.

No obstruction vector is constructed here.  The file only fixes the exact
kernel test that any future source producer must pass.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarDouglasObstruction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaComponentNonpolarDouglas
open CCM24FiniteSCompletedJuliaComponentObstruction
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarGapDouglas
open CCM24FiniteSCompletedJuliaNonpolarGapKernel
open CCM24FiniteSCompletedJuliaNonpolarGapObstruction
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Direct non-polar Douglas no-go forms -/

/-- A nonzero non-polar gap adjoint on the adjacent co-defect kernel rules
out a uniform direct non-polar Douglas package with the specified bound. -/
theorem noUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) := by
  rintro ⟨data⟩
  exact
    (noUniformNonpolarGapFactor_of_adjoint_ne_zero_on_leftCoDefectKernel
      p S x hx hgap bound) ⟨data.toFactorData⟩

/-- The same nonzero gap zero-mode rules out existence of any finite uniform
direct non-polar Douglas bound. -/
theorem noExistsUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact noUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    (bound := bound) p S x hx hgap hdata

/-- A raw-row nonzero zero-mode on the adjacent co-defect kernel rules out a
uniform direct non-polar Douglas package with the specified bound. -/
theorem noUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) := by
  have hgap :
      ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†)
        x ≠ 0 := by
    intro hzero
    exact hraw
      ((suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_raw
        owner lambda p S x hx).mp hzero)
  exact noUniformNonpolarGapDouglas_of_gapAdjoint_ne_zero
    (bound := bound) p S x hx hgap

/-- A raw-row nonzero zero-mode rules out existence of any finite uniform
direct non-polar Douglas bound. -/
theorem noExistsUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact noUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    (bound := bound) p S x hx hraw hdata

/-! ## Packed physical-analysis kernel readbacks -/

/-- The raw zero-mode test may be stated on the packed physical-analysis
kernel instead of the adjacent co-defect kernel. -/
theorem noExistsUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero_on_analysis
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixLocalNonpolarGapUniformDouglasData owner lambda bound) := by
  have hxLeft :
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0 :=
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mp hx
  exact noExistsUniformNonpolarGapDouglas_of_rawAdjoint_ne_zero
    p S x hxLeft hraw

/-- The same packed-kernel raw zero-mode also rules out the uniform
component-row entrance supplied by Proof 548. -/
theorem noExistsUniformComponentReadout_of_rawAdjoint_ne_zero_on_analysis
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound) := by
  have hxLeft :
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0 :=
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mp hx
  exact noExistsUniformComponentReadout_of_rawAdjoint_ne_zero
    p S x hxLeft hraw

end CCM24FiniteSCompletedJuliaNonpolarDouglasObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
