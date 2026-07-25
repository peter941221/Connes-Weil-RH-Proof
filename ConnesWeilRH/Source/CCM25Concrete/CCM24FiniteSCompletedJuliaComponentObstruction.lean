/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaComponentKernel

/-!
# Component-row zero-mode obstruction

Proof 536 says a component-row producer kills the raw four-term row and the
complete polar/raw mismatch on the actual adjacent left-co-defect kernel.
This module records the contrapositive as a reusable guard.

If either adjoint has a nonzero vector on that kernel, then no component-row
producer exists for the suffix.  Since Proof 535 identifies uniform component
rows with the family-uniform physical Douglas contract, the same vector also
rules out that uniform contract.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaComponentObstruction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaComponentKernel
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Single-suffix obstruction -/

/-- A nonzero raw four-term adjoint on the left-co-defect kernel forbids a
component-row factorization for this suffix. -/
theorem noComponentReadout_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryComponentReadoutData
        owner lambda p S ambientBound boundaryBound) := by
  rintro ⟨data⟩
  exact hraw
    (componentReadout_rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
      data x hx)

/-- A nonzero complete polar/raw mismatch adjoint on the left-co-defect
kernel forbids a component-row factorization for this suffix. -/
theorem noComponentReadout_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryComponentReadoutData
        owner lambda p S ambientBound boundaryBound) := by
  rintro ⟨data⟩
  exact hmismatch
    (componentReadout_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
      data x hx)

/-! ## Uniform-family obstruction -/

/-- The same raw zero-mode obstruction forbids a uniform component-row
package, independently of the numerical component bounds. -/
theorem noUniformComponentReadout_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryUniformComponentReadoutData
        owner lambda ambientBound boundaryBound) := by
  rintro ⟨data⟩
  exact hraw
    (componentReadout_rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
      (data.readout p S) x hx)

/-- The same mismatch zero-mode obstruction forbids a uniform component-row
package, independently of the numerical component bounds. -/
theorem noUniformComponentReadout_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryUniformComponentReadoutData
        owner lambda ambientBound boundaryBound) := by
  rintro ⟨data⟩
  exact hmismatch
    (componentReadout_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
      (data.readout p S) x hx)

/-- A raw zero-mode obstruction rules out the existence of any uniform
component-row bounds. -/
theorem noExistsUniformComponentReadout_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound) := by
  rintro ⟨ambientBound, boundaryBound, hdata⟩
  exact
    (noUniformComponentReadout_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
      (owner := owner) (lambda := lambda)
      (ambientBound := ambientBound) (boundaryBound := boundaryBound)
      p S x hx hraw) hdata

/-- A mismatch zero-mode obstruction rules out the existence of any uniform
component-row bounds. -/
theorem noExistsUniformComponentReadout_of_mismatchAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ ambientBound boundaryBound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformComponentReadoutData
          owner lambda ambientBound boundaryBound) := by
  rintro ⟨ambientBound, boundaryBound, hdata⟩
  exact
    (noUniformComponentReadout_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
      (owner := owner) (lambda := lambda)
      (ambientBound := ambientBound) (boundaryBound := boundaryBound)
      p S x hx hmismatch) hdata

/-! ## Physical-Douglas obstruction -/

/-- By Proof 535, a raw zero-mode obstruction also rules out the uniform
physical Douglas domination contract. -/
theorem noExistsUniformPhysicalDomination_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound) := by
  intro hdom
  have hcomponent :
      ∃ ambientBound boundaryBound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformComponentReadoutData
            owner lambda ambientBound boundaryBound) :=
    (exists_uniformComponentReadout_iff_exists_uniformPhysicalDomination
      owner lambda).mpr hdom
  exact
    (noExistsUniformComponentReadout_of_rawAdjoint_ne_zero
      p S x hx hraw) hcomponent

/-- By Proof 535, a mismatch zero-mode obstruction also rules out the uniform
physical Douglas domination contract. -/
theorem noExistsUniformPhysicalDomination_of_mismatchAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixMismatchAmbientBoundaryUniformDominationData
          owner lambda bound) := by
  intro hdom
  have hcomponent :
      ∃ ambientBound boundaryBound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformComponentReadoutData
            owner lambda ambientBound boundaryBound) :=
    (exists_uniformComponentReadout_iff_exists_uniformPhysicalDomination
      owner lambda).mpr hdom
  exact
    (noExistsUniformComponentReadout_of_mismatchAdjoint_ne_zero
      p S x hx hmismatch) hcomponent

end CCM24FiniteSCompletedJuliaComponentObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
