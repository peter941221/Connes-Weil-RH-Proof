/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaPolarRawReadout

/-!
# Family-uniform completed-Julia raw readout

Proof 508 gives a physical readout for one adjacent suffix under a supplied
Douglas domination.  Gate 3U needs the same bound for every visible prime and
every finite suffix.  This module packages exactly that quantifier and nothing
more.

The family package is equivalent to a family of bounded physical readouts.
It then transports each readout through the unconditional polar correction,
giving a family-uniform raw factorization and pointwise bound.  The domination
field remains an analytic producer obligation; no Gate 3U estimate, finite-S
sign, Burnol identity, or RH premise is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaUniformRawReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaPhysicalDouglasReadout
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The uniform producer contract -/

/-- One nonnegative bound dominating the complete signed mismatch on every
visible-prime/suffix pair.  The ambient and boundary energies stay summed in
the underlying physical domination predicate. -/
structure SuffixMismatchAmbientBoundaryUniformDominationData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  domination : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixMismatchAmbientBoundaryDomination owner lambda p S bound

/-- A family of actual bounded readouts with one common norm bound. -/
structure SuffixMismatchAmbientBoundaryUniformReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  readout : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixMismatchAmbientBoundaryReadoutData owner lambda p S bound

/-- Turn the uniform physical domination contract into its readout family.
Each member is the genuine Douglas readout from Proof 507. -/
noncomputable def
    SuffixMismatchAmbientBoundaryUniformDominationData.toReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) :
  SuffixMismatchAmbientBoundaryUniformReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
        suffixMismatchAmbientBoundaryReadoutDataOfDomination owner lambda p S
          bound (data.domination p S) }

theorem SuffixMismatchAmbientBoundaryUniformDominationData.toReadout_readout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    data.toReadout.readout p S =
      suffixMismatchAmbientBoundaryReadoutDataOfDomination owner lambda p S
        bound (data.domination p S) := by
  rfl

/-- Conversely, a readout family is already a uniform domination producer.
This makes the interface an exact equivalence rather than a stronger hidden
assumption. -/
noncomputable def
    SuffixMismatchAmbientBoundaryUniformReadoutData.toDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformDominationData owner lambda bound := by
  exact
    { bound_nonneg := data.bound_nonneg
      domination := fun p S => (data.readout p S).domination }

/-- The two family contracts are equivalent, including the shared numerical
bound. -/
theorem uniformDomination_iff_nonempty_uniformReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) ↔
      Nonempty (SuffixMismatchAmbientBoundaryUniformReadoutData
        owner lambda bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toReadout⟩
  · rintro ⟨data⟩
    exact ⟨data.toDomination⟩

/-! ## Uniform raw readout consequences -/

/-- The physical readout supplied for one suffix by a uniform family. -/
noncomputable def SuffixMismatchAmbientBoundaryUniformReadoutData.forSuffix
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    SuffixMismatchAmbientBoundaryReadoutData owner lambda p S bound :=
  data.readout p S

/-- The corrected readout of the raw one-sided intertwinement. -/
noncomputable def SuffixMismatchAmbientBoundaryUniformReadoutData.rawReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameAmbientBoundaryCarrier →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  rawCorrectionReadout (data.forSuffix p S)

theorem SuffixMismatchAmbientBoundaryUniformReadoutData.rawReadout_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    data.rawReadout p S ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      (suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)† := by
  exact rawCorrection_factorization (data.forSuffix p S)

theorem SuffixMismatchAmbientBoundaryUniformReadoutData.rawReadout_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖data.rawReadout p S‖ ≤
      ‖CCM24FiniteSProjectionTrace.detectorOperator owner‖ + bound := by
  exact rawCorrection_norm_le (data.forSuffix p S)

/-- Every member of a uniform family satisfies the same raw adjoint bound.
The bound is against the summed physical analysis column, not separate
ambient and boundary estimates. -/
theorem SuffixMismatchAmbientBoundaryUniformReadoutData.rawAdjoint_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformReadoutData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (x : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†) x‖ ≤
      (‖CCM24FiniteSProjectionTrace.detectorOperator owner‖ + bound) *
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
  exact SuffixMismatchAmbientBoundaryReadoutData.rawAdjoint_norm_le
    (data.forSuffix p S) x

/-- The uniform domination contract itself exports the same raw bound by
first constructing the readout family. -/
theorem SuffixMismatchAmbientBoundaryUniformDominationData.rawAdjoint_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformDominationData
      owner lambda bound) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (x : CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†) x‖ ≤
      (‖CCM24FiniteSProjectionTrace.detectorOperator owner‖ + bound) *
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ := by
  exact SuffixMismatchAmbientBoundaryUniformReadoutData.rawAdjoint_norm_le
    data.toReadout p S x

end CCM24FiniteSCompletedJuliaUniformRawReadout
end CCM25Concrete
end Source
end ConnesWeilRH
