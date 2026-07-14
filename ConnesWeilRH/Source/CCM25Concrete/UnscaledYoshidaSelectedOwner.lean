/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaFullProduct
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Selected owner for the unscaled Yoshida assembly

This module keeps the support-growing Yoshida source factor tied to the
existing selected convolution square and whole-line finite-prime crossing
operator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace UnscaledYoshidaSelectedOwner

open CC20YoshidaNearZeros
open CC20YoshidaConvolution.CompactLogTest
open CompactLogConvolution
open ConnesWeilRH.Source.CC20Concrete
open SelectedCrossingOperatorBridge
open scoped ComplexConjugate InnerProductSpace

/-- The existing selected square owner applied to one unscaled Yoshida source
factor. The convolution square remains definitional. -/
noncomputable def selectedOwner
    (base correction : CompactLogTest) (n : ℕ) :
    SelectedWeilSquare.SelectedWeilSquareOwner :=
  SelectedWeilSquare.SelectedWeilSquareOwner.ofCompactLogTest
    ((convolutionIterate base n).convolution correction)

@[simp] theorem selectedOwner_sourceTest
    (base correction : CompactLogTest) (n : ℕ) :
    (selectedOwner base correction n).sourceTest =
      (convolutionIterate base n).convolution correction :=
  rfl

@[simp] theorem selectedOwner_convolutionSquare
    (base correction : CompactLogTest) (n : ℕ) :
    (selectedOwner base correction n).convolutionSquare =
      ((convolutionIterate base n).convolution correction).convolutionSquare :=
  rfl

/-- Normalizing both points in the Hermitian orbit normalizes the actual
selected convolution square at `rho`. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_one
    (base correction : CompactLogTest) (n : ℕ) (rho : ℂ)
    (hrho :
      laplaceAt ((convolutionIterate base n).convolution correction) rho = 1)
    (hcomp :
      laplaceAt ((convolutionIterate base n).convolution correction)
        (-star rho) = 1) :
    laplaceAt (selectedOwner base correction n).convolutionSquare rho = 1 := by
  rw [selectedOwner_convolutionSquare, CompactLogTest.convolutionSquare,
    laplaceAt_convolution, laplaceAt_involution, hcomp, hrho]
  simp

/-- A zero of the assembled source factor is a zero of the selected
convolution square at the same node. -/
theorem selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
    (base correction : CompactLogTest) (n : ℕ) (z : ℂ)
    (hz :
      laplaceAt ((convolutionIterate base n).convolution correction) z = 0) :
    laplaceAt (selectedOwner base correction n).convolutionSquare z = 0 := by
  rw [selectedOwner_convolutionSquare, CompactLogTest.convolutionSquare,
    laplaceAt_convolution, laplaceAt_involution, hz]
  simp

theorem selectedOwner_sourceTest_support_subset_Icc
    (base correction : CompactLogTest) (n : ℕ) {a c : ℝ}
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c) :
    Function.support (selectedOwner base correction n).sourceTest.test ⊆
      Set.Icc a c := by
  intro x hx
  have hbounds := hsupport (by simpa using hx)
  exact ⟨hbounds.1.le, hbounds.2.le⟩

/-- The whole-line finite-prime operator built from the assembled Yoshida
source factor is compact whenever the existing per-prime basis witnesses are
supplied. -/
theorem operatorSum_isCompactOperator
    (base correction : CompactLogTest) (n : ℕ)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    IsCompactOperator
      (eulerLogWeightedGlobalPairTraceOperatorSum
        (selectedOwner base correction n) terms) := by
  exact eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator
    (selectedOwner base correction n) a c terms hprime
    (selectedOwner_sourceTest_support_subset_Icc
      base correction n hsupport) globalBasis basisData

theorem operatorSum_isSelfAdjoint
    (base correction : CompactLogTest) (n : ℕ)
    (terms : Finset (ℕ × ℕ)) :
    IsSelfAdjoint
      (eulerLogWeightedGlobalPairTraceOperatorSum
        (selectedOwner base correction n) terms) :=
  eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint
    (selectedOwner base correction n) terms

/-- The compact operator trace and the selected finite-prime sum use the same
assembled Yoshida source factor and the same selected square owner. -/
theorem ordinaryTraceAlong_operatorSum_eq_finitePrimeTerm_pow_sum
    (base correction : CompactLogTest) (n : ℕ)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupport : Function.support
        ((convolutionIterate base n).convolution correction).test ⊆
      Set.Ioo a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperatorSum
          (selectedOwner base correction n) terms) =
      ∑ pm ∈ terms,
        (selectedOwner base correction n).finitePrimeTerm (pm.1 ^ pm.2) := by
  exact
    ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
      (selectedOwner base correction n) a c terms hprime hnonzero
      (selectedOwner_sourceTest_support_subset_Icc
        base correction n hsupport) globalBasis basisData

/-- The fixed-threshold Hermitian construction produces an actual selected
owner whose convolution square detects `rho`, cancels the selected non-target
nodes, and retains the same unscaled far-tail estimate. -/
theorem exists_fixedWindows_nearbyZero_selectedOwner
    (rho : ℂ) (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (routeNodes : Finset ℂ)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ base : CompactLogTest, ∃ T : ℝ,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      0 ≤ T ∧
      ∀ R : ℝ, 0 ≤ R →
        ∃ correction : CompactLogTest, ∃ C : ℝ, ∃ n : ℕ,
          Function.support correction.test ⊆ Set.Ioo lower upper ∧
          Function.support (selectedOwner base correction n).sourceTest.test ⊆
            Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
              (((n + 1 : ℕ) : ℝ) * baseUpper + upper) ∧
          laplaceAt (selectedOwner base correction n).sourceTest rho = 1 ∧
          laplaceAt (selectedOwner base correction n).sourceTest (-star rho) = 1 ∧
          laplaceAt (selectedOwner base correction n).convolutionSquare rho = 1 ∧
          (∀ z : FiniteMellinNode
              (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
            z.1 ∉ ({rho, -star rho} : Finset ℂ) →
              laplaceAt (selectedOwner base correction n).convolutionSquare
                z.1 = 0) ∧
          0 ≤ C ∧
          ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 →
            T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
              ‖z - rho‖ ^ 2 *
                  ‖laplaceAt (selectedOwner base correction n).sourceTest z‖ <
                epsilon := by
  obtain ⟨base, T, hbaseSupport, _hbaseRho, _hbaseComp, hT, hfamily⟩ :=
    exists_fixedWindows_nearbyZero_unscaled_hermitian_square_assembly
      rho hrho routeNodes hbaseLower hbaseUpper hlower hupper epsilon hepsilon
  refine ⟨base, T, hbaseSupport, hT, ?_⟩
  intro R hR
  obtain ⟨correction, C, n, hcorrectionSupport, hsourceSupport,
      hsourceRho, hsourceComp, hsquareRho, hsquareZeros, hC, htail⟩ :=
    hfamily R hR
  exact ⟨correction, C, n, hcorrectionSupport, by simpa using hsourceSupport,
    by simpa using hsourceRho, by simpa using hsourceComp,
    by simpa using hsquareRho, by simpa using hsquareZeros, hC,
    by simpa using htail⟩

end UnscaledYoshidaSelectedOwner
end CCM25Concrete
end Source
end ConnesWeilRH
