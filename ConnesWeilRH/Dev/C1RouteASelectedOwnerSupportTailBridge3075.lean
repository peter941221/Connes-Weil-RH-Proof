/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RouteASelectedOwnerResidualReadback

/-!
# Route A selected-owner support and tail bridges

These are the two transport steps that are already justified by the existing
selected-owner definitions.  They do not identify the selected owner with the
fixed record-2678/2680 coefficient owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteASelectedOwnerSupportTailBridge3075

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaCorrectionFamily

noncomputable section

theorem residualFamily_selectedOwner_support_subset_Icc
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat) (baseRadius : Real)
    (y : FiniteMellinNode nodes → Complex)
    (hbase : Function.support base.test ⊆ Set.Ioo (-baseRadius) baseRadius) :
    Function.support
        (selectedOwner base (family.value y) n).sourceTest.test ⊆
      Set.Icc
        (-((n + 1 : Nat) * baseRadius) + lower)
        (((n + 1 : Nat) * baseRadius) + upper) := by
  have hiterate := convolutionIterate_support_subset_Ioo base hbase n
  have hraw := convolution_support_subset_add_Ioo
    (convolutionIterate base n) (family.value y) hiterate (family.support y)
  have hshift := halfDensityShift_support_subset
    ((convolutionIterate base n).convolution (family.value y)) hraw
  rw [selectedOwner_sourceTest]
  intro x hx
  have hx' := hshift hx
  exact ⟨le_of_lt (by nlinarith [hx'.1]), le_of_lt (by nlinarith [hx'.2])⟩

theorem residualFamily_selectedOwner_source_tail
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex)
    (rho : Complex) (T epsilon : Real)
    (htail : ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt ((convolutionIterate base n).convolution
              (family.value y)) z‖ < epsilon) :
    ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| → 2 * |rho.im| ≤ |z.im| →
        ‖z - rho‖ ^ 2 *
            ‖laplaceAt (selectedOwner base (family.value y) n).sourceTest
              (z - 1 / 2)‖ < epsilon := by
  exact selectedOwner_centered_source_distance_bound_lt base (family.value y) n rho T
    epsilon htail

end
end C1RouteASelectedOwnerSupportTailBridge3075
end Source
end ConnesWeilRH
