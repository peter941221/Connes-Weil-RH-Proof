import ConnesWeilRH.Dev.C1ExplicitHealthyCorrectionBudget
import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Dev.C1HealthyYoshidaUnscaledOrbit

/-! Same-owner rho facts for the powered-seed n=3 construction (3111).

The powered-seed carrier from 3110 fixes the finite pin object.  This module
connects the existing explicit healthy powered-seed correction to the rho
owner duties used by Route-B: target interpolation on the healthy node set,
closed-ball square-zero transport, minimal detection, centered orbit sum, and
support.  It does not prove the tail budget, cardinal pins, fixed-24 gate, or
spectral prefix sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBPoweredSeedOwnerFacts3111

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1ExplicitHealthyCorrectionBudget
open C1ExplicitSmoothSeed
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1HealthyYoshidaUnscaledOrbit
open C1SpectralWeil
open scoped BigOperators

noncomputable section

def poweredSeedExplicitOwner3111 (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) : CompactLogTest :=
  (selectedOwner (explicitPoweredHealthyBase rho)
    (explicitPoweredHealthyCorrection rho N routeNodes) 3).sourceTest

theorem poweredSeedExplicitOwner_target3111
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt (poweredSeedExplicitOwner3111 rho N routeNodes)
      (w.1 - 1 / 2) = healthyUnscaledTargetValue rho w := by
  exact selectedOwner_explicitPoweredHealthy_target rho N routeNodes 3 (w := w)

theorem poweredSeedExplicitOwner_square_zero3111
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (z : FiniteMellinNode
      (sourceNontrivialZerosInClosedBallFinset rho
          ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho) ∪ routeNodes))
    (hz : z.1 ∉ healthyUnscaledTargetNodes rho) :
    laplaceAt (poweredSeedExplicitOwner3111 rho N routeNodes).convolutionSquare
      (z.1 - 1 / 2) = 0 := by
  have hk : z.1 ∈ healthyKillSet rho N routeNodes := by
    simpa only [healthyKillSet] using z.2
  have hselected := selectedOwner_explicitPoweredHealthy_kills
    rho N routeNodes 3 z hz
  have hraw :
      laplaceAt
        ((convolutionIterate (explicitPoweredHealthyBase rho) 3).convolution
          (explicitPoweredHealthyCorrection rho N routeNodes)) z.1 = 0 := by
    simpa only [selectedOwner_laplaceAt_sourceTest_centered] using hselected
  simpa only [poweredSeedExplicitOwner3111] using
    selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      (explicitPoweredHealthyBase rho)
      (explicitPoweredHealthyCorrection rho N routeNodes) 3 z.1 hraw

theorem poweredSeedExplicitOwner_minimal3111
    (rho : sourceNontrivialZeroSet) (N : ℕ)
    (routeNodes : Finset ℂ)
    (hoff : rho.1.re ≠ 1 / 2) :
    HealthyMinimalLaplaceRealizes rho.1
      (poweredSeedExplicitOwner3111 rho.1 N routeNodes) := by
  have hhalf :
      laplaceAt (poweredSeedExplicitOwner3111 rho.1 N routeNodes) 0 = 0 := by
    have h := poweredSeedExplicitOwner_target3111 rho.1 N routeNodes
      ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩
    rw [show ((1 / 2 : ℂ) - 1 / 2) = 0 by ring] at h
    exact h.trans (healthyUnscaledTargetValue_half rho.2 hoff)
  have hone :
      laplaceAt (poweredSeedExplicitOwner3111 rho.1 N routeNodes) (1 / 2) = 0 := by
    have h := poweredSeedExplicitOwner_target3111 rho.1 N routeNodes
      ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩
    rw [show ((1 : ℂ) - 1 / 2) = (1 / 2 : ℂ) by ring] at h
    exact h.trans (healthyUnscaledTargetValue_one rho.2 hoff)
  have hthreeHalf :
      laplaceAt (poweredSeedExplicitOwner3111 rho.1 N routeNodes) 1 = 0 := by
    have h := poweredSeedExplicitOwner_target3111 rho.1 N routeNodes
      ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩
    rw [show ((3 / 2 : ℂ) - 1 / 2) = 1 by ring] at h
    exact h.trans (healthyUnscaledTargetValue_threeHalf rho.2)
  have hdet :
      laplaceAt (poweredSeedExplicitOwner3111 rho.1 N routeNodes) rho.1 ≠ 0 := by
    have h := poweredSeedExplicitOwner_target3111 rho.1 N routeNodes
      ⟨rho.1 + 1 / 2, mem_healthyUnscaledTargetNodes_detector rho.1⟩
    rw [show (rho.1 + 1 / 2) - 1 / 2 = rho.1 by ring] at h
    rw [h]
    exact healthyUnscaledTargetValue_detector_ne_zero rho.1 hoff
  exact ⟨hhalf, hone, hthreeHalf, hdet⟩

theorem poweredSeedExplicitOwner_centeredOrbit_sum3111
    (rho : sourceNontrivialZeroSet) (N : ℕ)
    (routeNodes : Finset ℂ) (hoff : rho.1.re ≠ 1 / 2) :
    (∑ u ∈ centeredFunctionalEquationOrbit rho.1,
      laplaceAt
        (poweredSeedExplicitOwner3111 rho.1 N routeNodes).convolutionSquare u) = -2 := by
  have hrawOrbit : ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
      laplaceAt
        ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
          (explicitPoweredHealthyCorrection rho.1 N routeNodes)) w.1 =
        negativeSourceOrbitValue rho.1 w := by
    intro w
    have htarget := selectedOwner_explicitPoweredHealthy_target
      rho.1 N routeNodes 3
      (w := (⟨w.1, Finset.mem_union_left _ w.2⟩ :
        FiniteMellinNode (healthyUnscaledTargetNodes rho.1)))
    have hraw' :
        laplaceAt
          ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
            (explicitPoweredHealthyCorrection rho.1 N routeNodes)) w.1 =
          healthyUnscaledTargetValue rho.1
            ⟨w.1, Finset.mem_union_left _ w.2⟩ := by
      simpa only [selectedOwner_laplaceAt_sourceTest_centered] using htarget
    exact hraw'.trans (healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2)
  have hrawRho :
      laplaceAt
        ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
          (explicitPoweredHealthyCorrection rho.1 N routeNodes)) rho.1 = 1 := by
    calc
      _ = negativeSourceOrbitValue rho.1
          ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩ :=
        hrawOrbit ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩
      _ = 1 := negativeSourceOrbitValue_rho rho.1
  have hrawCompanion :
      laplaceAt
        ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
          (explicitPoweredHealthyCorrection rho.1 N routeNodes)
        ) (1 - star rho.1) = -1 := by
    calc
      _ = negativeSourceOrbitValue rho.1
          ⟨1 - star rho.1,
            mem_sourceFunctionalEquationOrbit_companion rho.1⟩ :=
        hrawOrbit ⟨1 - star rho.1,
          mem_sourceFunctionalEquationOrbit_companion rho.1⟩
      _ = -1 := negativeSourceOrbitValue_companion rho.1 hoff
  have hrawOrbit' := hrawOrbit
  simpa only [poweredSeedExplicitOwner3111] using
    selectedOwner_centeredOrbit_sum_eq_neg_two
      (explicitPoweredHealthyBase rho.1)
      (explicitPoweredHealthyCorrection rho.1 N routeNodes) 3 rho.1 hoff
      hrawRho hrawCompanion hrawOrbit'

theorem poweredSeedExplicitOwner_support3111
    (rho : sourceNontrivialZeroSet) (N : ℕ)
    (routeNodes : Finset ℂ) :
    Function.support (poweredSeedExplicitOwner3111 rho.1 N routeNodes).test ⊆
      Set.Ioo (-55 : ℝ) 55 := by
  have hbase : Function.support (explicitPoweredHealthyBase rho.1).test ⊆
      Set.Ioo (-11 : ℝ) 11 := by
    intro x hx
    have h := explicitPoweredHealthyBase_support rho.1 hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hcorr : Function.support
      (explicitPoweredHealthyCorrection rho.1 N routeNodes).test ⊆
      Set.Ioo (-11 : ℝ) 11 := by
    intro x hx
    have h := explicitPoweredHealthyCorrection_support rho.1 N routeNodes hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hconv := convolutionIterate_convolution_support_subset_Ioo
    (explicitPoweredHealthyBase rho.1)
    (explicitPoweredHealthyCorrection rho.1 N routeNodes) hbase hcorr 3
  have hcast : ((3 + 1 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  rw [hcast] at hconv
  have hradius : Function.support
      ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
        (explicitPoweredHealthyCorrection rho.1 N routeNodes)).test ⊆
      Set.Ioo (-55 : ℝ) 55 := by
    convert hconv using 1 <;> norm_num
  simpa only [poweredSeedExplicitOwner3111, selectedOwner_sourceTest] using
    halfDensityShift_support_subset
      ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
        (explicitPoweredHealthyCorrection rho.1 N routeNodes)) hradius

end
end C1RouteBPoweredSeedOwnerFacts3111
end Source
end ConnesWeilRH
