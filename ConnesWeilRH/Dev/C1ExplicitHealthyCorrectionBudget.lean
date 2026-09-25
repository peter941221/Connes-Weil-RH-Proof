import ConnesWeilRH.Dev.C1ExplicitCardinalSeedBudget
import ConnesWeilRH.Dev.C1SelectedSquareHeightTail

/-!
# Explicit correction budget on the actual healthy node owner

This module identifies the complete finite node set used by the selected-square
height-tail consumer and instantiates its correction with `smoothSeed`.  The
same correction realizes the healthy target data, kills the complete prefix
owner away from those targets, preserves the seed support, and carries the
finite-order L1 budget from `C1ExplicitCardinalSeedBudget`.

No determinant sign or joint tail margin is asserted here.
-/

namespace ConnesWeilRH.Source.C1ExplicitHealthyCorrectionBudget

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1ExplicitFiniteNodeCorrection
open C1ExplicitSmoothSeed
open C1HealthyYoshidaUnscaledOrbit
open C1LaneRD3Root

noncomputable section

/-- The complete non-target prefix owner used by the selected-square
height-tail construction. -/
def healthyKillSet (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) : Finset ℂ :=
  sourceNontrivialZerosInClosedBallFinset rho
      ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho) ∪ routeNodes

/-- The exact interpolation owner: complete prefix nodes together with every
healthy target node.  `Finset` union removes all collisions. -/
def healthyCorrectionNodes (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) : Finset ℂ :=
  healthyKillSet rho N routeNodes ∪ healthyUnscaledTargetNodes rho

/-- Target data on the complete interpolation owner. -/
def healthyCorrectionValue (rho z : ℂ) : ℂ :=
  if hz : z ∈ healthyUnscaledTargetNodes rho then
    healthyUnscaledTargetValue rho ⟨z, hz⟩
  else 0

/-- The explicit correction used for the complete selected-owner prefix. -/
def explicitHealthyCorrection (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) : CompactLogTest :=
  correction (healthyCorrectionNodes rho N routeNodes) smoothSeed
    (healthyCorrectionValue rho)

/-! Powered-seed variants used by the record-1982 conditioning candidate.
They keep the same complete healthy owner; only the concrete interpolation
seed changes from `smoothSeed` to `poweredSeed`. -/
def explicitPoweredHealthyBase (rho : ℂ) : CompactLogTest :=
  correction (healthyUnscaledTargetNodes rho) poweredSeed (fun _ => 1)

def explicitPoweredHealthyCorrection (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) : CompactLogTest :=
  correction (healthyCorrectionNodes rho N routeNodes) poweredSeed
    (healthyCorrectionValue rho)

theorem explicitPoweredHealthyBase_targets (rho : ℂ)
    (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt (explicitPoweredHealthyBase rho) w.1 = 1 := by
  rw [explicitPoweredHealthyBase]
  exact correction_interpolates _ poweredSeed
    poweredSeed_laplaceAt_zero_ne_zero (fun _ => 1) w.2

theorem explicitPoweredHealthyCorrection_targets (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ)
    (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes) w.1 =
      healthyUnscaledTargetValue rho w := by
  have hmem : w.1 ∈ healthyCorrectionNodes rho N routeNodes := by
    exact Finset.mem_union_right _ w.2
  rw [explicitPoweredHealthyCorrection]
  calc
    laplaceAt
          (correction (healthyCorrectionNodes rho N routeNodes) poweredSeed
            (healthyCorrectionValue rho)) w.1 =
        healthyCorrectionValue rho w.1 :=
      correction_interpolates _ poweredSeed poweredSeed_laplaceAt_zero_ne_zero
        (healthyCorrectionValue rho) hmem
    _ = healthyUnscaledTargetValue rho w := by
      simp [healthyCorrectionValue, w.2]

theorem explicitPoweredHealthyCorrection_kills (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ)
    (z : FiniteMellinNode (healthyKillSet rho N routeNodes))
    (hz : z.1 ∉ healthyUnscaledTargetNodes rho) :
    laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes) z.1 = 0 := by
  have hmem : z.1 ∈ healthyCorrectionNodes rho N routeNodes := by
    exact Finset.mem_union_left _ z.2
  rw [explicitPoweredHealthyCorrection]
  calc
    laplaceAt
          (correction (healthyCorrectionNodes rho N routeNodes) poweredSeed
            (healthyCorrectionValue rho)) z.1 =
        healthyCorrectionValue rho z.1 :=
      correction_interpolates _ poweredSeed poweredSeed_laplaceAt_zero_ne_zero
        (healthyCorrectionValue rho) hmem
    _ = 0 := by simp [healthyCorrectionValue, hz]

theorem explicitPoweredHealthyBase_support (rho : ℂ) :
    Function.support (explicitPoweredHealthyBase rho).test ⊆
      Set.Icc (-10) 10 := by
  exact correction_support _ poweredSeed _
    (poweredSeed_support_subset_Ioo.trans Set.Ioo_subset_Icc_self)

theorem explicitPoweredHealthyCorrection_support (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) :
    Function.support (explicitPoweredHealthyCorrection rho N routeNodes).test ⊆
      Set.Icc (-10) 10 := by
  exact correction_support _ poweredSeed _
    (poweredSeed_support_subset_Ioo.trans Set.Ioo_subset_Icc_self)

theorem l1Mass_explicitPoweredHealthyBase_le_seed_ladder (rho : ℂ) :
    l1Mass (explicitPoweredHealthyBase rho) ≤
      ∑ z ∈ healthyUnscaledTargetNodes rho,
        ‖(1 : ℂ) /
            (nodeProduct (healthyUnscaledTargetNodes rho) z z *
              laplaceAt poweredSeed 0)‖ *
          (Real.exp (|z.re| * 10) *
            ladderBound (fun j => derivOrderL1 j poweredSeed)
              (((healthyUnscaledTargetNodes rho).erase z).toList.map
                (fun t => t - z)) 0) := by
  rw [explicitPoweredHealthyBase]
  exact l1Mass_correction_le_seed_ladder _ _ _ 10
    (poweredSeed_support_subset_Ioo.trans Set.Ioo_subset_Icc_self)

theorem l1Mass_explicitPoweredHealthyCorrection_le_seed_ladder
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) :
    l1Mass (explicitPoweredHealthyCorrection rho N routeNodes) ≤
      ∑ z ∈ healthyCorrectionNodes rho N routeNodes,
        ‖healthyCorrectionValue rho z /
            (nodeProduct (healthyCorrectionNodes rho N routeNodes) z z *
              laplaceAt poweredSeed 0)‖ *
          (Real.exp (|z.re| * 10) *
            ladderBound (fun j => derivOrderL1 j poweredSeed)
              (((healthyCorrectionNodes rho N routeNodes).erase z).toList.map
                (fun t => t - z)) 0) := by
  rw [explicitPoweredHealthyCorrection]
  exact l1Mass_correction_le_seed_ladder _ _ _ 10
    (poweredSeed_support_subset_Ioo.trans Set.Ioo_subset_Icc_self)

theorem selectedOwner_explicitPoweredHealthy_target (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) (n : ℕ)
    {w : FiniteMellinNode (healthyUnscaledTargetNodes rho)} :
    laplaceAt
        (selectedOwner (explicitPoweredHealthyBase rho)
          (explicitPoweredHealthyCorrection rho N routeNodes) n).sourceTest
        (w.1 - 1 / 2) = healthyUnscaledTargetValue rho w := by
  have h := selectedOwner_explicit_correction_target
    (explicitPoweredHealthyBase rho) poweredSeed
    (healthyCorrectionNodes rho N routeNodes)
    (healthyCorrectionValue rho) poweredSeed_laplaceAt_zero_ne_zero n
    (s := w.1) (Finset.mem_union_right _ w.2)
    (explicitPoweredHealthyBase_targets rho w)
  rw [selectedOwner_laplaceAt_sourceTest_centered,
    explicitPoweredHealthyCorrection]
  have hraw :
      laplaceAt
          ((convolutionIterate (explicitPoweredHealthyBase rho) n).convolution
            (correction (healthyCorrectionNodes rho N routeNodes) poweredSeed
              (healthyCorrectionValue rho))) w.1 =
        healthyCorrectionValue rho w.1 := by
    simpa only [selectedOwner_laplaceAt_sourceTest_centered] using h
  calc
    laplaceAt
          ((convolutionIterate (explicitPoweredHealthyBase rho) n).convolution
            (correction (healthyCorrectionNodes rho N routeNodes) poweredSeed
              (healthyCorrectionValue rho))) w.1 =
        healthyCorrectionValue rho w.1 := hraw
    _ = healthyUnscaledTargetValue rho w := by
      simp [healthyCorrectionValue, w.2]

theorem selectedOwner_explicitPoweredHealthy_kills (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) (n : ℕ)
    (z : FiniteMellinNode (healthyKillSet rho N routeNodes))
    (hz : z.1 ∉ healthyUnscaledTargetNodes rho) :
    laplaceAt
        (selectedOwner (explicitPoweredHealthyBase rho)
          (explicitPoweredHealthyCorrection rho N routeNodes) n).sourceTest
        (z.1 - 1 / 2) = 0 := by
  rw [selectedOwner_laplaceAt_sourceTest_centered, laplaceAt_convolution,
    laplaceAt_convolutionIterate]
  rw [explicitPoweredHealthyCorrection_kills rho N routeNodes z hz]
  simp

theorem explicitHealthyCorrection_targets (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ)
    (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt (explicitHealthyCorrection rho N routeNodes) w.1 =
      healthyUnscaledTargetValue rho w := by
  have hmem : w.1 ∈ healthyCorrectionNodes rho N routeNodes := by
    exact Finset.mem_union_right _ w.2
  rw [explicitHealthyCorrection]
  calc
    laplaceAt
          (correction (healthyCorrectionNodes rho N routeNodes) smoothSeed
            (healthyCorrectionValue rho)) w.1 =
        healthyCorrectionValue rho w.1 :=
      correction_interpolates _ smoothSeed smoothSeed_laplaceAt_zero_ne_zero
        (healthyCorrectionValue rho) hmem
    _ = healthyUnscaledTargetValue rho w := by
      simp [healthyCorrectionValue, w.2]

theorem explicitHealthyCorrection_kills (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ)
    (z : FiniteMellinNode (healthyKillSet rho N routeNodes))
    (hz : z.1 ∉ healthyUnscaledTargetNodes rho) :
    laplaceAt (explicitHealthyCorrection rho N routeNodes) z.1 = 0 := by
  have hmem : z.1 ∈ healthyCorrectionNodes rho N routeNodes := by
    exact Finset.mem_union_left _ z.2
  rw [explicitHealthyCorrection]
  calc
    laplaceAt
          (correction (healthyCorrectionNodes rho N routeNodes) smoothSeed
            (healthyCorrectionValue rho)) z.1 =
        healthyCorrectionValue rho z.1 :=
      correction_interpolates _ smoothSeed smoothSeed_laplaceAt_zero_ne_zero
        (healthyCorrectionValue rho) hmem
    _ = 0 := by simp [healthyCorrectionValue, hz]

theorem explicitHealthyCorrection_support (rho : ℂ) (N : ℕ)
    (routeNodes : Finset ℂ) :
    Function.support (explicitHealthyCorrection rho N routeNodes).test ⊆
      Set.Icc (-2) 2 := by
  exact correction_support _ smoothSeed _ smoothSeedComplex_support_subset

/-- The 1977 seed-ladder estimate specialized to the complete healthy owner.
Only derivative orders below the actual node count occur. -/
theorem l1Mass_explicitHealthyCorrection_le_budget
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (higher : ℕ → ℝ)
    (hhigh : ∀ j, 4 ≤ j →
      j < (healthyCorrectionNodes rho N routeNodes).card →
        derivOrderL1 j smoothSeed ≤ higher j) :
    l1Mass (explicitHealthyCorrection rho N routeNodes) ≤
      ∑ z ∈ healthyCorrectionNodes rho N routeNodes,
        ‖healthyCorrectionValue rho z /
            (nodeProduct (healthyCorrectionNodes rho N routeNodes) z z *
              laplaceAt smoothSeed 0)‖ *
          (Real.exp (|z.re| * 2) *
            ladderBound (smoothSeedBudget higher)
              (((healthyCorrectionNodes rho N routeNodes).erase z).toList.map
                (fun t => t - z)) 0) := by
  exact l1Mass_correction_smoothSeed_le_budget _ _ higher hhigh

end

end ConnesWeilRH.Source.C1ExplicitHealthyCorrectionBudget
