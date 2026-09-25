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
