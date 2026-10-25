import ConnesWeilRH.Dev.C1RouteBPoweredSeedOwnerFacts3111
import ConnesWeilRH.Dev.C1RouteBPrefixOwnerTransport3108
import ConnesWeilRH.Dev.C1RowBPrefixTransport2723

/-! Same-owner row-B prefix transport for the explicit powered-seed owner (3114).

The 3111 owner facts already provide the healthy target interpolation and
closed-ball square-zero transport.  This module instantiates the existing
row-B prefix theorem on that exact owner, using `N >= 5` to place the height-64
prefix inside the powered correction's closed-ball radius.  It removes a
prefix premise for this owner; it does not prove cardinal pins or `hgate24`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBPoweredSeedOwnerPrefix3114

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaClosedPrefix
open C1RouteBPoweredSeedOwnerFacts3111
open C1ExplicitHealthyCorrectionBudget
open C1RouteBPrefixOwnerTransport3108
open C1RowBPrefixTransport2723
open C1FourPointSpectralPrefixTransport
open C1HealthyYoshidaSpectralNegativity
open C1TwoPointSpectralDecomposition
open C1FourPointRowBWired2721
open C1SpectralWeil
open scoped BigOperators

noncomputable section

theorem poweredSeedExplicitOwner_targetOrbit3114
    (rho : sourceNontrivialZeroSet) (N : ℕ) (routeNodes : Finset ℂ)
    (w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1)) :
    laplaceAt (poweredSeedExplicitOwner3111 rho.1 N routeNodes)
        (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w := by
  have htarget := poweredSeedExplicitOwner_target3111 rho.1 N routeNodes
    (⟨w.1, Finset.mem_union_left _ w.2⟩ :
      FiniteMellinNode (healthyUnscaledTargetNodes rho.1))
  have hvalue :
      healthyUnscaledTargetValue rho.1
          ⟨w.1, Finset.mem_union_left _ w.2⟩ =
        negativeSourceOrbitValue rho.1 w :=
    healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2
  exact htarget.trans hvalue

theorem poweredSeedExplicitOwner_prefixSquareZero3114
    (rho : sourceNontrivialZeroSet) (N : ℕ) (routeNodes : Finset ℂ)
    (hN : 5 ≤ N)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : ℝ) < rho.1.re) :
    ∀ z : sourceNontrivialZeroSet,
      z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
      laplaceAt
          (poweredSeedExplicitOwner3111 rho.1 N routeNodes).convolutionSquare
          (z.1 - 1 / 2) = 0 := by
  intro z hzPrefix hnotOrbit
  have hzFinite : z ∈ finiteHeightZeros ((2 : ℝ) ^ 6) := by
    exact (spectralHeightShellPrefix_subset_finiteHeightZeros 6) hzPrefix
  have hball64 := mem_closedBall_about_anchor_of_mem_finiteHeightZeros
    rho.1 ((2 : ℝ) ^ 6) z hzFinite
  have hpow : (64 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    have hpow' : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (N + 1) := by
      apply pow_right_mono₀
      · norm_num
      · omega
    norm_num at hpow'
    exact hpow'
  have hball : z.1 ∈ Metric.closedBall rho.1
      ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho.1) := by
    apply Metric.mem_closedBall.mpr
    have hball64' := Metric.mem_closedBall.mp hball64
    norm_num at hball64'
    linarith
  have hballFinset : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
      ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho.1) :=
    mem_sourceNontrivialZerosInClosedBallFinset.mpr ⟨hball, z.2⟩
  have hmem : z.1 ∈
      sourceNontrivialZerosInClosedBallFinset rho.1
          ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho.1) ∪ routeNodes :=
    Finset.mem_union_left _ hballFinset
  have htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt
            ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
              (explicitPoweredHealthyCorrection rho.1 N routeNodes)) w.1 =
          healthyUnscaledTargetValue rho.1 w := by
    intro w
    have hselected := selectedOwner_explicitPoweredHealthy_target
      rho.1 N routeNodes 3 (w := w)
    calc
      laplaceAt
          ((convolutionIterate (explicitPoweredHealthyBase rho.1) 3).convolution
            (explicitPoweredHealthyCorrection rho.1 N routeNodes)) w.1 =
          laplaceAt
            (selectedOwner (explicitPoweredHealthyBase rho.1)
              (explicitPoweredHealthyCorrection rho.1 N routeNodes) 3).sourceTest
            (w.1 - 1 / 2) := by
        symm
        exact selectedOwner_laplaceAt_sourceTest_centered
          (explicitPoweredHealthyBase rho.1)
          (explicitPoweredHealthyCorrection rho.1 N routeNodes) 3 w.1
      _ = healthyUnscaledTargetValue rho.1 w := hselected
  by_cases htarget : z.1 ∈ healthyUnscaledTargetNodes rho.1
  · have hz0 := selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_target_not_mem_orbit
      (explicitPoweredHealthyBase rho.1)
      (explicitPoweredHealthyCorrection rho.1 N routeNodes)
      3 rho.1 rho.2 hoff hright htargetValues z htarget hnotOrbit
    simpa [poweredSeedExplicitOwner3111] using hz0
  · have hz0 := poweredSeedExplicitOwner_square_zero3111 rho.1 N routeNodes
      ⟨z.1, hmem⟩ htarget
    simpa using hz0

theorem poweredSeedExplicitOwner_rowBSpanPrefix3114
    (rho : sourceNontrivialZeroSet) (N : ℕ) (routeNodes : Finset ℂ)
    (hN : 5 ≤ N)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : ℝ) < rho.1.re)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721) :
    (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (poweredSeedExplicitOwner3111 rho.1 N routeNodes) rho.1)
            (poweredSeedExplicitOwner3111 rho.1 N routeNodes) 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : ℝ) * 24 ^ 2) := by
  exact rowBSpanPrefix_of_imCap_2723
    (poweredSeedExplicitOwner3111 rho.1 N routeNodes)
    rho hoff hIm
    (poweredSeedExplicitOwner_targetOrbit3114 rho N routeNodes)
    (poweredSeedExplicitOwner_prefixSquareZero3114 rho N routeNodes hN hoff hright)

end
end C1RouteBPoweredSeedOwnerPrefix3114
end Source
end ConnesWeilRH
