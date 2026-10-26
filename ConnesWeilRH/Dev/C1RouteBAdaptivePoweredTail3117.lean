import ConnesWeilRH.Dev.C1RouteBQuadraticPinGapCost3116
import ConnesWeilRH.Dev.C1HealthyYoshidaClosedPrefix
import ConnesWeilRH.Dev.C1FourPointContradictionAssembly

/-! Adaptive tails for the actual powered-seed family.

Choose the base threshold, complete zero prefix and correction before the
convolution count. Its finite quadratic constant is allowed to depend on rho
and the complete prefix; it is never replaced by its necessary lower cost.
A positive lower bound on the later span coefficient suffices for eventual
strict negativity of the same span's Weil value. No gate is supplied.
-/

namespace ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117

open CC20YoshidaConvolution CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1ExplicitSmoothSeed C1ExplicitFiniteNodeCorrection C1ExplicitHealthyCorrectionBudget
open C1HealthyYoshidaUnscaledOrbit C1HealthyYoshidaClosedPrefix
open C1HealthyYoshidaDetector C1HealthyYoshidaMinimalInterpolation
open C1FourPointSpectralPrefixTransport C1FourPointHighShellTail
open C1FourPointContradictionAssembly C1SpectralWeil C1SpectralTailBound
open C1HealthyYoshidaSpectralNegativity C1TwoPointSpectralDecomposition
open C1RouteBQuadraticPinGapCost3116 C1LaneRD3Root
open scoped BigOperators

noncomputable section

def poweredFamilyOwner3117 (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) : CompactLogTest :=
  (selectedOwner (explicitPoweredHealthyBase rho)
    (explicitPoweredHealthyCorrection rho N routeNodes) n).sourceTest

def poweredFamilySpan3117 (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (lambda : ℝ) : CompactLogTest :=
  annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator (poweredFamilyOwner3117 rho N routeNodes n) rho)
    (poweredFamilyOwner3117 rho N routeNodes n) lambda

theorem poweredFamily_target3117 (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt (poweredFamilyOwner3117 rho N routeNodes n) (w.1 - 1 / 2) =
      healthyUnscaledTargetValue rho w :=
  selectedOwner_explicitPoweredHealthy_target rho N routeNodes n (w := w)

theorem poweredFamily_raw_targets3117 (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (w : FiniteMellinNode (healthyUnscaledTargetNodes rho)) :
    laplaceAt ((convolutionIterate (explicitPoweredHealthyBase rho) n).convolution
      (explicitPoweredHealthyCorrection rho N routeNodes)) w.1 =
        healthyUnscaledTargetValue rho w := by
  rw [← selectedOwner_laplaceAt_sourceTest_centered]
  exact poweredFamily_target3117 rho N routeNodes n w

theorem poweredFamily_raw_kills3117 (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (w : FiniteMellinNode (healthyKillSet rho N routeNodes))
    (hw : w.1 ∉ healthyUnscaledTargetNodes rho) :
    laplaceAt ((convolutionIterate (explicitPoweredHealthyBase rho) n).convolution
      (explicitPoweredHealthyCorrection rho N routeNodes)) w.1 = 0 := by
  rw [laplaceAt_convolution, explicitPoweredHealthyCorrection_kills rho N routeNodes w hw]
  simp

theorem poweredFamily_prefix_square_zero3117
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) :
    ∀ z : sourceNontrivialZeroSet, z ∈ spectralHeightShellPrefix (N + 1) →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (poweredFamilyOwner3117 rho.1 N routeNodes n).convolutionSquare
          (z.1 - 1 / 2) = 0 := by
  intro z hz hnotOrbit
  have hball := mem_closedBall_about_anchor_of_mem_finiteHeightZeros rho.1
    ((2 : ℝ) ^ (N + 1)) z
    ((spectralHeightShellPrefix_subset_finiteHeightZeros (N + 1)) hz)
  have hmem : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
      ((2 : ℝ) ^ (N + 1) + 2 + dist (2 : ℂ) rho.1) ∪ routeNodes :=
    Finset.mem_union_left _ (mem_sourceNontrivialZerosInClosedBallFinset.mpr ⟨hball, z.2⟩)
  exact selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_closedBall_not_mem_orbit
    (explicitPoweredHealthyBase rho.1) (explicitPoweredHealthyCorrection rho.1 N routeNodes)
    n rho.1 rho.2 (ne_of_gt hright) hright routeNodes _
    (poweredFamily_raw_targets3117 rho.1 N routeNodes n)
    (poweredFamily_raw_kills3117 rho.1 N routeNodes n) z hmem hnotOrbit

theorem poweredFamily_span_prefix3117
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) (lambda : ℝ)
    (hheight : 2 * |rho.1.im| ≤ (2 : ℝ) ^ (N + 1)) :
    (∑ k ∈ Finset.range (N + 1), ∑' z : spectralHeightShell k,
      spectralTerm (poweredFamilySpan3117 rho.1 N routeNodes n lambda).convolutionSquare
        z.1).re ≤ -(xiMultiplicity rho : ℝ) * lambda ^ 2 := by
  have hstrict : |rho.1.im| < (2 : ℝ) ^ (N + 1) := by
    have hp := pow_pos (by norm_num : (0 : ℝ) < 2) (N + 1)
    have ha := abs_nonneg rho.1.im
    linarith
  have hidx : dyadicShellIndex |rho.1.im| ≤ N :=
    Nat.find_min' (exists_lt_two_pow_succ |rho.1.im|) hstrict
  have hrho : rho ∈ spectralHeightShellPrefix (N + 1) :=
    (mem_spectralHeightShellPrefix_iff (N + 1) rho).mpr (by omega)
  have horbit (w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1)) :
      laplaceAt (poweredFamilyOwner3117 rho.1 N routeNodes n) (w.1 - 1 / 2) =
        negativeSourceOrbitValue rho.1 w :=
    (poweredFamily_target3117 rho.1 N routeNodes n
      ⟨w.1, Finset.mem_union_left _ w.2⟩).trans
        (healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2)
  have h := finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
    (poweredFamilyOwner3117 rho.1 N routeNodes n) rho lambda
    (spectralHeightShellPrefix (N + 1)) hrho (ne_of_gt hright) horbit
    (poweredFamily_prefix_square_zero3117 rho hright N routeNodes n)
  rw [← sum_spectralHeightShellPrefix_eq_shell_prefix]
  exact h

theorem poweredFamily_cc20_vanishes3117
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (poweredFamilyOwner3117 rho.1 N routeNodes n) := by
  intro p _hp
  change laplaceAt (poweredFamilyOwner3117 rho.1 N routeNodes n)
    (criticalVanishingPointValue p) = 0
  cases p
  · have h := poweredFamily_target3117 rho.1 N routeNodes n
      ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩
    rw [show (1 / 2 : ℂ) - 1 / 2 = 0 by ring] at h
    exact h.trans (healthyUnscaledTargetValue_half rho.2 (ne_of_gt hright))
  · have h := poweredFamily_target3117 rho.1 N routeNodes n
      ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩
    rw [show (1 : ℂ) - 1 / 2 = (1 / 2 : ℂ) by ring] at h
    exact h.trans (healthyUnscaledTargetValue_one rho.2 (ne_of_gt hright))
  · have h := poweredFamily_target3117 rho.1 N routeNodes n
      ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩
    rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by ring] at h
    exact h.trans (healthyUnscaledTargetValue_threeHalf rho.2)

/-- Uniform relative tail smallness for coefficients bounded below, with no
upper bound on the coefficient. The actual family theorem consumes this. -/
theorem exists_eventual_relative_tail_budget3117
    (rho : ℂ) (C4 C2 ell : ℝ) (hell : 0 < ell) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ lambda : ℝ, ell ≤ lambda →
      (3 + ‖rho‖) ^ 4 * ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
        (2 * Real.pi) ^ 12 * (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2) < lambda ^ 2 := by
  let H : ℝ := (3 + ‖rho‖) ^ 4
  let A : ℝ := H * (1 + H / ell) ^ 2 * (2 * Real.pi) ^ 12
  have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq := hpow.mul hpow
  have hscaled : Filter.Tendsto
      (fun n : ℕ => A * (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2))
      Filter.atTop (nhds 0) := by
    have h := hsq.mul_const (A * (C4 * C2) ^ 2)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    (hscaled.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨n0, ?_⟩
  intro n hn lambda hlower
  have hlam : 0 < lambda := hell.trans_le hlower
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hratio : 1 + H / lambda ≤ 1 + H / ell :=
    add_le_add (le_refl 1) (div_le_div_of_nonneg_left hH hell hlower)
  have hcoeff : (1 + H / lambda) ^ 2 ≤ (1 + H / ell) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hratio 2
  have hnormal : H * (1 + H / lambda) ^ 2 * (2 * Real.pi) ^ 12 *
      (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2) < 1 := by
    refine lt_of_le_of_lt ?_ (hn0 n hn)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff hH)
        (by positivity)) (sq_nonneg _)
  change H * (H + |lambda|) ^ 2 * (2 * Real.pi) ^ 12 *
    (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2) < lambda ^ 2
  calc
    _ = lambda ^ 2 * (H * (1 + H / lambda) ^ 2 * (2 * Real.pi) ^ 12 *
        (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2)) := by
      rw [abs_of_pos hlam]
      field_simp [hlam.ne']
      ring
    _ < lambda ^ 2 * 1 := mul_lt_mul_of_pos_left hnormal (sq_pos_of_pos hlam)
    _ = lambda ^ 2 := mul_one _

/-- The actual rho-dependent family has an eventual negative span for every
coefficient above ell. Its genuine quadratic upper bound and the necessary
3116 cost are retained together. No numerical pins or gate sign are inputs. -/
theorem exists_eventual_powered_span_qw_neg3117
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (routeNodes : Finset ℂ) (ell : ℝ) (hell : 0 < ell) :
    ∃ N : ℕ, ∃ C2 : ℝ, ∃ n0 : ℕ,
      0 ≤ C2 ∧
      quadraticStripPin3116
        (laplaceAt (explicitPoweredHealthyCorrection rho.1 N routeNodes)) C2 ∧
      (1 ≤ |rho.1.im| → |rho.1.re - 1 / 2| ≤ 1 / 16 →
        rho.1.im ^ 2 ≤ (16 * ((2 * Real.pi) ^ 2 * C2) + 4 * rho.1.im ^ 2) *
          |rho.1.re - 1 / 2|) ∧
      ∀ n : ℕ, n0 ≤ n →
        CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
          (poweredFamilyOwner3117 rho.1 N routeNodes n) ∧
        ∀ lambda : ℝ, ell ≤ lambda →
          C1SameOwnerWeil.qw (poweredFamilySpan3117 rho.1 N routeNodes n lambda) < 0 := by
  let base := explicitPoweredHealthyBase rho.1
  obtain ⟨Cb2, hCb2, hbase2⟩ := exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay base
  obtain ⟨T, hTnonneg, hcontract⟩ :=
    exists_laplaceAt_vertical_half_contraction_of_quadratic_bound base Cb2 hCb2 hbase2
  obtain ⟨N, hT, hheight, hsmall⟩ :=
    exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T (1 : ℝ) rho
  let correction := explicitPoweredHealthyCorrection rho.1 N routeNodes
  obtain ⟨C4, hC4, hbase4⟩ := exists_uniform_compactLog_laplaceAt_vertical_quartic_decay base
  obtain ⟨C2, hC2, hcorrection2⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay correction
  obtain ⟨n0, hn0⟩ := exists_eventual_relative_tail_budget3117 rho.1 C4 C2 ell hell
  refine ⟨N, C2, n0, hC2, hcorrection2, ?_, ?_⟩
  · intro him hgap
    exact powered_correction_pin_gap_cost3116 rho.1 N routeNodes C2
      (ne_of_gt hright) hgap him hcorrection2
  · intro n hn
    refine ⟨poweredFamily_cc20_vanishes3117 rho hright N routeNodes n, ?_⟩
    intro lambda hlower
    have hlam : 0 < lambda := hell.trans_le hlower
    have hbudget : (3 + ‖rho.1‖) ^ 4 *
        ((3 + ‖rho.1‖) ^ 4 + |lambda|) ^ 2 * (2 * Real.pi) ^ 12 *
        (((1 / 2 : ℝ) ^ n * (C4 * C2)) ^ 2) < (lambda * 1) ^ 2 := by
      simpa only [mul_one] using hn0 n hn lambda hlower
    have htail := selectedOwner_fullOrbit_span_fourthOrderSpectralTail
      base correction rho.1 lambda C4 C2 T (lambda * 1) n hC4 hC2
      hcontract hbase4 hcorrection2 hbudget
    exact qw_neg_of_spectralHeightShellPrefix_and_coefficient_scaled_tail
      (poweredFamilySpan3117 rho.1 N routeNodes n lambda) rho T 1 lambda htail
      N hT hheight hlam (poweredFamily_span_prefix3117 rho hright N routeNodes n lambda hheight)
      hsmall

end
end ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117
