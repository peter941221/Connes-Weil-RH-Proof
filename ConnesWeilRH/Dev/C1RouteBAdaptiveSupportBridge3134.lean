import ConnesWeilRH.Dev.C1RouteBAdaptivePoweredTail3117
import ConnesWeilRH.Dev.C1RouteBVariableLambdaGate3130

/-! The actual support bridge for the adaptive powered family (record 3134).
This keeps the 3117 powered owner as the owner throughout. -/

namespace ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1ExplicitHealthyCorrectionBudget
open C1FourPointSpectralPrefixTransport
open C1OrbitWindowSemiLocalGate
open C1RouteBAdaptivePoweredTail3117
open C1RouteBQuadraticPinGapCost3116
open C1RouteBVariableLambdaGate3130
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition

noncomputable section

theorem poweredFamilyOwner_support3134
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) :
    Function.support (poweredFamilyOwner3117 rho N routeNodes n).test ⊆
      Set.Ioo (-(((n + 1 : ℕ) : ℝ) * 11 + 11))
        (((n + 1 : ℕ) : ℝ) * 11 + 11) := by
  let base := explicitPoweredHealthyBase rho
  let correction := explicitPoweredHealthyCorrection rho N routeNodes
  have hbase : Function.support base.test ⊆ Set.Ioo (-11 : ℝ) 11 := by
    intro x hx
    have hx' := explicitPoweredHealthyBase_support rho hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hcorrection : Function.support correction.test ⊆ Set.Ioo (-11 : ℝ) 11 := by
    intro x hx
    have hx' := explicitPoweredHealthyCorrection_support rho N routeNodes hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hraw := convolutionIterate_convolution_support_subset_Ioo
    base correction hbase hcorrection n
  have hselected := halfDensityShift_support_subset
    ((convolutionIterate base n).convolution correction) hraw
  rw [poweredFamilyOwner3117, selectedOwner_sourceTest]
  intro x hx
  have hx' := hselected hx
  constructor <;> linarith [hx'.1, hx'.2]

set_option maxHeartbeats 800000 in
-- The generic gate normalization unfolds the full owner/span support algebra.
theorem poweredFamily_gate_bridge3134
    (rho : sourceNontrivialZeroSet) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (lambda : ℝ) :
    variableLambdaGatePredicate3130 rho
        (poweredFamilyOwner3117 rho.1 N routeNodes n) lambda ↔
      orbitWindowSemiLocalGate
        (poweredFamilySpan3117 rho.1 N routeNodes n lambda) := by
  let B : ℝ := ((n + 1 : ℕ) : ℝ) * 11 + 11
  exact variableLambdaGatePredicate3130_iff_owner_gate_of_support
    (poweredFamilyOwner3117 rho.1 N routeNodes n) lambda B
    (by simpa [B] using poweredFamilyOwner_support3134 rho.1 N routeNodes n)

theorem negative_powered_owner_rejects_gate3134
    (rho : sourceNontrivialZeroSet) (N : ℕ) (routeNodes : Finset ℂ)
    (n : ℕ) (lambda : ℝ)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet
      (poweredFamilySpan3117 rho.1 N routeNodes n lambda))
    (hneg : C1SameOwnerWeil.qw
      (poweredFamilySpan3117 rho.1 N routeNodes n lambda) < 0) :
    ¬ variableLambdaGatePredicate3130 rho
        (poweredFamilyOwner3117 rho.1 N routeNodes n) lambda := by
  intro hpred
  have hgate : orbitWindowSemiLocalGate
      (poweredFamilySpan3117 rho.1 N routeNodes n lambda) :=
    (poweredFamily_gate_bridge3134 rho N routeNodes n lambda).mp hpred
  have hqwnonneg : 0 ≤ C1SameOwnerWeil.qw
      (poweredFamilySpan3117 rho.1 N routeNodes n lambda) :=
    qw_nonneg_of_orbitWindowSemiLocalGate _ hvanishes hgate
  exact (not_lt_of_ge hqwnonneg) hneg

/-/ The 3117 eventual negative-span construction now reaches the gate
    interface without changing its owner or importing numerical data. -/
theorem exists_eventual_powered_owner_rejects_gate3135
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
          C1SameOwnerWeil.qw (poweredFamilySpan3117 rho.1 N routeNodes n lambda) < 0 ∧
          ¬ variableLambdaGatePredicate3130 rho
            (poweredFamilyOwner3117 rho.1 N routeNodes n) lambda := by
  obtain ⟨N, C2, n0, hC2, hpin, hstrip, hfamily⟩ :=
    exists_eventual_powered_span_qw_neg3117 rho hright routeNodes ell hell
  refine ⟨N, C2, n0, hC2, hpin, hstrip, ?_⟩
  intro n hn
  obtain ⟨hvanishes, hnegative⟩ := hfamily n hn
  have hannihilator := fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple
    (poweredFamilyOwner3117 rho.1 N routeNodes n) rho.1 hvanishes
  refine ⟨hvanishes, ?_⟩
  intro lambda hlambda
  have hspanvanishes := annihilatorDetectorSpanVector_vanishesOn_cc20Triple
    (fullFunctionalEquationOrbitAnnihilator
      (poweredFamilyOwner3117 rho.1 N routeNodes n) rho.1)
    (poweredFamilyOwner3117 rho.1 N routeNodes n) lambda hannihilator hvanishes
  exact ⟨hnegative lambda hlambda,
    negative_powered_owner_rejects_gate3134 rho N routeNodes n lambda
      hspanvanishes (hnegative lambda hlambda)⟩

end
end ConnesWeilRH.Source.C1RouteBAdaptiveSupportBridge3134
