import ConnesWeilRH.Dev.C1RowBStoredCapture2722F
import ConnesWeilRH.Dev.C1ExplicitSmoothSeed

/-! Route-B powered-seed carrier (record 3110).

Record 2724 rejected the old `explicitSeed` identification for the wired
cardinal pins.  This module keeps the same finite node data and target values,
but rebuilds the carrier with the actual Lean `poweredSeed`.  It proves the
transport-side facts on that owner: interpolation, the three CC20 vanishing
conditions, support, and the wired contradiction interface with powered-seed
cardinal pin premises.

The numeric pins, fixed-24 gate, and spectral prefix remain explicit inputs.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBPoweredSeedCarrier3110

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1ArchimedeanIntegrabilityGeneric
open C1CenterTwoCriterionBridge
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SpectralTailBound
open C1SpectralSummability
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open C1FourPointHighShellTail
open C1FourPointSpanGateCertificate
open C1SignedVarianceIdentity
open C1BipartiteMeanGapCertificate
open C1FourPointContradictionAssembly
open C1FourPointRowBWired2721
open C1ExplicitFiniteNodeCorrection
open C1ExplicitSmoothSeed
open C1RowBCardinalCarrier2722D
open C1RowBStoredCapture2722F
open C1StripTransport2722C
open scoped BigOperators

noncomputable section

def poweredSeedCarrierSourceTest3110 (targets nodes : Finset ℂ)
    (y : ℂ → ℂ) : CompactLogTest :=
  (selectedOwner
    (cardinalOwner targets poweredSeed (fun _ => 1))
    (cardinalOwner nodes poweredSeed y) 3).sourceTest

theorem poweredSeedCarrier_target3110
    {targets nodes : Finset ℂ} (hsub : targets ⊆ nodes)
    (y : ℂ → ℂ) {s : ℂ} (hs : s ∈ targets) :
    laplaceAt (poweredSeedCarrierSourceTest3110 targets nodes y)
      (s - 1 / 2) = y s := by
  unfold poweredSeedCarrierSourceTest3110 cardinalOwner
  apply selectedOwner_explicit_correction_target
    (correction targets poweredSeed (fun _ => 1)) poweredSeed nodes y
    poweredSeed_laplaceAt_zero_ne_zero 3 (hsub hs)
  exact correction_interpolates targets poweredSeed
    poweredSeed_laplaceAt_zero_ne_zero (fun _ => 1) hs

theorem poweredSeedCarrier_cc20Vanishes3110
    {targets nodes : Finset ℂ} (hsub : targets ⊆ nodes)
    (htri : shiftedCC20Triple2722D ⊆ targets)
    (y : ℂ → ℂ)
    (hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (poweredSeedCarrierSourceTest3110 targets nodes y) := by
  intro p _hp
  change CompactLogTest.laplaceAt
      (poweredSeedCarrierSourceTest3110 targets nodes y)
      (criticalVanishingPointValue p) = 0
  cases p
  · have hT := poweredSeedCarrier_target3110 hsub y
      (htri (by simp [shiftedCC20Triple2722D] : (1 / 2 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((1 / 2 : ℂ) - 1 / 2) = (0 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))
  · have hT := poweredSeedCarrier_target3110 hsub y
      (htri (by simp [shiftedCC20Triple2722D] : (1 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((1 : ℂ) - 1 / 2 : ℂ) = (1 / 2 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))
  · have hT := poweredSeedCarrier_target3110 hsub y
      (htri (by simp [shiftedCC20Triple2722D] : (3 / 2 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((3 / 2 : ℂ) - 1 / 2 : ℂ) = (1 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))

theorem poweredSeedCarrier_sourceTest_support3110
    (targets nodes : Finset ℂ) (y : ℂ → ℂ) :
    Function.support (poweredSeedCarrierSourceTest3110 targets nodes y).test ⊆
      Set.Ioo (-55 : ℝ) 55 := by
  have hseed : Function.support poweredSeed.test ⊆ Set.Icc (-10 : ℝ) 10 :=
    poweredSeed_support_subset_Ioo.trans Set.Ioo_subset_Icc_self
  have hbaseS : Function.support
      (cardinalOwner targets poweredSeed (fun _ => 1)).test ⊆
      Set.Ioo (-11 : ℝ) 11 := by
    have hcorr := correction_support targets poweredSeed (fun _ => 1) hseed
    intro x hx
    have hx' := hcorr hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hcorrS : Function.support
      (cardinalOwner nodes poweredSeed y).test ⊆ Set.Ioo (-11 : ℝ) 11 := by
    have hcorr := correction_support nodes poweredSeed y hseed
    intro x hx
    have hx' := hcorr hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hconv := convolutionIterate_convolution_support_subset_Ioo
    (cardinalOwner targets poweredSeed (fun _ => 1))
    (cardinalOwner nodes poweredSeed y) hbaseS hcorrS 3
  have hcast : ((3 + 1 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  rw [hcast] at hconv
  have hradius : Function.support
      ((convolutionIterate
        (cardinalOwner targets poweredSeed (fun _ => 1)) 3).convolution
        (cardinalOwner nodes poweredSeed y)).test ⊆ Set.Ioo (-55 : ℝ) 55 := by
    convert hconv using 1 <;> norm_num
  simpa only [poweredSeedCarrierSourceTest3110, selectedOwner_sourceTest] using
    halfDensityShift_support_subset
      ((convolutionIterate
        (cardinalOwner targets poweredSeed (fun _ => 1)) 3).convolution
        (cardinalOwner nodes poweredSeed y)) hradius

theorem fourPointContradictionRowBPoweredSeed3110
    (targets nodes : Finset ℂ) (hsub : targets ⊆ nodes)
    (htri : shiftedCC20Triple2722D ⊆ targets)
    (y : ℂ → ℂ)
    (hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0)
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        64 ≤ |t| →
          ‖cardinalSum targets poweredSeed (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721)
    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖cardinalSum targets poweredSeed (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721)
    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖cardinalSum nodes poweredSeed y
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
    (poweredSeedCarrierSourceTest3110 targets nodes y) rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          (poweredSeedCarrierSourceTest3110 targets nodes y) rho.1).involution.convolution
            (poweredSeedCarrierSourceTest3110 targets nodes y)) +
        ICgate ((poweredSeedCarrierSourceTest3110 targets nodes y).involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            (poweredSeedCarrierSourceTest3110 targets nodes y) rho.1))) +
      24 ^ 2 * ICgate
        ((poweredSeedCarrierSourceTest3110 targets nodes y).convolutionSquare) ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (poweredSeedCarrierSourceTest3110 targets nodes y) rho.1)
            (poweredSeedCarrierSourceTest3110 targets nodes y) 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False := by
  refine fourPointContradictionRowBWired2722C
    targets nodes poweredSeed (fun _ => 1) y
    (cardinalOwner targets poweredSeed (fun _ => 1))
    (cardinalOwner nodes poweredSeed y) rho (B := 55)
    hNorm hIm
    (poweredSeedCarrier_cc20Vanishes3110 hsub htri y hy)
    (poweredSeedCarrier_sourceTest_support3110 targets nodes y)
    rfl rfl ?_ ?_ ?_ hgate24 hprefix
  · intro sigma hsigma t ht
    exact hcontractPin sigma hsigma t ht
  · intro sigma hsigma t
    exact hquarticPin sigma hsigma t
  · intro sigma hsigma t
    exact hquadraticPin sigma hsigma t

def poweredSeedStoredCarrierSourceTest3110 : CompactLogTest :=
  poweredSeedCarrierSourceTest3110 storedTargets2722F storedNodes2722F storedY2722F

theorem fourPointContradictionRowBPoweredSeedStored3110
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        64 ≤ |t| →
          ‖cardinalSum storedTargets2722F poweredSeed (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredQRowB2721)
    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖cardinalSum storedTargets2722F poweredSeed (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721)
    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖cardinalSum storedNodes2722F poweredSeed storedY2722F
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
          poweredSeedStoredCarrierSourceTest3110 rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          poweredSeedStoredCarrierSourceTest3110 rho.1).involution.convolution
            poweredSeedStoredCarrierSourceTest3110) +
        ICgate (poweredSeedStoredCarrierSourceTest3110.involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            poweredSeedStoredCarrierSourceTest3110 rho.1))) +
      24 ^ 2 * ICgate poweredSeedStoredCarrierSourceTest3110.convolutionSquare ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              poweredSeedStoredCarrierSourceTest3110 rho.1)
            poweredSeedStoredCarrierSourceTest3110 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False := by
  apply fourPointContradictionRowBPoweredSeed3110
    (targets := storedTargets2722F) (nodes := storedNodes2722F)
    (y := storedY2722F) storedTargetsSubset2722F storedTripleSubset2722F
    storedYVanishes2722F rho hNorm hIm hcontractPin hquarticPin hquadraticPin
  · simpa [poweredSeedStoredCarrierSourceTest3110] using hgate24
  · simpa [poweredSeedStoredCarrierSourceTest3110] using hprefix

end
end C1RouteBPoweredSeedCarrier3110
end Source
end ConnesWeilRH
