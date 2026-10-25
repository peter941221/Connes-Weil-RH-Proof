import ConnesWeilRH.Dev.C1RouteBPoweredSeedCarrier3110
import ConnesWeilRH.Dev.C1RouteBLowRungPoweredSeedEnvelope3112
import ConnesWeilRH.Dev.C1ExplicitSmoothSeed
import ConnesWeilRH.Dev.C1TwoPointSpectralDecomposition

/-! Envelope-to-pin bridge for the powered-seed carrier (3113).

The low-rung envelope is an upper bound on the actual cardinal sum.  This
module exposes the exact three envelope inequalities that would discharge the
powered-seed carrier's three wired pins, and transports them into the existing
same-owner contradiction.  It leaves those envelope inequalities as the
remaining quantified numerical certificate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBPoweredSeedEnvelopePinBridge3113

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1RouteBPoweredSeedCarrier3110
open C1RouteBLowRungPoweredSeedEnvelope3112
open C1ExplicitSmoothSeed
open C1StripTransport2722C
open C1OrbitWindowSemiLocalGate
open C1LocalConfigurationDomination
open C1FourPointSpectralPrefixTransport
open C1TwoPointSpectralDecomposition
open C1SpectralWeil
open C1FourPointRowBWired2721
open C1RowBCardinalCarrier2722D
open scoped BigOperators

noncomputable section

theorem fourPointContradictionRowBPoweredSeed_of_lowRungEnvelopePins3113
    (targets nodes : Finset ℂ) (hsub : targets ⊆ nodes)
    (htri : shiftedCC20Triple2722D ⊆ targets)
    (y : ℂ → ℂ)
    (hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0)
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hcontractEnv : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      64 ≤ |t| →
        lowRungPoweredSeedEnvelope3112 targets (fun _ => 1) sigma t ≤
          wiredQRowB2721)
    (hquarticEnv : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
          lowRungPoweredSeedEnvelope3112 targets (fun _ => 1) sigma t ≤
        wiredC4RowB2721)
    (hquadraticEnv : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
          lowRungPoweredSeedEnvelope3112 nodes y sigma t ≤
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
  apply fourPointContradictionRowBPoweredSeed3110 targets nodes hsub htri y hy rho
    hNorm hIm
  · intro sigma hsigma t ht
    exact (norm_cardinalSum_poweredSeed_le_lowRung_env3112 targets (fun _ => 1)
      hsigma).trans (hcontractEnv sigma hsigma t ht)
  · intro sigma hsigma t
    calc
      ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖cardinalSum targets poweredSeed (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          ‖t / (2 * Real.pi)‖ ^ 4 *
            lowRungPoweredSeedEnvelope3112 targets (fun _ => 1) sigma t :=
        mul_le_mul_of_nonneg_left
          (norm_cardinalSum_poweredSeed_le_lowRung_env3112 targets (fun _ => 1)
            hsigma) (by positivity)
      _ ≤ wiredC4RowB2721 := hquarticEnv sigma hsigma t
  · intro sigma hsigma t
    calc
      ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖cardinalSum nodes poweredSeed y
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          ‖t / (2 * Real.pi)‖ ^ 2 *
            lowRungPoweredSeedEnvelope3112 nodes y sigma t :=
        mul_le_mul_of_nonneg_left
          (norm_cardinalSum_poweredSeed_le_lowRung_env3112 nodes y hsigma)
          (by positivity)
      _ ≤ wiredC2RowB2721 := hquadraticEnv sigma hsigma t
  · exact hgate24
  · exact hprefix

end
end C1RouteBPoweredSeedEnvelopePinBridge3113
end Source
end ConnesWeilRH
