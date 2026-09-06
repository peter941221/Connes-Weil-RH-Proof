import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

/-!
# P2 bilateral-profile same-detector exit

This leaf packages the direct profile-sign consumer with the healthy B5
contradiction.  The producer still has to construct the fields for the pinned
orbit detector; this file only fixes the owner and quantifier of that
obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BilateralProfileExit

open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1P2BilateralProfile
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

structure P2BilateralProfileSignWitness (g : CompactLogTest) where
  harch : archimedeanTerm g.convolutionSquare ≤ 0
  hprofile : ∀ n ∈ globalPrimeIndexSet g.convolutionSquare,
    (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0

theorem qw_nonneg_of_p2BilateralProfileSignWitness
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (p : P2BilateralProfileSignWitness g) :
    0 ≤ qw g := by
  exact qw_nonneg_of_archimedean_nonpos_and_visible_bilateralProfile_nonpos
    g hvanishes p.harch p.hprofile

theorem sourceRH_of_healthyDetector_p2BilateralProfileSignWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (P2BilateralProfileSignWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileSignWitness g hdata.vanishesOnF hp2⟩

end
end C1P2BilateralProfileExit
end Source
end ConnesWeilRH
