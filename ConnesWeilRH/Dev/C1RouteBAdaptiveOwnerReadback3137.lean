import ConnesWeilRH.Dev.C1RouteBAdaptiveSupportBridge3134

/-! Canonical Lean readback for the adaptive powered owner (record 3137).

These declarations do not enumerate a numerical manifest. They pin the owner
identity and the exact prime-power index-set definition that any future
certificate must match.
-/

namespace ConnesWeilRH.Source.C1RouteBAdaptiveOwnerReadback3137

open CC20YoshidaConvolution.CompactLogTest
open C1RouteBAdaptivePoweredTail3117
open C1SameOwnerWeil
open CCM25Concrete
open C1ExplicitHealthyCorrectionBudget
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.SelectedWeilSquare.SelectedFinitePrimeSupportData

noncomputable section

theorem poweredFamilyOwner_identity3137
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) :
    poweredFamilyOwner3117 rho N routeNodes n =
      (selectedOwner (explicitPoweredHealthyBase rho)
        (explicitPoweredHealthyCorrection rho N routeNodes) n).sourceTest := by
  rfl

theorem poweredFamily_globalPrimeIndexSet_mem_iff3137
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (n q : ℕ) :
    q ∈ globalPrimeIndexSet
        (poweredFamilyOwner3117 rho N routeNodes n).convolutionSquare ↔
      IsPrimePow q ∧
        finitePrimeTermComplex
          (poweredFamilyOwner3117 rho N routeNodes n).convolutionSquare q ≠ 0 := by
  exact mem_globalPrimeIndexSet_iff
    (poweredFamilyOwner3117 rho N routeNodes n).convolutionSquare q

theorem poweredFamily_globalPrimeIndexSet_selected3137
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) :
    globalPrimeIndexSet
        (poweredFamilyOwner3117 rho N routeNodes n).convolutionSquare =
      (SelectedFinitePrimeSupportData.ofOwner
        (SelectedWeilSquareOwner.ofCompactLogTest
          (poweredFamilyOwner3117 rho N routeNodes n))).globalPrimeIndexSet := by
  exact globalPrimeIndexSet_square_eq_selected
    (poweredFamilyOwner3117 rho N routeNodes n)

end
end ConnesWeilRH.Source.C1RouteBAdaptiveOwnerReadback3137
