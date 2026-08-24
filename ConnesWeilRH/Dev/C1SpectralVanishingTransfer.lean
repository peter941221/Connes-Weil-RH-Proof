/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyTestSpace

/-!
# C1SpectralVanishingTransfer - the finite-node vanishing bridge

This is the honest W2 boundary for the healthy owner.  The finite vanishing
nodes `0`, `1 / 2`, and `1` are arithmetic pole nodes; they are not source
spectral zeros.  The useful consequence of the node at `1 / 2` is instead
that the Hermitian square has zero values at both pole evaluations.  The
proof keeps the `CC20TestSpace.mellinAt` slot, the compact-log `laplaceAt`
slot, and the positive-variable Mellin route tied to one owner.

No spectral zero is removed by this lemma, and no sign or RH statement is
claimed.  The remaining off-line spectral contribution is handled separately
by the W3 split.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralVanishingTransfer

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open C1HealthyYoshidaDetector
open C1LogPositiveBridge

noncomputable section

/-! ### One-owner coordinate readback -/

/-- The healthy `mellinAt` slot is exactly the compact-log Laplace value at the
same complex point. -/
theorem healthy_mellinAt_eq_laplaceAt
    (g : CompactLogTest) (s : Complex) :
    C1.healthyCC20TestSpace.mellinAt g s =
      CompactLogTest.laplaceAt g s :=
  C1.healthyMellinReadoff g s

/-- The positive-variable route Mellin value is the same owner value too. -/
theorem healthy_routeMellin_eq_laplaceAt
    (g : CompactLogTest) (s : Complex) :
    mellin (fun x : Real => C1.healthyCC20TestSpace.toRouteTest g x) s =
      CompactLogTest.laplaceAt g s := by
  rw [C1.healthyRouteMellinReadoff, C1.healthyMellinReadoff]

/-! ### W2: the half-node kills the square pole pair -/

/-- Vanishing at the finite node `1 / 2` transfers to the compact-log
Laplace coordinate without changing the test owner. -/
theorem laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hhalf : CriticalVanishingPoint.half ∈ F)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    CompactLogTest.laplaceAt g (1 / 2 : Complex) = 0 := by
  calc
    CompactLogTest.laplaceAt g (1 / 2 : Complex) =
        C1.healthyCC20TestSpace.mellinAt g
          (criticalVanishingPointValue CriticalVanishingPoint.half) := by
      rw [C1.healthyMellinReadoff]
      simp [criticalVanishingPointValue]
    _ = 0 := hvanishes CriticalVanishingPoint.half hhalf

/-- The same vanishing is visible in the positive-variable route Mellin
coordinate. -/
theorem route_mellinAt_half_eq_zero_of_vanishesOn_of_mem_half
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hhalf : CriticalVanishingPoint.half ∈ F)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    mellin (fun x : Real => C1.healthyCC20TestSpace.toRouteTest g x)
        (criticalVanishingPointValue CriticalVanishingPoint.half) = 0 := by
  rw [C1.healthyRouteMellinReadoff]
  exact laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half g hhalf hvanishes

/-- The Hermitian square vanishes at both pole evaluations once its root
vanishes at the right half-node. -/
theorem convolutionSquare_laplaceAt_polePair_eq_zero_of_vanishesOn_of_mem_half
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hhalf : CriticalVanishingPoint.half ∈ F)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    CompactLogTest.laplaceAt g.convolutionSquare (1 / 2 : Complex) = 0 /\
      CompactLogTest.laplaceAt g.convolutionSquare (-1 / 2 : Complex) = 0 := by
  have h := laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half g hhalf hvanishes
  constructor
  · rw [laplaceAt_convolutionSquare_half, h, mul_zero]
  · rw [laplaceAt_convolutionSquare_neg_half, h, star_zero, zero_mul]

/-- **W2 endpoint.**  On any finite vanishing set containing `1 / 2`, the
same-owner Weil square has no pole term and therefore consists exactly of the
negative archimedean and finite-prime contributions. -/
theorem qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_of_mem_half
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hhalf : CriticalVanishingPoint.half ∈ F)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare := by
  rw [C1SameOwnerWeil.qw_eq_psi_square,
    C1SameOwnerWeil.psi_eq_components,
    C1HealthyYoshidaDetector.poleTerm_convolutionSquare_of_laplaceAt_half_eq_zero
      g (laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half g hhalf hvanishes)]
  ring

/-! ### Axiom-cleanliness audit -/
#print axioms healthy_mellinAt_eq_laplaceAt
#print axioms healthy_routeMellin_eq_laplaceAt
#print axioms laplaceAt_half_eq_zero_of_vanishesOn_of_mem_half
#print axioms route_mellinAt_half_eq_zero_of_vanishesOn_of_mem_half
#print axioms convolutionSquare_laplaceAt_polePair_eq_zero_of_vanishesOn_of_mem_half
#print axioms qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_of_mem_half

end
end C1SpectralVanishingTransfer
end Source
end ConnesWeilRH
