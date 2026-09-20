import ConnesWeilRH.Dev.C1P2PhysicalPointBump
import ConnesWeilRH.Dev.C1HealthyDetectorEvenOddPair

/-!
# Physical point interpolation with finite Mellin constraints

This leaf combines the genuine physical point bump with the existing
same-owner residual-window correction.  It proves that a prescribed physical
sample can be retained while arbitrary finite Laplace data are imposed.  It
is an interpolation interface only: it does not prove health, a signed
budget, or semi-local positivity.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2PhysicalMellinInterpolation

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1HealthyDetectorArchRescue
open C1HealthyDetectorEvenOddPair
open C1P2PhysicalPointBump

noncomputable section

theorem exists_physicalPoint_mellinInterpolation
    (nodes : Finset Complex) {x : Real} (hx : 0 < x)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ g : CompactLogTest,
      Function.support g.test ⊆ Set.Icc (-x / 4) (3 * x / 2) ∧
        (∀ z : FiniteMellinNode nodes,
          laplaceAt g z.1 = y z) ∧
        g.test x = 1 := by
  have hleft : -x / 4 < 0 := by linarith
  have hright : 0 < x / 4 := by linarith
  obtain ⟨p, hpSupport, hpValue⟩ :=
    exists_compactLogTest_supported_Icc_eq_one
      (a := x / 2) (b := 3 * x / 2) (x := x)
      (by linarith) (by linarith)
  let target : FiniteMellinNode nodes → Complex := fun z =>
    y z - laplaceAt p z.1
  obtain ⟨c, hcSupport, hcValues⟩ :=
    exists_residualWindow_correction nodes hleft hright target
  let g : CompactLogTest := sumTest p c
  have hcx : c.test x = 0 := by
    by_contra hne
    have hxSupport : x ∈ Function.support c.test :=
      Function.mem_support.mpr hne
    have hxWindow := hcSupport hxSupport
    rcases hxWindow with ⟨hxLower, hxUpper⟩
    linarith
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u hu
    rcases support_sumTest_subset p c hu with hp | hc
    · have hwindow := hpSupport hp
      rcases hwindow with ⟨hLower, hUpper⟩
      exact ⟨by linarith, by linarith⟩
    · have hwindow := hcSupport hc
      rcases hwindow with ⟨hLower, hUpper⟩
      exact ⟨by linarith, by linarith⟩
  · intro z
    dsimp [g]
    rw [laplaceAt_sumTest, hcValues]
    dsimp [target]
    ring
  · dsimp [g]
    simp [hpValue, hcx]

end
end C1P2PhysicalMellinInterpolation
end Source
end ConnesWeilRH
