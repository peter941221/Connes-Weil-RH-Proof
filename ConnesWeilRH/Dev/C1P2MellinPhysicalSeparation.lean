import ConnesWeilRH.Dev.C1P2PhysicalMellinInterpolation

/-!
# Mellin/physical separation

The finite Mellin interpolation interface does not determine a physical
prime-log sample.  This is a no-go for any proposed producer that tries to
derive the visible-prime profile from Mellin node values alone.

The result is deliberately owner-local and carries no sign or RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2MellinPhysicalSeparation

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaUnscaledOrbit
open C1P2PhysicalMellinInterpolation

noncomputable section

/-- Finite Mellin data can be zero while a prescribed positive physical
coordinate is nonzero. Hence Mellin data alone do not determine that sample.
-/
theorem exists_zero_finiteMellin_data_nonzero_physical_value
    (nodes : Finset Complex) {x : Real} (hx : 0 < x) :
    ∃ g : CompactLogTest,
      (∀ z : FiniteMellinNode nodes, laplaceAt g z.1 = 0) ∧
        g.test x = 1 := by
  obtain ⟨g, _hsupport, hgMellin, hgx⟩ :=
    exists_physicalPoint_mellinInterpolation nodes hx
      (fun _ => 0)
  refine ⟨g, ?_, ?_⟩
  · intro z
    simpa using hgMellin z
  · rw [hgx]

end
end C1P2MellinPhysicalSeparation
end Source
end ConnesWeilRH
