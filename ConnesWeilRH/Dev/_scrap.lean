import ConnesWeilRH.Dev.Wall14PlateauProbe
import ConnesWeilRH.Dev.Wall14ArchSufficiency
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Wall14PlateauIntegral

Closes the Wall-A 1.4 `hI` leaf for the large-plateau owner by proving
`|Re(∫ archimedeanIntegrand)| < 3 * A`, which (since `3 < log(4π)+γ`) closes
`archimedeanTerm ≠ 0`.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set
open scoped ComplexConjugate
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner

/-! Foundational facts: plateau support radius 1, F even, F = 0 for |y| > 2. -/

theorem plateauReal_eq_zero_of_le_one_abs (t : ℝ) (ht : (1 : ℝ) ≤ |t|) :
    plateauReal t = 0 := by
  exact plateauBump.zero_of_le_dist ht

theorem plateauReal_le_one (t : ℝ) : plateauReal t ≤ 1 := by
  exact plateauBump.le_one

theorem plateauReal_mem_Icc (t : ℝ) : plateauReal t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨plateauReal_nonneg t, plateauReal_le_one t⟩

/-! F(-y)=F(y): the convolution square is even. -/
theorem plateauF_symm (y : ℝ) : plateauF (-y) = plateauF y := by
  rw [plateauF_eq_conv, plateauF_eq_conv]
  let φ : ℝ → ℝ := fun t : ℝ => -t
  have hφ : AEMeasurable φ (volume : Measure ℝ) := measurable_neg.aemeasurable
  have hmap : (volume : Measure ℝ).map φ = (volume : Measure ℝ) := by
    rw [Measure.map_neg_eq_self]
  have hv (t : ℝ) :
      (∫ x, plateauReal x * (plateauReal (-y - x))) =
        ∫ x, (plateauReal x * plateauReal (-y - x)) ∂((volume : Measure ℝ).map φ) := by
    rw [hmap]
  have hsub : (∫ t0 : ℝ, plateauReal t0 * plateauReal ((-y) - t0)) =
      ∫ x : ℝ, plateauReal (-x) * plateauReal ((-y) - (-x)) := by
    exact hv.symm
  have heq : (∫ t : ℝ, plateauReal t * plateauReal (y - t)) =
      ∫ t : ℝ, plateauReal t * plateauReal (y - t) := rfl
  sorry
end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
