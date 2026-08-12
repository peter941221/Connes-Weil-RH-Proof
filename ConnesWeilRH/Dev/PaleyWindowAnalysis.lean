import ConnesWeilRH.Dev.PaleyHTAssembly
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

open MeasureTheory Set

namespace ConnesWeilRH
namespace Dev
namespace PaleyWindowAnalysis

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.PaleyWindow
open ConnesWeilRH.Dev.PaleyWindowHT
open ConnesWeilRH.Dev.SoninWindowWitness

/-!
# V_arch = simultaneous half-line annihilation (Dev, sub-target C setup)

From sub-target B, `u` lies in `V_arch` iff `u` is radial AND `HT u` is radial.
Unwinding each radial condition gives the concrete, testable form that the
sub-target C construction must satisfy: on every `t < log lambda` the value
`u t` is `0` AND the value `(HT u) t` is `0`.  Sub-target A already proves the
first branch for the window element; the whole remaining difficulty is the
second half-line annihilation of its Hardy-Titchmarsh image.
-/

theorem radial_mem_iff_ae {U : cc20GlobalLogCrossingL2} (l : CCM24SoninScale) :
    U ∈ ccm24LogRadialSupportClosedSubspace l ↔
      (∀ᵐ t ∂volume, t < Real.log l → U t = 0) :=
  mem_ccm24LogRadialSupportClosedSubspace_iff l U

theorem vArch_mem_iff_support_ae (l : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24ArchimedeanSoninClosedSubspace l ↔
      (∀ᵐ t ∂volume, t < Real.log l → u t = 0) ∧
      (∀ᵐ t ∂volume, t < Real.log l →
        (ccm24ArchimedeanHardyTitchmarsh u) t = 0) := by
  rw [archimedeanSonin_mem_radial_and_ht_radial]
  simp [mem_ccm24LogRadialSupportClosedSubspace_iff]

/-- Sub-target A already solves the first (radial) half-line branch. -/
theorem radial_half_solved (l : CCM24SoninScale) :
    (∀ᵐ t ∂volume, t < Real.log l → soninWindowIndicator l t = 0) := by
  rw [← radial_mem_iff_ae (U := soninWindowIndicator l) (l := l)]
  exact soninWindowIndicator_mem_radial l

/-- The honest OPEN C gate, typed: a nonzero element with BOTH half-lines
annihilated (hence a nonzero V_arch element) exists. -/
noncomputable def cOpenNontrivial (l : CCM24SoninScale) : Prop :=
  ∃ u : cc20GlobalLogCrossingL2, u ≠ 0 ∧
    u ∈ ccm24ArchimedeanSoninClosedSubspace l

end PaleyWindowAnalysis
end Dev
end ConnesWeilRH
