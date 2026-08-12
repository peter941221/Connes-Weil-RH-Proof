import ConnesWeilRH.Dev.PaleyWindowProbe
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

open MeasureTheory Set

namespace ConnesWeilRH
namespace Dev
namespace PaleyWindowHT

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.PaleyWindow
open ConnesWeilRH.Dev.SoninWindowWitness

/-!
# Hardy-Titchmarsh isometry assembly (Dev, sub-target B)

Builds the well-defined nonzero L2 image of the radial window element under
the archimedean Hardy-Titchmarsh isometry (docs/paley_wiener/01, sub-target B),
and records the exact typed reduction that IS sub-target C: a nonzero u lies
in V_arch = Radial INTER HT^-1(Radial) iff u is radial AND HT(u) is radial.
-/

/-- The (well-defined) Hardy-Titchmarsh image of the radial window element. -/
noncomputable def htOfWindow (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 :=
  ccm24ArchimedeanHardyTitchmarsh (soninWindowIndicator lambda)

/-- Target B: HT is an injective isometry, so the radial window element is
carried to a well-defined nonzero L2 element. -/
theorem htOfWindow_ne_zero (lambda : CCM24SoninScale) :
    htOfWindow lambda ≠ 0 := by
  intro hzero
  have hz0 : soninWindowIndicator lambda = 0 := by
    have hs := congrArg (ccm24ArchimedeanHardyTitchmarsh.symm) hzero
    simpa [htOfWindow] using hs
  exact soninWindowIndicator_ne_zero lambda hz0

/-- Target C contract: V_arch membership is exactly `u radial` AND `(HT u) radial`. -/
theorem archimedeanSonin_mem_radial_and_ht_radial
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24ArchimedeanSoninClosedSubspace lambda ↔
      (u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
        ccm24ArchimedeanHardyTitchmarsh u ∈
          ccm24LogRadialSupportClosedSubspace lambda) := by
  change u ∈
      (ccm24LogRadialSupportClosedSubspace lambda ⊓
        ccm24ArchimedeanFourierSupportClosedSubspace lambda) ↔
      (u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
        ccm24ArchimedeanHardyTitchmarsh u ∈
          ccm24LogRadialSupportClosedSubspace lambda)
  simp [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]

end PaleyWindowHT
end Dev
end ConnesWeilRH
