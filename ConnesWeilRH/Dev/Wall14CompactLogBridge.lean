import ConnesWeilRH.Dev.Wall14PlateauBumpHI
import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.CompactLogArchimedeanLift
import ConnesWeilRH.Dev.Wall14ArchReduction
import ConnesWeilRH.Dev.Wall14SelfTestWitness

/-!
# Wall14CompactLogBridge — lift the closed Wall-A 1.4 arch real part onto the
compact-log carrier, and pin the one genuinely-unbuilt object-layer seam to the
SCAL refutation target.

`Wall14PlateauBumpHI.bumpArchimedeanTerm_re_pos` closes the archimedean term of the
explicit big-plateau bump *as a `SelectedWeilSquareOwner`*:

    0 < (bumpPlateauOwner.archimedeanTerm).re              (BumpHI:651, axiom-clean)

`bumpPlateauOwner = SelectedWeilSquareOwner.ofCompactLogTest bumpPlateauTest`
(ExplicitComplex:132, rfl), so the real part is exactly
`compactLogArchimedeanTerm bumpPlateauTest`
(CompactLogArchimedeanLift:38).  That is the CCM25 Eq.3.7 term on the compact-log
carrier, which the healthy SCAL arch slot eventually reads
(`healthySymbols.archimedeanTerm (convolutionStar f f)`, WellFormHealthyRepoint).

This module closes the compact-log side axiom-clean and *pins* the one remaining
object-layer re-type (SCAL `convolutionStar` on `TestFunction = SchwartzMap` vs the
compact square) as an explicit socket to downstream `/ the SC target.  RH NOT claimed.

Sanity for the real-pointing one-liner: on the compact carrier the healthy arch
term is positive, so `2*arch + (a - b) = 0` (the SCB pair) cannot hold with the
definitive sign, which is exactly the healthy-carrier Wall-A 1.4 dead/not hinge.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14CompactLogBridge

open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.CompactLogArchimedeanLift

/-- The real Eq.3.7 archimedean term at the explicit big-plateau compact-log test
is strictly positive (the lead piece `C * A > 0` dominates the real part of the
archimedean integral).  Axiom-clean lift of `bumpArchimedeanTerm_re_pos`. -/
theorem compactLogArchimedean_bump_pos :
    0 < compactLogArchimedeanTerm Wall14Plateau.bumpPlateauTest := by
  unfold compactLogArchimedeanTerm
  exact Wall14Plateau.bumpArchimedeanTerm_re_pos

/-- The archimedean term at the plateau square is non-zero (equivalently,
`compactLogArchimedean_bump_pos` with sign).  Downstream a non-zero real arch
is all the healthy-SCB refutation needs. -/
theorem compactLogArchimedean_bump_ne_zero :
    compactLogArchimedeanTerm Wall14Plateau.bumpPlateauTest ≠ 0 := by
  exact ne_of_gt compactLogArchimedean_bump_pos

end Wall14CompactLogBridge
end Dev
end Source
end ConnesWeilRH