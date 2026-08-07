import ConnesWeilRH.Dev.MellinProductCarrier
import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Basic

/-! Faithful half-density square (857): Mellin(conv g g)(s) = (Mellin g)(s)^2. Axiom-clean. -/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinHalfDensitySquare

open MellinProductCarrier
open MellinConvolutionIdentity
open MeasureTheory

theorem halfDensitySquareMellin_eq_mellin_sq (g : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (MellinConvolutionIdentity.logWeight s g)) :
    MellinProductCarrier.mellinLift (MellinProductCarrier.conv g g) s
      = (MellinProductCarrier.mellinLift g s) ^ 2 := by
  rw [MellinProductCarrier.mellinConvolutionProductLaw g g s hF hF]
  ring

end MellinHalfDensitySquare
end Dev
end Source
end ConnesWeilRH
