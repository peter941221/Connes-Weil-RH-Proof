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

/-- The genuine half-density square factors through the SQUARED Mellin:
M(conv g g)(s) = (M g)^2. -/
theorem halfDensitySquareMellin_eq_mellin_sq (g : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (MellinConvolutionIdentity.logWeight s g)) :
    MellinProductCarrier.mellinLift (MellinProductCarrier.conv g g) s
      = (MellinProductCarrier.mellinLift g s) ^ 2 := by
  rw [MellinProductCarrier.mellinConvolutionProductLaw g g s hF hF]
  ring

/-- The route half-density pole sum reads the DOUBLE square; on the faithful carrier
that is the FOURTH power of the Mellin: M(conv(conv g g)(conv g g))(s) = (M g)^4.
This is the exact analytic shape the endpoint / half-density sign slot becomes: the
sign question reduces to a fourth-power sum at (+i/2) and (-i/2) (via 856/857), not the additive
2 * M g.  A complex fourth power still carries a phase, so this lemma alone does not
force nonnegativity; it certifies the correct multiplicative shape. -/
theorem halfDensityDoubleSquareMellin_eq_mellin_pow4 (g : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (MellinConvolutionIdentity.logWeight s g))
    (hFF : Integrable (MellinConvolutionIdentity.logWeight s
        (MellinProductCarrier.conv g g))) :
    MellinProductCarrier.mellinLift
        (MellinProductCarrier.conv (MellinProductCarrier.conv g g)
          (MellinProductCarrier.conv g g)) s
      = (MellinProductCarrier.mellinLift g s) ^ 4 := by
  rw [MellinProductCarrier.mellinConvolutionProductLaw
      (MellinProductCarrier.conv g g) (MellinProductCarrier.conv g g) s hFF hFF]
  rw [halfDensitySquareMellin_eq_mellin_sq g s hF]
  ring

end MellinHalfDensitySquare
end Dev
end Source
end ConnesWeilRH
