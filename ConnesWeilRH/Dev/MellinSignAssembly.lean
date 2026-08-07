import ConnesWeilRH.Dev.MellinHalfDensitySquare
import ConnesWeilRH.Dev.MellinConjugation
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import ConnesWeilRH.Basic

/-!
Faithful half-density sign assembly (858c): bind the 857/857b fourth-power shape
to the 858b critical-line reality, and reduce the faithful pole sum to a single
real statement.

On the faithful Mellin-product carrier the route half-density pole sum is

    Re[M(conv(conv g g)(conv g g))(+i/2)] + Re[M(conv(conv g g)(conv g g))(-i/2)]
                          = (M g i/2)^4 .re + (M g -i/2)^4 .re                  (857/857b)

For a real-valued test (`conj o g = g`) the reality lemma (`MellinConjugation`)
gives `M(g -i/2) = conj(M(g i/2))`, so the second fourth power is the conjugate
of the first and the whole sum collapses to `2 * Re[(M g (i/2))^4]`.

No RH is claimed; this certifies that the whole open sign slot is exactly the
single real statement `Re[(M g i/2)^4] >= 0`, an independent analytic input.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinSignAssembly

noncomputable section
open MellinProductCarrier
open MellinConjugation
open MeasureTheory
open scoped ComplexConjugate Topology

/-- The fourth power of a conjugate is the conjugate of the fourth power. -/
lemma pow4_conj (z : ℂ) : conj (z ^ 4) = (conj z) ^ 4 := by
  simp

/-- The faithful half-density pole sum at (+i/2) is the 4th power at +i/2. -/
theorem halfDensity_poleSum_top (g : ℝ → ℂ)
    (w : ℂ) (hw : w = MellinProductCarrier.mellinLift g (Complex.I / 2))
    (hF : Integrable (MellinConvolutionIdentity.logWeight (Complex.I / 2) g))
    (hFF : Integrable (MellinConvolutionIdentity.logWeight (Complex.I / 2)
        (MellinProductCarrier.conv g g))) :
    (MellinProductCarrier.mellinLift
        (MellinProductCarrier.conv (MellinProductCarrier.conv g g)
          (MellinProductCarrier.conv g g)) (Complex.I / 2)).re = (w ^ 4).re := by
  rw [MellinHalfDensitySquare.halfDensityDoubleSquareMellin_eq_mellin_pow4 g (Complex.I / 2) hF hFF]
  simp [hw]

/-- The faithful half-density pole sum reduces to `2 * Re[(M g i/2)^4]` for a
   real-valued test.  This is the single real frontier of the sign slot. -/
theorem halfDensity_poleSum_pow4_real (g : ℝ → ℂ)
    (hg : ∀ x : ℝ, conj (g x) = g x)
    (hFp : Integrable (MellinConvolutionIdentity.logWeight (Complex.I / 2) g))
    (hFFp : Integrable (MellinConvolutionIdentity.logWeight (Complex.I / 2)
        (MellinProductCarrier.conv g g)))
    (hFm : Integrable (MellinConvolutionIdentity.logWeight (- (Complex.I / 2)) g))
    (hFFm : Integrable (MellinConvolutionIdentity.logWeight (- (Complex.I / 2))
        (MellinProductCarrier.conv g g))) :
    ((MellinProductCarrier.mellinLift
        (MellinProductCarrier.conv (MellinProductCarrier.conv g g)
          (MellinProductCarrier.conv g g)) (Complex.I / 2)).re +
      (MellinProductCarrier.mellinLift
        (MellinProductCarrier.conv (MellinProductCarrier.conv g g)
          (MellinProductCarrier.conv g g)) (- (Complex.I / 2))).re) =
      2 * ((MellinProductCarrier.mellinLift g (Complex.I / 2)) ^ 4).re := by
  rw [MellinHalfDensitySquare.halfDensityDoubleSquareMellin_eq_mellin_pow4 g
      (Complex.I / 2) hFp hFFp]
  rw [MellinHalfDensitySquare.halfDensityDoubleSquareMellin_eq_mellin_pow4 g
      (- (Complex.I / 2)) hFm hFFm]
  have hw2 := MellinConjugation.mellinLift_real_involution g hg
  -- hw2 : M(-i/2) = conj (M(i/2))
  let w : ℂ := MellinProductCarrier.mellinLift g (Complex.I / 2)
  have hmin : ((MellinProductCarrier.mellinLift g (-(Complex.I / 2)) ^ 4)).re
        = (w ^ 4).re := by
    rw [show MellinProductCarrier.mellinLift g (-(Complex.I / 2)) = conj w by
      simpa [w] using hw2]
    conv_lhs => rw [← pow4_conj w]
    exact Complex.conj_re (w ^ 4)
  rw [hmin]
  ring

end
end MellinSignAssembly
end Dev
end Source
end ConnesWeilRH


