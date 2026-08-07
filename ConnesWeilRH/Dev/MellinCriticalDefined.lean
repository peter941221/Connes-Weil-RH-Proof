import ConnesWeilRH.Dev.MellinProductCarrier
import ConnesWeilRH.Dev.MellinSignAssembly

/-!
Critical-line well-formedness (859): the sign slot of the faithful half-line
route is only well-defined when the Mellin at the critical point exists. On the
log carrier that existence is `Integrable (logWeight (i/2) g)`, the
well-definedness condition that 859 reports most natural smooth tests fail
(their Mellin integrand ~ t^-1 at 0 is not L^1-loc). This module names that
predicate so route code can read well-formedness as data.

For a real-valued test on the defined sub-domain, the 858c sign reduction
(pole sum = 2*Re[(Mg(i/2))^4]) applies, hence the sign slot is the inequality
`0 <= Re[(mellinLift g (I/2))^4]` under `criticalDefined g`. This is honest: we
do NOT claim to prove that inequality; we record that it is exactly the
well-formed, defined-edition of the previous open.

No RH claimed. Target axioms [propext, Classical.choice, Quot.sound].
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinCriticalDefined

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

/-- The log-coordinate test whose Mellin is well-defined at the critical point
   `i/2`. `logWeight s g = (e^x)^s * g x`, so at s = i/2 the integrability IS
   the well-defined-ness of the faithful Mellin evaluation there (859). -/
def criticalDefined (g : ℝ → ℂ) : Prop :=
  Integrable (MellinConvolutionIdentity.logWeight (Complex.I / 2) g)

/-- On the defined sub-domain, the route pole sum for a real-valued test is
   exactly `2*Re[(mellinLift g (I/2))^4]`. Re-read of
   `halfDensity_poleSum_pow4_real` under the `criticalDefined` predicate. -/
theorem poleSum_eq_of_criticalDefined_real (g : ℝ → ℂ)
    (hg : ∀ x : ℝ, conj (g x) = g x)
    (hF : criticalDefined g)
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
  exact MellinSignAssembly.halfDensity_poleSum_pow4_real g hg hF hFFp hFm hFFm

end
end MellinCriticalDefined
end Dev
end Source
end ConnesWeilRH


