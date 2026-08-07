import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Dev.MellinProductCarrier
import ConnesWeilRH.Source.CC20Concrete.GlobalLogHaar
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Basic

/-!
# Mellin-product law merged onto the Hilbert carrier (852 merge)

The multiplicative half-density Mellin law, stated on the Hilbert log carrier
cc20GlobalLogCrossingL2, instead of the additive-model convention.  The product
law itself is already proved axiom-clean in MellinConvolutionIdentity; this
module lifts it onto the Hilbert carrier via the Lp coefficient representation.
No RH is claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinHilbertCarrierMerge

noncomputable def hilbertCarrier := ConnesWeilRH.Source.CC20Concrete.cc20GlobalLogCrossingL2

def mellinLawPremise (f : hilbertCarrier) (s : ℂ) : Prop :=
  MeasureTheory.Integrable
    (MellinConvolutionIdentity.logWeight s (f : ℝ → ℂ)) MeasureTheory.volume

def mellinHalfDensityStatement (f g : hilbertCarrier) (s : ℂ) : Prop :=
  mellinLawPremise f s ∧ mellinLawPremise g s ∧
    MellinProductCarrier.mellinLift
        (MellinProductCarrier.conv (f : ℝ → ℂ) (g : ℝ → ℂ)) s
      = MellinProductCarrier.mellinLift (f : ℝ → ℂ) s *
          MellinProductCarrier.mellinLift (g : ℝ → ℂ) s

/-- The honest half-density law holds by the already-proven product law. -/
theorem mellinHalfDensityProven (f g : hilbertCarrier) (s : ℂ) :
    mellinLawPremise f s → mellinLawPremise g s →
      mellinHalfDensityStatement f g s := by
  intro hF hG
  unfold mellinHalfDensityStatement mellinLawPremise
  exact ⟨hF, hG,
    MellinProductCarrier.mellinConvolutionProductLaw
      (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) (s := s) hF hG⟩

end MellinHilbertCarrierMerge
end Dev
end Source
end ConnesWeilRH
