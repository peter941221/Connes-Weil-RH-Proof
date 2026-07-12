/- Minimal research probe for the ambient Schwartz source owner. -/

import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.AnalyticCoreBase
import Mathlib.Analysis.Fourier.Convolution

namespace ConnesWeilRH
namespace Source
namespace Dev

open scoped FourierTransform SchwartzMap

abbrev AmbientTest := SchwartzMap ℝ ℂ

noncomputable def ambientLegacy :
    AnalyticCore.LegacyTestEquiv TestFunction where
  encode := id
  decode := id
  encode_decode := by intro F; rfl
  decode_encode := by intro f; rfl

noncomputable def ambientConvolution (f g : AmbientTest) : AmbientTest :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g

noncomputable def ambientInvolution (f : AmbientTest) : AmbientTest :=
  (f.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ (E := ℝ))).postcompCLM
    Complex.conjCLE.toContinuousLinearMap

noncomputable def ambientSourceAlgebra : AnalyticCore.SourceTestAlgebra where
  Test := TestFunction
  legacy := ambientLegacy
  convolutionStar := ambientConvolution
  involution := ambientInvolution
  convolutionSquare := fun g => ambientConvolution g g
  convolutionSquare_eq := by intro g; rfl

theorem ambientConvolution_fourier (f g : AmbientTest) :
    𝓕 (ambientConvolution f g) =
      (fun x => (𝓕 f x) * (𝓕 g x)) := by
  rw [ambientConvolution, SchwartzMap.fourier_convolution]
  rfl

theorem ambientConvolution_eq_compactLogConvolution
    (f g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    ambientConvolution f.test g.test = (f.convolution g).test := by
  ext x
  rw [ambientConvolution, SchwartzMap.convolution_apply,
    CCM25Concrete.CompactLogConvolution.CompactLogTest.convolution_apply,
    MeasureTheory.convolution_def]
  rfl

theorem ambientCarrier_is_complex_vector_space :
    IsScalarTower ℂ ℂ AmbientTest := by infer_instance

end Dev
end Source
end ConnesWeilRH
