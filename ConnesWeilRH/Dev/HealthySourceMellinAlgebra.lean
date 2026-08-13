
/-
Experimental Schwartz convolution algebra on the full `TestFunction` carrier.

The concrete algebra `concreteTestAlgebra` uses `f + g`. This module instead
uses ordinary additive convolution, for which mathlib proves the Fourier law
  `𝓕(f * g) = 𝓕(f) * 𝓕(g)`
(`SchwartzMap.fourier_convolution`).

A Fourier product law is not a Mellin product law on the same input coordinate.
The correct CCM25 owner first passes to the logarithmic coordinate and uses
`CompactLogTest.involution.convolution`; see `C1SameOwnerWeil`. The Fourier
transform below is also not the CCM25 involution `f*(x) = conj (f(-x))`.
Therefore this module is an experimental carrier and must not be used as a
same-owner RH readout without an explicit coordinate bridge.

RH NOT claimed.
-/
import ConnesWeilRH.Basic
import ConnesWeilRH.Source.AnalyticCoreBase
import Mathlib.Analysis.Fourier.Convolution

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace HealthySourceMellinAlgebra

open AnalyticCore

open scoped FourierTransform

/-- Identity bridge: `TestFunction` as its own legacy carrier.  `encode =
decode = id` is a full bijection, so this is a valid `LegacyTestEquiv` on the
full Schwartz space. -/
noncomputable def healthyLegacyTestEquiv :
    LegacyTestEquiv TestFunction where
  encode := id
  decode := id
  encode_decode := by
    intro F
    rfl
  decode_encode := by
    intro f
    rfl

/-- Ordinary additive convolution on `TestFunction = SchwartzMap ℝ ℂ`. -/
noncomputable def healthyConvolutionStar
    (f g : TestFunction) : TestFunction :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) f g

/-- Fourier transform used by this experimental algebra. It is not the CCM25
logarithmic involution. -/
noncomputable def healthyInvolution
    (f : TestFunction) : TestFunction :=
  𝓕 f

/-- Experimental self-convolution; not the CCM25 half-density square. -/
noncomputable def healthyConvolutionSquare
    (g : TestFunction) : TestFunction :=
  healthyConvolutionStar g g

/-- Experimental source algebra: identity legacy and additive convolution. -/
noncomputable def healthyMellinSourceTestAlgebra :
    SourceTestAlgebra where
  Test := TestFunction
  legacy := healthyLegacyTestEquiv
  convolutionStar := healthyConvolutionStar
  involution := healthyInvolution
  convolutionSquare := healthyConvolutionSquare
  convolutionSquare_eq := by
    intro g
    rfl

/-- Fourier transform of additive convolution is pointwise multiplication.
This theorem makes no Mellin-coordinate claim. -/
theorem healthyFourierConvolutionMul
    (f g : TestFunction) :
    𝓕 (healthyConvolutionStar f g) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) (𝓕 f) (𝓕 g) := by
  unfold healthyConvolutionStar
  simp [SchwartzMap.fourier_convolution]

end HealthySourceMellinAlgebra
end Dev
end Source
end ConnesWeilRH
