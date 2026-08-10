
/-
Healthy source-test algebra: a SourceTestAlgebra on the full `TestFunction`
(Schwartz) carrier whose convolution is the TRUE Mellin/Analytic product
`SchwartzMap.convolution`, NOT the broken additive `f + g` unfolding.

Why this matters (route root):
  The concrete algebra `concreteTestAlgebra` (AnalyticCoreBase) set
  `convolutionStar f g = f + g`, which is ADDITIVE rather than
  multiplicative-Mellin.  With additive convolution, `mellin(f * g)` has no
  product law and `qwLambda`-style identities break (see the closure-audit
  doc and the 2=1 contradiction
  `CC20YoshidaConstruction.not_normalizedCC20MellinConvolutionLaw`).  The
  healthy carrier is the true convolution on Schwartz maps: mathlib's
  `SchwartzMap.convolution` satisfies the Fourier product law
  `𝓕(f * g) = 𝓕(f) * 𝓕(g)`
  (`SchwartzMap.fourier_convolution`), the multiplicative-Mellin property,
  and coincides with ordinary convolution on the dense Schwartz subspace
  (`SchwartzMap.convolution_apply`).

  This module builds a `SourceTestAlgebra` on the SAME carrier `TestFunction`
  (= `ConcreteTest` = `SchwartzMap ℝ ℂ`) using `Test := TestFunction`
  and the identity `LegacyTestEquiv`, so it drops into the skeleton consumer
  without a type change; only the broken additive product is replaced by the
  Mellin one.

  RH NOT claimed: this only fixes the source algebra product on a healthy
  carrier.  The finite-S sign / fullWeilPositivity discharge remains open.
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

/-- The true convolution star on `TestFunction` = `SchwartzMap ℝ ℂ`. -/
noncomputable def healthyConvolutionStar
    (f g : TestFunction) : TestFunction :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) f g

/-- The Fourier (reflection/adjoint) involution on the carrier. -/
noncomputable def healthyInvolution
    (f : TestFunction) : TestFunction :=
  𝓕 f

/-- The convolution square is the Mellin product of the test with itself. -/
noncomputable def healthyConvolutionSquare
    (g : TestFunction) : TestFunction :=
  healthyConvolutionStar g g

/-- The healthy source test algebra: identity legacy, true Mellin convolution.
-/
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

/-- The Fourier transform of the healthy convolution is the pointwise product
of Fourier transforms - the multiplicative-Mellin law the additive model
violates. -/
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
