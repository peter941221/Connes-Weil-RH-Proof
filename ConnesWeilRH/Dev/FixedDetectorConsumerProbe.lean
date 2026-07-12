/- Minimal fixed-detector consumer probe; deliberately avoids broad packages. -/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact

namespace ConnesWeilRH
namespace Source
namespace Dev

open CCM25Concrete

structure FixedDetectorWeilData
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ) where
  square : TestFunction
  square_eq : square = W.convolutionStar f f
  exactSupport : FinitePrimeExact.ExactSupportAtLambda W f f lambda
  qwDefinition : W.qw f f = W.psi square
  qwLambdaFormula :
    W.qwLambda lambda f f =
      W.archimedeanTerm square + W.polePairing f -
        ∑ n ∈ W.restrictedPrimeIndexSet lambda,
          W.vonMangoldtWeight n * W.primePowerPairing n f f
  poleNormalization :
    W.polePairing f = W.poleFunctional square

theorem fixedDetector_qw_reads_square
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : FixedDetectorWeilData W f lambda) :
    W.qw f f = W.psi (W.convolutionStar f f) := by
  rw [h.qwDefinition, h.square_eq]

theorem fixedDetector_qwLambda_reads_square
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : FixedDetectorWeilData W f lambda) :
    W.qwLambda lambda f f =
      W.archimedeanTerm (W.convolutionStar f f) + W.polePairing f -
        ∑ n ∈ W.restrictedPrimeIndexSet lambda,
          W.vonMangoldtWeight n * W.primePowerPairing n f f := by
  rw [h.qwLambdaFormula, h.square_eq]

theorem fixedDetector_has_local_prime_support
    {W : WeilFormSymbols} {f : TestFunction} {lambda : ℝ}
    (h : FixedDetectorWeilData W f lambda) :
    FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement W f f lambda :=
  FinitePrimeExact.visibility_at_lambda_of_exact_support h.exactSupport

end Dev
end Source
end ConnesWeilRH
