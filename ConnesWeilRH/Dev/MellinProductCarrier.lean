/-
Mellin-product carrier (Route B / parallel source model): a **standalone
carrier** whose convolution genuinely multiplies under the Mellin transform.

The CC20 concrete additive model cannot satisfy
`NormalizedCC20MellinConvolutionLaw` (`CC20ConcreteTestSpace.lean:167`); the
counterexample `not_normalizedCC20MellinConvolutionLaw`
(`CC20YoshidaConstruction.lean:2727`) proves no in-model reassembly works.  The
decision record `docs/proofs/setup/design-parallel-source-model-consensus.md`
mandates a **new Mellin-product convolution** on a carrier that does *not*
require the total `LegacyTestEquiv.decode` (the A2 / Seam-B wall).

This module supplies that carrier.  A "test" is a complex-valued function on the
additive log coordinate (`ℝ → ℂ`, the `.logfun` slot; `CompactLogTest.test` is
one).  Its Mellin evaluation is the log-lift
`MellinAt f s = mellin (fun t => f (log t)) s`, and its convolution is the
log-additive convolution `(f ⋆ g) x = ∫_t f t · g (x - t)`.

The Mellin product law for this carrier is the identity already proved in
`MellinConvolutionIdentity.mellin_log_convolution_product`:

    mellin (fun z => (f ⋆ g) (log z)) s = mellin (fun t => f (log t)) s
                                          · mellin (fun t => g (log t)) s.

- Axiom-clean, no sorries.  Target axioms [propext, Classical.choice,
  Quot.sound].  Integrability premises are terminating witnesses, not axioms.
-/

import ConnesWeilRH.Dev.MellinConvolutionIdentity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinProductCarrier

noncomputable section
open MeasureTheory
open scoped Convolution Topology

/-- A log-coordinate test: a complex-valued function on the additive log axis. -/
structure Test where
  log : ℝ → ℂ

/-- The log-additive convolution, `(f ⋆ g) x = ∫_t f t · g (x - t)`.  This is the
`MeasureTheory.convolution` with scalar bilinear map `ContinuousLinearMap.mul` -/
noncomputable def conv (f g : ℝ → ℂ) : ℝ → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g

/-- Mellin evaluation in the log coordinate: `mellin (fun t => f (log t)) s`.
(Kept under a distinct name to avoid shadowing mathlib's `mellin`.) -/
noncomputable def mellinLift (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => f (Real.log t)) s

/-- The Mellin product law of this carrier.  It is literally the theorem
`MellinConvolutionIdentity.mellin_log_convolution_product`, with the
integrability premises kept as terminating convergence witnesses. -/
theorem mellinConvolutionProductLaw (f g : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (MellinConvolutionIdentity.logWeight s f))
    (hG : Integrable (MellinConvolutionIdentity.logWeight s g)) :
    mellinLift (conv f g) s = mellinLift f s * mellinLift g s := by
  simpa [mellinLift, conv] using
    MellinConvolutionIdentity.mellin_log_convolution_product
      (F := f) (G := g) (s := s) hF hG

end
end MellinProductCarrier
end Dev
end Source
end ConnesWeilRH