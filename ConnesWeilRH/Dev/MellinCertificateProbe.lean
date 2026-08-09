/-
Mellin-carrier free-standing finite-prime certificate probe (A-lane).

L657's slot `CommonFinitePrimeArithmeticSourceData W` needs `W : WeilFormSymbols`
whose fields sit on `TestFunction`; the Mellin carrier (`Test = ℝ → ℂ`) cannot
fill it without the dead `decode` wall.  This probe records the two honest,
axiom-clean facts the Mellin route actually contributes:

1. the multiplicative square-law `Mellin (f ⋆ f) = Mellin f · Mellin f` — a
   corollary of `MellinProductCarrier.mellinConvolutionProductLaw`;
2. the per-point von-Mangoldt weight at the prime `2` is positive
   (Λ(2) = log 2 > 0) — the seed a finite-prime certificate needs.

No RH claim.  Zero `sorry`.  No new `axiom`.
-/

import ConnesWeilRH.Dev.MellinProductCarrier
import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe
import Mathlib.Analysis.MellinTransform

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinCertificateProbe

open MeasureTheory
open scoped Convolution Topology

noncomputable section

/-- The Mellin square-law, restated on the carrier (the product law with
`g := f`).  Axiom-clean by construction. -/
theorem mellin_squareLaw (f : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (MellinConvolutionIdentity.logWeight s f)) :
    MellinProductCarrier.mellinLift (MellinProductCarrier.conv f f) s =
      (MellinProductCarrier.mellinLift f s) * (MellinProductCarrier.mellinLift f s) := by
  exact MellinProductCarrier.mellinConvolutionProductLaw f f s hF hF

#print axioms mellin_squareLaw

/-- Prime `2` has a positive von Mangoldt weight, Λ(2) = log 2 > 0. -/
lemma vonMangoldt_two_pos : 0 < ArithmeticFunction.vonMangoldt 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Real.log_pos (by norm_num)

#print axioms vonMangoldt_two_pos

end
end MellinCertificateProbe
end Dev
end Source
end ConnesWeilRH