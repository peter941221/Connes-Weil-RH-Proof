import ConnesWeilRH.Dev.Wall14ArchReduction
import ConnesWeilRH.Dev.A3NonzeroCompactLogGateProbe
import ConnesWeilRH.Dev.ScabLhsZero

/-!
# Wall14SelfTestWitness

Self-created, explicitly-computable witness for the Wall-A 1.4 healthy-carrier
refutation hinge.  The healthy SCAL reduction and refutation-hinge theorems range
over ANY `f : TestFunction` (`TestFunction = SchwartzMap Real Complex`).  We
instantiate them at the explicit mathlib bump
`A3NonzeroCompactLogGateProbe.nonzeroTest.test` (smooth, even, compact,
`test(0) = 1 != 0`), so the `arch(f*f) != 0` hypothesis is now ONE scalar at a
concrete, computable test rather than at the route's `Classical.choose` bump.

This module does NOT yet close the archimedean integral inequality; it pins the
dead/not verdict to that single explicit scalar and registers the concrete
counterexample shape.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14SelfTestWitness

open ConnesWeilRH.Source.Dev.A3NonzeroCompactLogGateProbe
open ConnesWeilRH.Source.CCM25Concrete.ScabNormalForm

/-- The self-constructed explicit test: the real smooth compact bump at 0,
   viewed as a `TestFunction` (= `SchwartzMap ℝ ℂ`), equal to 1 at 0. -/
noncomputable abbrev witnessTest : TestFunction :=
  ConnesWeilRH.Source.Dev.A3NonzeroCompactLogGateProbe.nonzeroTest.test

/-- The witness is a genuine non-zero `TestFunction` (value `1` at `0`). -/
theorem witnessTest_ne_zero : Not (witnessTest = 0) := by
  unfold witnessTest
  exact ConnesWeilRH.Source.Dev.A3NonzeroCompactLogGateProbe.nonzeroTest_test_ne_zero

/-- The healthy-cursor symbols of the Wall-A 1.4 reduction. -/
noncomputable abbrev healthySymbols :=
  ConnesWeilRH.Source.Dev.ScabLhsZero.healthySymbols

/-- Refutation hinge pinned to the self-created witness: if the archimedean term
   at the witness square is not zero, the healthy Wall-A 1.4 target is refuted. -/
theorem witness_refuted_of_arch_ne_zero
    (globalSum restrictedSum : Real)
    (hsum : globalSum = restrictedSum)
    (harch : Not (healthySymbols.archimedeanTerm
        (healthySymbols.convolutionStar witnessTest witnessTest) = 0)) :
    Not (ScabPoleArchTarget healthySymbols witnessTest globalSum restrictedSum) := by
  exact ConnesWeilRH.Source.CCM25Concrete.healthy_target_refuted_of_arch_ne_zero
    witnessTest globalSum restrictedSum hsum harch

end Wall14SelfTestWitness
end Dev
end Source
end ConnesWeilRH