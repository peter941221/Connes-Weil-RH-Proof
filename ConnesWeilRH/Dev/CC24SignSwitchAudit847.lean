import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.CC20TestSpace
import ConnesWeilRH.Source.CC20RHExit
import ConnesWeilRH.Route.CC20RouteRealization
import ConnesWeilRH.Route.Exhaustion

/-!
# 847 audit: the "sign switch" is NOT a flip — the C1 positivity input and the
detector-positive object have SUBJECT/OBJECT + quantifier + inequality double mismatch.

This file pins, with `#check`, that:
  * `CC20FiniteVanishingWeilCriterion` is a UNIVERSAL `≤ 0` statement
      (∀ g, compactSupportSmooth g -> VanishesOn F g -> weilLocalSum(g) ≤ 0),
  * the route's only `fullWeilPositivity` for the finite-vanishing CC20 exit is set to
    `PLift (CC20FiniteVanishingWeilCriterion ...)`, which the source REFUTES
      (`not_...Input_fullWeilPositivity`),
  * `normalizedCC20YoshidaDetectorExists` is the PROVEN *positive* side, but it is
    an **existential** `∃ g, ... weilLocalSum(g) > 0` (detector), NOT a universal `≤0`.

So 847's earlier "flip ≤0 -> >0" was an OVERCLAIM: the two predicates are not one
predicate with a flipped inequality; they are different quantifier/inequality shapes.
The real switch candidate is the OTHER positivity producer, `Exhaustion.FullWeilPositivity`
(positive by construction), not the refuted finite-vanishing `≤0`.
-/

open ConnesWeilRH.Source
open ConnesWeilRH.Route

-- the two inequality/quantifier shapes to contrast
#check CC20WeilNonpositive
#check CC20FiniteVanishingWeilCriterion
#check ConnesWeilRH.WeilPositivityInput

-- the route's refuted finite-vanishing input
#check ConnesWeilRH.Route.normalizedCC20FiniteVanishingWeilCriterionInput
#check ConnesWeilRH.Route.normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity_eq
#check ConnesWeilRH.Route.not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity

-- the PROVEN detector-positive side (existential `weilLocalSum g > 0`, under InterpolationNode)
open ConnesWeilRH.Source.CC20YoshidaInterpolationNode
#check normalizedCC20YoshidaDetectorExists
#check normalizedCC20YoshidaDetectorExists_of_moment_data
#check concreteYoshidaMomentData_weilLocalSum_positive
#check concreteYoshidaMomentData_halfDensityPoleSum_negative

-- the positive-by-construction other producer (Exhaustion, ns = Route)
#check ConnesWeilRH.Route.FullWeilPositivity
#check ConnesWeilRH.Route.toWeilPositivityInput
#check ConnesWeilRH.Route.full_weil_positivity_input_holds

-- the criterion binding the input to the RH (that holds then)
#check ConnesWeilRH.FiniteVanishingCriterionPackage
#check CC20PropositionC1SourceCriterion
#check CC20PropositionC1InputData

-- (build-verified 2026-08-07, all #check resolve; body intentionally empty — this
--  pins the shapes and the double-mismatch, it does not close RH)