import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.CC20RHExit
import ConnesWeilRH.Route.CC20RouteRealization
import ConnesWeilRH.Route.Exhaustion

/-!
# 848 probe: is `Exhaustion.FullWeilPositivity` (constructive) a *type-compatible* replacement
for the refuted finite-vanishing `fullWeilPositivity`?

The architecture (per 847b):
  CC20PropositionC1SourceCriterion B F input = CC20PropositionC1InputData B F input → B.SourceRH
  CC20PropositionC1InputData fields include `fullWeilPositivity : input.fullWeilPositivity`
    -- i.e. the criterion demands the input's OWN fullWeilPositivity as a witness.
  The refutation `not_...Input_fullWeilPositivity` targets the SPECIFIC value
    `normalizedCC20FiniteVanishingWeilCriterionInput` (its field = refuted universal ≤0).
  WHILSW `Exhaustion.toWeilPositivityInput` produces an input whose
    fullWeilPositivity = `FullWeilPositivity inputs g L` (a VALUE/type, constructive,
    not refuted).

So the refutation is per-VALUE, not per-type: the criterion slot accepts any
`WeilPositivityInput`; the finite-vanishing one is dead because ITS OWN field is false,
the Exhaustion one is not automatically blocked.  The remaining REAL question this probe
pins is the (required) 2 fields of `CC20PropositionC1RouteInputData`:
  tripleVanishingMatchesMellin  (for g.test.tripleVanishing)
  + the finiteSetDisjointFromNontrivialZeros for the same F.
Whether the Exhaustion-based input actually satisfies the standard `F = cc20TripleFiniteVanishingSet`
is a PER-F / carrier question, not a sign flip.

This file pins those shapes with `#check`; body intentionally empty (audit only).  It
does not close RH.  All identifiers were just verified to exist for the build.
-/

open ConnesWeilRH.Source
open ConnesWeilRH.Route

namespace ConnesWeilRH

-- the two positivity producers both fit `WeilPositivityInput` (value-level, same type)
#check CC20PropositionC1InputData
#check CC20PropositionC1SourceCriterion
#check Route.normalizedCC20FiniteVanishingWeilCriterionInput
#check Route.toWeilPositivityInput
#check Route.FullWeilPositivity

-- the per-value refutation vs the constructive field
#check Route.normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity_eq
#check Route.not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity

-- the concrete/proven positive side (detector), per-g, constructive
open ConnesWeilRH.Source.CC20YoshidaInterpolationNode
#check concreteYoshidaMomentData_weilLocalSum_positive
#check concreteYoshidaMomentData_halfDensityPoleSum_negative
#check normalizedCC20YoshidaDetectorExists

end ConnesWeilRH