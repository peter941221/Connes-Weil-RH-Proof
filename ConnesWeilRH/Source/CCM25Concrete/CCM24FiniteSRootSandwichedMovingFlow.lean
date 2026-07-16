/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualMovingProjection
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace

/-!
# Root-sandwiched moving finite-S flow

The actual orthogonal projection derivative is sandwiched by the selected
convolution root before taking a trace.  The completed response is one
crossing plus its adjoint, so one explicit trace-class crossing witness makes
the real trace identity legal without cycling a raw whole-line convolution.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootSandwichedMovingFlow

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSBandTrace
open CCM24FiniteSActualMovingProjection

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- One root-smoothed oriented boundary crossing. -/
noncomputable def rootSandwichedLeftCrossing
    (root P X : Op) : Op :=
  root ∘L projectionLeftCrossing P X ∘L root.adjoint

/-- The completed root-smoothed orthogonal projection tangent. -/
noncomputable def rootSandwichedOrthogonalFlow
    (root P X : Op) : Op :=
  root ∘L orthogonalProjectionDerivative P X ∘L root.adjoint

/-- Root sandwiching preserves the completed crossing plus adjoint structure. -/
theorem rootSandwichedOrthogonalFlow_eq_left_add_adjoint
    (root P X : Op) :
    rootSandwichedOrthogonalFlow root P X =
      rootSandwichedLeftCrossing root P X +
        (rootSandwichedLeftCrossing root P X).adjoint := by
  unfold rootSandwichedOrthogonalFlow rootSandwichedLeftCrossing
    orthogonalProjectionDerivative
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- One trace-class oriented crossing makes the completed root-sandwiched
flow trace class in the same named Hilbert basis. -/
theorem rootSandwichedOrthogonalFlow_isTraceClassAlong
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (root P X : Op)
    (hleft : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedLeftCrossing root P X)) :
    PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedOrthogonalFlow root P X) := by
  rw [rootSandwichedOrthogonalFlow_eq_left_add_adjoint]
  exact PositiveTrace.isTraceClassAlong_add basis _ _ hleft
    (PositiveTrace.isTraceClassAlong_adjoint basis _ hleft)

/-- The legal completed trace is twice the real part of one oriented
crossing.  No branchwise absolute value or raw-convolution cycle occurs. -/
theorem ordinaryTraceAlong_rootSandwichedOrthogonalFlow_eq_two_re
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (root P X : Op)
    (hleft : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedLeftCrossing root P X)) :
    PositiveTrace.ordinaryTraceAlong basis
        (rootSandwichedOrthogonalFlow root P X) =
      (2 * (PositiveTrace.ordinaryTraceAlong basis
        (rootSandwichedLeftCrossing root P X)).re : ℝ) := by
  rw [rootSandwichedOrthogonalFlow_eq_left_add_adjoint]
  rw [PositiveTrace.ordinaryTraceAlong_add basis _ _ hleft
    (PositiveTrace.isTraceClassAlong_adjoint basis _ hleft)]
  rw [PositiveTrace.ordinaryTraceAlong_adjoint, Complex.star_def,
    Complex.add_conj]

/-- The selected convolution root applied to the actual moving Sonin
projection derivative. -/
noncomputable def actualMovingSoninRootFlow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  rootSandwichedOrthogonalFlow (rootConvolution owner)
    (parameterizedCanonicalGramProjection lambda alpha S)
    (parameterizedFiniteEulerGenerator alpha S)

/-- Its single oriented crossing, the remaining Gate 3L analytic owner. -/
noncomputable def actualMovingSoninRootCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  rootSandwichedLeftCrossing (rootConvolution owner)
    (parameterizedCanonicalGramProjection lambda alpha S)
    (parameterizedFiniteEulerGenerator alpha S)

theorem actualMovingSoninRootFlow_eq_crossing_add_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    actualMovingSoninRootFlow owner lambda alpha S =
      actualMovingSoninRootCrossing owner lambda alpha S +
        (actualMovingSoninRootCrossing owner lambda alpha S).adjoint := by
  exact rootSandwichedOrthogonalFlow_eq_left_add_adjoint _ _ _

/-- Infinite-dimensional readback of the moving Sonin trace response. -/
theorem ordinaryTraceAlong_actualMovingSoninRootFlow_eq_two_re
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime)
    (hcrossing : PositiveTrace.IsTraceClassAlong basis
      (actualMovingSoninRootCrossing owner lambda alpha S)) :
    PositiveTrace.ordinaryTraceAlong basis
        (actualMovingSoninRootFlow owner lambda alpha S) =
      (2 * (PositiveTrace.ordinaryTraceAlong basis
        (actualMovingSoninRootCrossing owner lambda alpha S)).re : ℝ) := by
  exact ordinaryTraceAlong_rootSandwichedOrthogonalFlow_eq_two_re
    basis _ _ _ hcrossing

end CCM24FiniteSRootSandwichedMovingFlow
end CCM25Concrete
end Source
end ConnesWeilRH
