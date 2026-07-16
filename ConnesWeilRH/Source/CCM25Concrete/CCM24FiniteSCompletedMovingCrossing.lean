/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandCalculus

/-!
# Completed infinite-dimensional moving Sonin crossing

The source identity `R=E Q E-K_prol` is inserted into the actual oriented
projection crossing on the common-log Hilbert carrier.  The outer crossing,
compressed second-support crossing, both prolate interference terms, and the
prolate square remain in one operator before trace legality or estimation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedMovingCrossing

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSOrthogonalProjectionFlow

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The compressed second-support operator `E Q E`. -/
noncomputable def compressedSecondSupport (E Q : Op) : Op :=
  E * Q * E

/-- Difference of the two oriented projection crossings. -/
noncomputable def signedProjectionLeftCrossing
    (E R X : Op) : Op :=
  projectionLeftCrossing E X - projectionLeftCrossing R X

/-- The complete five-branch expansion after substituting
`R=E Q E-K_prol`.  No branch is estimated separately here. -/
noncomputable def completedMovingCrossing
    (E Q K X : Op) : Op :=
  let A := compressedSecondSupport E Q
  projectionLeftCrossing E X -
      (1 - A) * X * A +
    (1 - A) * X * K -
    K * X * A +
    K * X * K

/-- Algebraic five-branch readback of the complete signed crossing. -/
theorem signedProjectionLeftCrossing_eq_completedMovingCrossing
    (E Q R K X : Op)
    (hR : R = compressedSecondSupport E Q - K) :
    signedProjectionLeftCrossing E R X =
      completedMovingCrossing E Q K X := by
  rw [hR]
  unfold signedProjectionLeftCrossing completedMovingCrossing
    projectionLeftCrossing
  dsimp only
  noncomm_ring

/-- Actual moving `R_alpha=E Q_alpha E-K_alpha` identity. -/
theorem parameterizedCanonicalGramProjection_eq_compression_sub_prolate
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedCanonicalGramProjection lambda alpha S =
      compressedSecondSupport
          (radialSupportProjection lambda)
          (parameterizedFourierSupportProjection lambda alpha S halpha) -
        parameterizedProlateRemainder lambda alpha S halpha := by
  rw [parameterizedCanonicalGramProjection_eq_soninProjection
    lambda alpha S halpha]
  unfold parameterizedProlateRemainder compressedSecondSupport
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The true common-log moving outer-minus-Sonin crossing is the complete
five-branch owner. -/
theorem actualSignedMovingCrossing_eq_completed
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    signedProjectionLeftCrossing
        (radialSupportProjection lambda)
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) =
      completedMovingCrossing
        (radialSupportProjection lambda)
        (parameterizedFourierSupportProjection lambda alpha S halpha)
        (parameterizedProlateRemainder lambda alpha S halpha)
        (parameterizedFiniteEulerGenerator alpha S) := by
  exact signedProjectionLeftCrossing_eq_completedMovingCrossing _ _ _ _ _
    (parameterizedCanonicalGramProjection_eq_compression_sub_prolate
      lambda alpha S halpha)

/-- Root sandwiching is applied only after the five branches have been
recombined into the complete physical-boundary owner. -/
theorem rootSandwiched_actualSignedMovingCrossing_eq_completed
    (root : Op) (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    root ∘L
        signedProjectionLeftCrossing
          (radialSupportProjection lambda)
          (parameterizedCanonicalGramProjection lambda alpha S)
          (parameterizedFiniteEulerGenerator alpha S) ∘L
        root.adjoint =
      root ∘L
        completedMovingCrossing
          (radialSupportProjection lambda)
          (parameterizedFourierSupportProjection lambda alpha S halpha)
          (parameterizedProlateRemainder lambda alpha S halpha)
          (parameterizedFiniteEulerGenerator alpha S) ∘L
        root.adjoint := by
  rw [actualSignedMovingCrossing_eq_completed lambda alpha S halpha]

end CCM24FiniteSCompletedMovingCrossing
end CCM25Concrete
end Source
end ConnesWeilRH
