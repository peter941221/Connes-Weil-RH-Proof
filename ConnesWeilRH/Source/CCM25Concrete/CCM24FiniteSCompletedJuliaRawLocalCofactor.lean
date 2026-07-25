/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope

/-!
# Local raw cofactor bridge

Proof 555 identifies the raw adjacent row with the difference of two complete
raw response adjoints.  The local raw defect already stored in the same
source model is the corresponding un-adjointed difference after the reverse
transition has been inserted.

This module proves the exact cofactor identity

```text
localRawDefect(p,S) * T_(p,S)
  = -rho_p * RawRow(p,S)†.
```

The reverse-transition identity is used before any norm or trace is taken.
This is an operator identity only: it does not supply a uniform bound through
the physical ambient-plus-boundary analysis column.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawLocalCofactor

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Adjoint orientation -/

theorem suffixActualBandRawPhysicalFourTermRow_adjoint_eq_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRawPhysicalFourTermRow owner lambda p S)† =
      suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S := by
  rw [← suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow]
  simp only [ContinuousLinearMap.adjoint_adjoint]

/-! ## The local cofactor identity -/

theorem suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S ∘L
        suffixEulerFrameTransition lambda p S =
      -((primeSchurMarkovScalar p : ℂ) •
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S) := by
  apply ContinuousLinearMap.ext
  intro x
  have hpair := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator x)
    (suffixEulerFrameReverse_comp_transition lambda p S)
  simp only [suffixActualBandLocalRawDefect,
    suffixActualBandRawQuadraticIntertwiningDefect,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply]
    at hpair ⊢
  rw [hpair]
  simp only [map_smul]
  module

/-! ## The four-term row as the adjoint local cofactor -/

theorem suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawPhysicalRow_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandLocalRawDefect owner lambda p S ∘L
        suffixEulerFrameTransition lambda p S =
      -((primeSchurMarkovScalar p : ℂ) •
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S)†) := by
  rw [suffixActualBandRawPhysicalFourTermRow_adjoint_eq_rawIntertwiningDefect]
  exact suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawIntertwiningDefect
    owner lambda p S

end CCM24FiniteSCompletedJuliaRawLocalCofactor
end CCM25Concrete
end Source
end ConnesWeilRH
