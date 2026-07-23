/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphSupportDefect

/-!
# Concrete normalized readback of the graph-support defect

Proof 522 names the complementary graph defect at the generic colligation
level.  This module carries that ledger through the actual
`PrimeEulerProjectedJuliaInput` and its normalized Schur frame.  The projected
carrier keeps the Schur part and deletes the complementary defect; no estimate
or vanishing claim is made.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphSupportDefectReadback

open CCM24FiniteSJuliaSchur
open CCM24FiniteSActualSchurGraphSupportDefect
open CCM24FiniteSProjectionTrace

/-! ## Concrete graph-action and defect operators -/

noncomputable def canonicalGraphActionUpper
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (data.toColligation.eulerGraphAction
      data.toColligation.graphCosine
      data.toColligation.graphSineCanonical).1

noncomputable def canonicalGraphSupportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  graphSupportDefect data.toColligation data.toColligation.graphCosine

noncomputable def normalizedCanonicalGraphActionUpper
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  primeEulerSchurNormalizer data.prime ∘L
    canonicalGraphActionUpper data

noncomputable def normalizedCanonicalGraphSupportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  primeEulerSchurNormalizer data.prime ∘L
    canonicalGraphSupportDefect data

/-! ## Exact source-carrier readback -/

theorem canonicalGraphActionUpper_eq_schur_add_supportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    canonicalGraphActionUpper data =
      data.toColligation.schurFrame data.toColligation.graphCosine +
        canonicalGraphSupportDefect data := by
  simpa only [canonicalGraphActionUpper, canonicalGraphSupportDefect] using
    congrArg Prod.fst
      (eulerGraphAction_on_graphFrame_eq_schur_add_graphSupportDefect
        data.toColligation data.toColligation.graphCosine)

theorem projection_mul_canonicalGraphSupportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    data.toColligation.projection * canonicalGraphSupportDefect data = 0 := by
  have hprojection : data.toColligation.projection = data.projection := rfl
  have hidempotent : data.projection * data.projection = data.projection := by
    simpa only [ContinuousLinearMap.mul_def] using data.projection_idempotent
  change data.toColligation.projection *
      (complement data.toColligation.projection *
        data.toColligation.graphCosine) = 0
  calc
    data.projection *
        (complement data.toColligation.projection *
          data.toColligation.graphCosine) =
      (data.projection * complement data.toColligation.projection) *
        data.toColligation.graphCosine := by
          noncomm_ring
    _ = 0 := by
      rw [hprojection]
      unfold complement
      calc
        data.projection * (1 - data.projection) *
            data.toColligation.graphCosine =
          (data.projection - data.projection * data.projection) *
            data.toColligation.graphCosine := by
              noncomm_ring
        _ = 0 := by
          rw [hidempotent]
          simp

theorem projection_mul_canonicalGraphActionUpper_eq_schurFrame
    (data : PrimeEulerProjectedJuliaInput) :
    data.projection * canonicalGraphActionUpper data =
      data.toColligation.schurFrame data.toColligation.graphCosine := by
  change data.toColligation.projection * canonicalGraphActionUpper data =
    data.toColligation.schurFrame data.toColligation.graphCosine
  rw [canonicalGraphActionUpper_eq_schur_add_supportDefect]
  rw [mul_add]
  rw [data.toColligation.projection_mul_schurFrame,
    projection_mul_canonicalGraphSupportDefect]
  simp

theorem normalizedCanonicalGraphActionUpper_eq_normalizedSchurFrame_add_defect
    (data : PrimeEulerProjectedJuliaInput) :
    normalizedCanonicalGraphActionUpper data =
      data.normalizedSchurFrame +
        normalizedCanonicalGraphSupportDefect data := by
  unfold normalizedCanonicalGraphActionUpper
  rw [
    canonicalGraphActionUpper_eq_schur_add_supportDefect,
    normalizedCanonicalGraphSupportDefect,
    PrimeEulerProjectedJuliaInput.normalizedSchurFrame]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

end CCM24FiniteSActualSchurGraphSupportDefectReadback
end CCM25Concrete
end Source
end ConnesWeilRH
