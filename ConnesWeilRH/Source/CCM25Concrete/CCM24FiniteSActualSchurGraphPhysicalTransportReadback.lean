/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphSupportDefectReadback

/-!
# Physical Euler transport readback for the graph-support defect

Proof 523 identifies the complementary graph-support defect on the concrete
Schur carrier.  This module applies the actual normalized Euler transport to
the projected and unprojected graph frames.  The projected frame gives the
normalized Schur frame exactly; the unprojected frame leaves one explicit
physical residual.  No estimate of the defect itself is assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalTransportReadback

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurGraphSupportDefect
open CCM24FiniteSActualSchurGraphSupportDefectReadback
open CCM24FiniteSJuliaSchur
open CCM24FiniteSProjectionTrace

/-! ## The two concrete graph frames -/

noncomputable def canonicalProjectedGraphFrame
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  data.toColligation.projection ∘L data.toColligation.graphCosine +
    data.toColligation.graphSineCanonical

noncomputable def canonicalFullGraphFrame
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  data.toColligation.graphCosine + data.toColligation.graphSineCanonical

noncomputable def normalizedCanonicalGraphPhysicalResidual
    (data : PrimeEulerProjectedJuliaInput) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  normalizedPrimeEulerFrameTransport data.prime ∘L
    canonicalGraphSupportDefect data

theorem canonicalFullGraphFrame_eq_projected_add_supportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    canonicalFullGraphFrame data =
      canonicalProjectedGraphFrame data +
        canonicalGraphSupportDefect data := by
  unfold canonicalFullGraphFrame canonicalProjectedGraphFrame
    canonicalGraphSupportDefect graphSupportDefect complement
  simp only [ContinuousLinearMap.mul_def]
  rw [sub_eq_add_neg, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.neg_comp]
  have hone :
      (ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
          data.toColligation.graphCosine =
        data.toColligation.graphCosine := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  change data.toColligation.graphCosine + data.toColligation.graphSineCanonical =
    data.toColligation.projection ∘L data.toColligation.graphCosine +
      data.toColligation.graphSineCanonical +
        ((ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
          data.toColligation.graphCosine +
          -data.toColligation.projection ∘L data.toColligation.graphCosine)
  rw [hone]
  abel

/-! ## Actual normalized transport of the projected graph frame -/

theorem normalizedPrimeEulerFrameTransport_comp_projectedGraphFrame
    (data : PrimeEulerProjectedJuliaInput) :
    normalizedPrimeEulerFrameTransport data.prime ∘L
        canonicalProjectedGraphFrame data =
      data.normalizedSchurFrame := by
  apply ContinuousLinearMap.ext
  intro x
  unfold normalizedPrimeEulerFrameTransport canonicalProjectedGraphFrame
    PrimeEulerProjectedJuliaInput.normalizedSchurFrame
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  have h := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T x)
    (eulerTransport_on_projectedGraphFrame_eq_schurFrame
      data.toColligation data.toColligation.graphCosine)
  rw [primeEulerTransport_eq_id_sub_translation]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply] at h
  simp only [primeEulerSchurNormalizer, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  have hscalar : data.toColligation.scalar =
      (ccm24PrimeEulerCoefficient data.prime : ℂ) •
        (ContinuousLinearMap.id ℂ finiteSCarrier) := by
    rfl
  have htransport : data.toColligation.transport =
      (cc20GlobalLogTranslation
        (-Real.log data.prime)).toContinuousLinearMap := by
    rfl
  have hprojection : data.toColligation.projection = data.projection := by
    rfl
  have hgraphSine : data.toColligation.graphSine
      data.toColligation.graphCosine = data.toColligation.graphSineCanonical :=
    data.toColligation.graphSine_eq_graphSineCanonical
  rw [hscalar, htransport, hprojection, hgraphSine] at h
  rw [hprojection]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  apply congrArg (fun y : finiteSCarrier =>
    (1 + (ccm24PrimeEulerCoefficient data.prime : ℂ))⁻¹ • y)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, one_smul] using h

/-! ## The unprojected response and its physical residual -/

theorem normalizedPrimeEulerFrameTransport_comp_fullGraphFrame_eq_normalizedSchurFrame_add_residual
    (data : PrimeEulerProjectedJuliaInput) :
    normalizedPrimeEulerFrameTransport data.prime ∘L
        canonicalFullGraphFrame data =
      data.normalizedSchurFrame +
        normalizedCanonicalGraphPhysicalResidual data := by
  rw [canonicalFullGraphFrame_eq_projected_add_supportDefect]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, normalizedCanonicalGraphPhysicalResidual]
  rw [show normalizedPrimeEulerFrameTransport data.prime
      (canonicalProjectedGraphFrame data x) =
      data.normalizedSchurFrame x by
    exact congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T x)
      (normalizedPrimeEulerFrameTransport_comp_projectedGraphFrame data)]

theorem normalizedCanonicalGraphPhysicalResidual_norm_le_supportDefect
    (data : PrimeEulerProjectedJuliaInput) :
    ‖normalizedCanonicalGraphPhysicalResidual data‖ ≤
      ‖canonicalGraphSupportDefect data‖ := by
  unfold normalizedCanonicalGraphPhysicalResidual
  calc
    ‖normalizedPrimeEulerFrameTransport data.prime ∘L
        canonicalGraphSupportDefect data‖ ≤
      ‖normalizedPrimeEulerFrameTransport data.prime‖ *
        ‖canonicalGraphSupportDefect data‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖canonicalGraphSupportDefect data‖ := by
      exact mul_le_mul_of_nonneg_right
        (normalizedPrimeEulerFrameTransport_norm_le_one data.prime)
        (norm_nonneg _)
    _ = ‖canonicalGraphSupportDefect data‖ := one_mul _

end CCM24FiniteSActualSchurGraphPhysicalTransportReadback
end CCM25Concrete
end Source
end ConnesWeilRH
