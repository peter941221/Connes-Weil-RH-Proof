/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedRadialSupport

/-!
# Parameterized finite-S Sonin subspaces

The moving semilocal Hardy--Titchmarsh involution is the exact similarity of
the source involution by the synchronized Euler equivalence.  Its Fourier
support and complete Sonin intersection are therefore actual closed
subspaces on the common-log carrier.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedSoninSubspace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedRadialSupport

/-- Moving semilocal Hardy--Titchmarsh involution. -/
noncomputable def parameterizedSemilocalHardyTitchmarsh
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier ≃L[ℂ] finiteSCarrier :=
  (parameterizedFiniteEulerEquiv alpha S halpha).symm.trans
    (ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.trans
      (parameterizedFiniteEulerEquiv alpha S halpha))

theorem parameterizedSemilocalHardyTitchmarsh_apply
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedSemilocalHardyTitchmarsh alpha S halpha u =
      parameterizedFiniteEulerEquiv alpha S halpha
        (ccm24ArchimedeanHardyTitchmarsh
          ((parameterizedFiniteEulerEquiv alpha S halpha).symm u)) :=
  rfl

theorem parameterizedSemilocalHardyTitchmarsh_intertwines
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedSemilocalHardyTitchmarsh alpha S halpha
        (parameterizedFiniteEulerEquiv alpha S halpha u) =
      parameterizedFiniteEulerEquiv alpha S halpha
        (ccm24ArchimedeanHardyTitchmarsh u) := by
  rw [parameterizedSemilocalHardyTitchmarsh_apply]
  rw [(parameterizedFiniteEulerEquiv alpha S halpha).symm_apply_apply]

theorem parameterizedSemilocalHardyTitchmarsh_involutive
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedSemilocalHardyTitchmarsh alpha S halpha
        (parameterizedSemilocalHardyTitchmarsh alpha S halpha u) = u := by
  rw [parameterizedSemilocalHardyTitchmarsh_apply,
    parameterizedSemilocalHardyTitchmarsh_apply]
  rw [(parameterizedFiniteEulerEquiv alpha S halpha).symm_apply_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_involutive]
  rw [(parameterizedFiniteEulerEquiv alpha S halpha).apply_symm_apply]

/-- Actual moving Fourier-support closed subspace. -/
noncomputable def parameterizedFourierSupportClosedSubspace
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ClosedSubmodule ℂ finiteSCarrier :=
  ClosedSubmodule.comap
    (parameterizedSemilocalHardyTitchmarsh alpha S halpha).toContinuousLinearMap
    (ccm24LogRadialSupportClosedSubspace lambda)

theorem mem_parameterizedFourierSupportClosedSubspace_iff
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    u ∈ parameterizedFourierSupportClosedSubspace lambda alpha S halpha ↔
      parameterizedSemilocalHardyTitchmarsh alpha S halpha u ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
  Iff.rfl

theorem parameterizedFiniteEulerEquiv_mem_fourierSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda) :
    parameterizedFiniteEulerEquiv alpha S halpha u ∈
      parameterizedFourierSupportClosedSubspace lambda alpha S halpha := by
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff] at hu
  rw [mem_parameterizedFourierSupportClosedSubspace_iff]
  rw [parameterizedSemilocalHardyTitchmarsh_intertwines]
  exact parameterizedFiniteEulerEquiv_mem_radialSupport
    lambda alpha S halpha hu

theorem parameterizedFiniteEulerEquiv_symm_mem_sourceFourierSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈
      parameterizedFourierSupportClosedSubspace lambda alpha S halpha) :
    (parameterizedFiniteEulerEquiv alpha S halpha).symm u ∈
      ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  rw [mem_parameterizedFourierSupportClosedSubspace_iff] at hu
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
  have hpre := parameterizedFiniteEulerEquiv_symm_mem_radialSupport
    lambda alpha S halpha hu
  rw [parameterizedSemilocalHardyTitchmarsh_apply] at hpre
  rw [(parameterizedFiniteEulerEquiv alpha S halpha).symm_apply_apply]
    at hpre
  exact hpre

theorem parameterizedFiniteEulerEquiv_maps_fourierSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ClosedSubmodule.mapEquiv (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda) =
      parameterizedFourierSupportClosedSubspace lambda alpha S halpha := by
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda) u).1 hu
    have hout := parameterizedFiniteEulerEquiv_mem_fourierSupport
      lambda alpha S halpha hpre
    rw [(parameterizedFiniteEulerEquiv alpha S halpha).apply_symm_apply]
      at hout
    exact hout
  · intro hu
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda) u).2
    exact parameterizedFiniteEulerEquiv_symm_mem_sourceFourierSupport
      lambda alpha S halpha hu

/-- Complete moving Sonin intersection. -/
noncomputable def parameterizedSoninClosedSubspace
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ClosedSubmodule ℂ finiteSCarrier :=
  ccm24LogRadialSupportClosedSubspace lambda ⊓
    parameterizedFourierSupportClosedSubspace lambda alpha S halpha

/-- Exact transport of the complete source Sonin intersection. -/
theorem parameterizedFiniteEulerEquiv_maps_sonin
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ClosedSubmodule.mapEquiv (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda) =
      parameterizedSoninClosedSubspace lambda alpha S halpha := by
  rw [ccm24ArchimedeanSoninClosedSubspace,
    parameterizedSoninClosedSubspace,
    ClosedSubmodule.mapEquiv_inf_eq,
    parameterizedFiniteEulerEquiv_maps_radialSupport,
    parameterizedFiniteEulerEquiv_maps_fourierSupport]

end CCM24FiniteSParameterizedSoninSubspace
end CCM25Concrete
end Source
end ConnesWeilRH
