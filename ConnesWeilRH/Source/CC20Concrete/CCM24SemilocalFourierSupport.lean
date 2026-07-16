/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24FiniteEulerSoninTransport
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# Concrete semilocal Fourier support

CCM24 Proposition 4.6 proves `F_S theta_S = theta_S F_infinity`.
On the common logarithmic carrier, `theta_S` is the concrete finite Euler
transport `T_S`. Therefore the semilocal Hardy--Titchmarsh transform is the
specific similarity

`H_S = T_S H_infinity T_S⁻¹`.

This module uses that operator to define the target Fourier-support closed
subspace, proves exact transport of both support conditions, and constructs
the restricted finite-S Sonin equivalence without any stored support or
intersection-transport premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

/-- The actual semilocal Hardy--Titchmarsh transform in common log
coordinates, forced by CCM24's Fourier-intertwining identity. -/
noncomputable def ccm24SemilocalHardyTitchmarsh
    (S : List CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 ≃L[ℂ] cc20GlobalLogCrossingL2 :=
  (ccm24FiniteEulerTransportEquiv S).symm.trans
    (ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.trans
      (ccm24FiniteEulerTransportEquiv S))

theorem ccm24SemilocalHardyTitchmarsh_apply
    (S : List CCM24VisiblePrime) (u : cc20GlobalLogCrossingL2) :
    ccm24SemilocalHardyTitchmarsh S u =
      ccm24FiniteEulerTransportEquiv S
        (ccm24ArchimedeanHardyTitchmarsh
          ((ccm24FiniteEulerTransportEquiv S).symm u)) :=
  rfl

/-- The concrete finite Euler transport intertwines the archimedean and
semilocal Hardy--Titchmarsh transforms. -/
theorem ccm24SemilocalHardyTitchmarsh_intertwines
    (S : List CCM24VisiblePrime) (u : cc20GlobalLogCrossingL2) :
    ccm24SemilocalHardyTitchmarsh S
        (ccm24FiniteEulerTransportEquiv S u) =
      ccm24FiniteEulerTransportEquiv S
        (ccm24ArchimedeanHardyTitchmarsh u) := by
  rw [ccm24SemilocalHardyTitchmarsh_apply]
  rw [(ccm24FiniteEulerTransportEquiv S).symm_apply_apply]

/-- The concrete semilocal Hardy--Titchmarsh transform is an involution. -/
theorem ccm24SemilocalHardyTitchmarsh_involutive
    (S : List CCM24VisiblePrime) (u : cc20GlobalLogCrossingL2) :
    ccm24SemilocalHardyTitchmarsh S
        (ccm24SemilocalHardyTitchmarsh S u) = u := by
  rw [ccm24SemilocalHardyTitchmarsh_apply,
    ccm24SemilocalHardyTitchmarsh_apply]
  rw [(ccm24FiniteEulerTransportEquiv S).symm_apply_apply]
  rw [ccm24ArchimedeanHardyTitchmarsh_involutive]
  rw [(ccm24FiniteEulerTransportEquiv S).apply_symm_apply]

/-- The actual target Fourier-support condition: the semilocal
Hardy--Titchmarsh transform vanishes below `log lambda`. -/
noncomputable def ccm24SemilocalFourierSupportClosedSubspace
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 :=
  ClosedSubmodule.comap
    (ccm24SemilocalHardyTitchmarsh S).toContinuousLinearMap
    (ccm24LogRadialSupportClosedSubspace lambda)

theorem mem_ccm24SemilocalFourierSupportClosedSubspace_iff
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24SemilocalFourierSupportClosedSubspace lambda S ↔
      ccm24SemilocalHardyTitchmarsh S u ∈
        ccm24LogRadialSupportClosedSubspace lambda :=
  Iff.rfl

theorem ccm24FiniteEulerTransportEquiv_mem_semilocalFourierSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda) :
    ccm24FiniteEulerTransportEquiv S u ∈
      ccm24SemilocalFourierSupportClosedSubspace lambda S := by
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff] at hu
  rw [mem_ccm24SemilocalFourierSupportClosedSubspace_iff]
  rw [ccm24SemilocalHardyTitchmarsh_intertwines]
  exact ccm24FiniteEulerTransportEquiv_mem_logRadialSupport lambda S hu

theorem ccm24FiniteEulerTransportEquiv_symm_mem_archimedeanFourierSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24SemilocalFourierSupportClosedSubspace lambda S) :
    (ccm24FiniteEulerTransportEquiv S).symm u ∈
      ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  rw [mem_ccm24SemilocalFourierSupportClosedSubspace_iff] at hu
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
  have hpre := ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
    lambda S hu
  rw [ccm24SemilocalHardyTitchmarsh_apply] at hpre
  simpa using hpre

/-- The concrete finite Euler transport maps the actual archimedean Fourier
support onto the actual semilocal Fourier support. -/
theorem ccm24FiniteEulerTransport_maps_fourierSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule.mapEquiv (ccm24FiniteEulerTransportEquiv S)
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda) =
      ccm24SemilocalFourierSupportClosedSubspace lambda S := by
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (ccm24FiniteEulerTransportEquiv S)
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda) u).1 hu
    simpa using
      ccm24FiniteEulerTransportEquiv_mem_semilocalFourierSupport
        lambda S hpre
  · intro hu
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (ccm24FiniteEulerTransportEquiv S)
      (ccm24ArchimedeanFourierSupportClosedSubspace lambda) u).2
    exact
      ccm24FiniteEulerTransportEquiv_symm_mem_archimedeanFourierSupport
        lambda S hu

/-- The complete semilocal Sonin space on the common log carrier. -/
noncomputable def ccm24SemilocalSoninClosedSubspace
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 :=
  ccm24LogRadialSupportClosedSubspace lambda ⊓
    ccm24SemilocalFourierSupportClosedSubspace lambda S

/-- Exact complete-Sonin transport, derived from the two actual support
operators rather than stored as a theorem field. -/
theorem ccm24FiniteEulerTransport_maps_sonin
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule.mapEquiv (ccm24FiniteEulerTransportEquiv S)
        (ccm24ArchimedeanSoninClosedSubspace lambda) =
      ccm24SemilocalSoninClosedSubspace lambda S := by
  rw [ccm24ArchimedeanSoninClosedSubspace,
    ccm24SemilocalSoninClosedSubspace,
    ClosedSubmodule.mapEquiv_inf_eq,
    ccm24FiniteEulerTransport_maps_logRadialSupport,
    ccm24FiniteEulerTransport_maps_fourierSupport]

/-- Restriction of the concrete finite Euler transport to the actual source
and semilocal Sonin spaces. -/
noncomputable def ccm24FiniteEulerRestrictedSoninLinearEquiv
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule ≃ₗ[ℂ]
      (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule where
  toFun u :=
    ⟨ccm24FiniteEulerTransportEquiv S u,
      ⟨ccm24FiniteEulerTransportEquiv_mem_logRadialSupport
          lambda S u.property.1,
        ccm24FiniteEulerTransportEquiv_mem_semilocalFourierSupport
          lambda S u.property.2⟩⟩
  invFun u :=
    ⟨(ccm24FiniteEulerTransportEquiv S).symm u,
      ⟨ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
          lambda S u.property.1,
        ccm24FiniteEulerTransportEquiv_symm_mem_archimedeanFourierSupport
          lambda S u.property.2⟩⟩
  left_inv u := by
    apply Subtype.ext
    exact (ccm24FiniteEulerTransportEquiv S).symm_apply_apply u
  right_inv u := by
    apply Subtype.ext
    exact (ccm24FiniteEulerTransportEquiv S).apply_symm_apply u
  map_add' u v := by
    apply Subtype.ext
    exact (ccm24FiniteEulerTransportEquiv S).map_add u v
  map_smul' c u := by
    apply Subtype.ext
    exact (ccm24FiniteEulerTransportEquiv S).map_smul c u

noncomputable def ccm24FiniteEulerRestrictedSoninEquiv
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule ≃L[ℂ]
      (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule :=
  LinearEquiv.toContinuousLinearEquivOfBounds
      (ccm24FiniteEulerRestrictedSoninLinearEquiv lambda S)
      ‖(ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap‖
      ‖(ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap‖
      (fun u => by
        change ‖ccm24FiniteEulerTransportEquiv S (u : cc20GlobalLogCrossingL2)‖ ≤
          ‖(ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap‖ *
            ‖(u : cc20GlobalLogCrossingL2)‖
        exact (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap.le_opNorm _)
      (fun u => by
        change ‖(ccm24FiniteEulerTransportEquiv S).symm
            (u : cc20GlobalLogCrossingL2)‖ ≤
          ‖(ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap‖ *
            ‖(u : cc20GlobalLogCrossingL2)‖
        exact (ccm24FiniteEulerTransportEquiv S).symm.toContinuousLinearMap.le_opNorm _)

theorem ccm24FiniteEulerRestrictedSoninEquiv_coe
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule) :
    ((ccm24FiniteEulerRestrictedSoninEquiv lambda S u :
        (ccm24SemilocalSoninClosedSubspace lambda S).toSubmodule) :
      cc20GlobalLogCrossingL2) =
        ccm24FiniteEulerTransportEquiv S u :=
  rfl

/-- The fully concrete finite-S instance of CCM24 Theorem 4.6. No support
subspace or restricted equivalence remains as caller-supplied data. -/
noncomputable def concreteCCM24FiniteEulerRestrictedSoninData
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    CCM24FiniteEulerRestrictedSoninData lambda S where
  sourceFourierSupport :=
    ccm24ArchimedeanFourierSupportClosedSubspace lambda
  targetFourierSupport :=
    ccm24SemilocalFourierSupportClosedSubspace lambda S
  restrictedTheta := ccm24FiniteEulerRestrictedSoninEquiv lambda S
  restrictedTheta_coe := ccm24FiniteEulerRestrictedSoninEquiv_coe lambda S

noncomputable def concreteCCM24SoninTransportData
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData
      ℂ cc20GlobalLogCrossingL2 cc20GlobalLogCrossingL2 :=
  (concreteCCM24FiniteEulerRestrictedSoninData lambda S).toSoninTransportData

/-- Proof 315 positivity instantiated with the concrete radial support,
archimedean Fourier support, semilocal Fourier support, and finite Euler
restricted equivalence. -/
theorem concreteCCM24_target_compression_sub_gramCorrected_isPositive
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection ∘L
          (ccm24SemilocalFourierSupportClosedSubspace lambda S).toSubmodule.starProjection ∘L
          (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection -
        (concreteCCM24SoninTransportData lambda S).gramCorrectedTargetSoninProjection).IsPositive :=
  CCM24FiniteEulerRestrictedSoninData.target_compression_sub_gramCorrected_isPositive
    (concreteCCM24FiniteEulerRestrictedSoninData lambda S)

end CC20Concrete
end Source
end ConnesWeilRH
