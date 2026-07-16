/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24GaussianMellin
import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport

/-!
# Original CCM24 radial carriers and common-log readback

CCM24 first radializes both the archimedean carrier `L²(R)^ev` and the
`K_S`-invariant semilocal carrier to

`L²(R_+^*, d*rho)`.

This module retains that multiplicative-Haar carrier as a genuine type and
only then applies `rho = exp t`.  The archimedean radial Fourier transform is
constructed from the actual additive Plancherel Fourier transform through
the explicit half-density map.  The finite-S radial Fourier transform is
constructed from that genuine source transform and the independently built
finite Euler transport; it is not defined by conjugating either common-log
Hardy--Titchmarsh operator.

Primary source: CCM24 v2, Sections 3.1 and 4.1--4.2, especially equations
(17), (42), (47) and Theorem 1(ii):
https://arxiv.org/html/2310.18423v2
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

/-- The original archimedean radial carrier after `w_infinity`, before the
logarithmic coordinate is applied. -/
noncomputable abbrev ccm24ArchimedeanRadialL2 :=
  ccm24MultiplicativeHaarL2

/-- The radialized finite-S carrier after CCM24's canonical `w_S`.  The list
parameter records the visible finite places while the radial Haar measure is
the same canonical `d*rho` measure for every finite `S`. -/
noncomputable abbrev ccm24SemilocalRadialL2
    (_S : List CCM24VisiblePrime) := ccm24MultiplicativeHaarL2

/-- CCM24's normalized archimedean half-density map
`w_infinity : L²(R)^ev -> L²(R_+^*,d*rho)` as an actual unitary equivalence. -/
noncomputable def ccm24ArchimedeanEvenRadialEquiv :
    ccm24EvenAdditiveL2 ≃ₗᵢ[ℂ] ccm24ArchimedeanRadialL2 :=
  ccm24EvenLogCarrierEquiv.trans ccm24HaarLogEquiv.symm

/-- The source radial carrier aligns with common-log by the literal
measure-preserving substitution `rho = exp t`. -/
noncomputable def ccm24ArchimedeanRadialLogEquiv :
    ccm24ArchimedeanRadialL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  ccm24HaarLogEquiv

/-- The same literal Haar/log alignment for the radialized semilocal carrier. -/
noncomputable def ccm24SemilocalRadialLogEquiv
    (_S : List CCM24VisiblePrime) :
    ccm24SemilocalRadialL2 _S ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  ccm24HaarLogEquiv

/-- Genuine archimedean radial Fourier: apply the actual additive
Plancherel Fourier transform on `L²(R)^ev`, with the explicit `w_infinity`
equivalence on the two sides. -/
noncomputable def ccm24ArchimedeanRadialFourier :
    ccm24ArchimedeanRadialL2 ≃ₗᵢ[ℂ] ccm24ArchimedeanRadialL2 :=
  ccm24ArchimedeanEvenRadialEquiv.symm.trans
    (ccm24EvenAdditiveFourier.trans ccm24ArchimedeanEvenRadialEquiv)

/-- Before using the Fourier--Mellin theorem, the common-log readback of the
radial transform is exactly the independently transported genuine source
Fourier. -/
theorem ccm24ArchimedeanRadialFourier_log_readback_raw
    (u : ccm24ArchimedeanRadialL2) :
    ccm24ArchimedeanRadialLogEquiv
        (ccm24ArchimedeanRadialFourier u) =
      ccm24ArchimedeanSourceFourier
        (ccm24ArchimedeanRadialLogEquiv u) := by
  simp [ccm24ArchimedeanRadialLogEquiv,
    ccm24ArchimedeanRadialFourier,
    ccm24ArchimedeanEvenRadialEquiv,
    ccm24ArchimedeanSourceFourier_apply]

/-- Final source-carrier readback: genuine radial Fourier becomes the
Hardy--Titchmarsh involution in common-log coordinates. -/
theorem ccm24ArchimedeanRadialFourier_log_readback
    (u : ccm24ArchimedeanRadialL2) :
    ccm24ArchimedeanRadialLogEquiv
        (ccm24ArchimedeanRadialFourier u) =
      ccm24ArchimedeanHardyTitchmarsh
        (ccm24ArchimedeanRadialLogEquiv u) := by
  rw [ccm24ArchimedeanRadialFourier_log_readback_raw,
    ccm24ArchimedeanSourceFourier_eq_hardyTitchmarsh]

/-- The radial form of CCM24's finite Euler comparison map.  It is built by
moving the already explicit product `prod_p (I-p^(-1/2)U_(-log p))` through
the literal Haar/log coordinate equivalence. -/
noncomputable def ccm24FiniteEulerRadialTransportEquiv
    (S : List CCM24VisiblePrime) :
    ccm24ArchimedeanRadialL2 ≃L[ℂ] ccm24SemilocalRadialL2 S :=
  ccm24HaarLogEquiv.toContinuousLinearEquiv.trans
    ((ccm24FiniteEulerTransportEquiv S).trans
      ccm24HaarLogEquiv.symm.toContinuousLinearEquiv)

theorem ccm24FiniteEulerRadialTransport_log_intertwines
    (S : List CCM24VisiblePrime) (u : ccm24ArchimedeanRadialL2) :
    ccm24SemilocalRadialLogEquiv S
        (ccm24FiniteEulerRadialTransportEquiv S u) =
      ccm24FiniteEulerTransportEquiv S
        (ccm24ArchimedeanRadialLogEquiv u) := by
  simp [ccm24FiniteEulerRadialTransportEquiv,
    ccm24ArchimedeanRadialLogEquiv, ccm24SemilocalRadialLogEquiv]

/-- The finite-S radial Fourier transform, characterized on the original
radial carrier by the genuine source Fourier and the independently produced
Euler comparison map.  No Hardy--Titchmarsh operator occurs in this
definition. -/
noncomputable def ccm24SemilocalRadialFourier
    (S : List CCM24VisiblePrime) :
    ccm24SemilocalRadialL2 S ≃L[ℂ] ccm24SemilocalRadialL2 S :=
  (ccm24FiniteEulerRadialTransportEquiv S).symm.trans
    (ccm24ArchimedeanRadialFourier.toContinuousLinearEquiv.trans
      (ccm24FiniteEulerRadialTransportEquiv S))

theorem ccm24SemilocalRadialFourier_intertwines
    (S : List CCM24VisiblePrime) (u : ccm24ArchimedeanRadialL2) :
    ccm24SemilocalRadialFourier S
        (ccm24FiniteEulerRadialTransportEquiv S u) =
      ccm24FiniteEulerRadialTransportEquiv S
        (ccm24ArchimedeanRadialFourier u) := by
  rw [ccm24SemilocalRadialFourier]
  simp

/-- Final semilocal-carrier readback: the genuine finite-S radial Fourier
becomes the existing common-log `H_S`.  The proof uses the source
Fourier--Mellin theorem; the statement is not true by definition. -/
theorem ccm24SemilocalRadialFourier_log_readback
    (S : List CCM24VisiblePrime) (u : ccm24SemilocalRadialL2 S) :
    ccm24SemilocalRadialLogEquiv S
        (ccm24SemilocalRadialFourier S u) =
      ccm24SemilocalHardyTitchmarsh S
        (ccm24SemilocalRadialLogEquiv S u) := by
  let v : ccm24ArchimedeanRadialL2 :=
    (ccm24FiniteEulerRadialTransportEquiv S).symm u
  have hu : ccm24FiniteEulerRadialTransportEquiv S v = u := by
    exact (ccm24FiniteEulerRadialTransportEquiv S).apply_symm_apply u
  rw [← hu, ccm24SemilocalRadialFourier_intertwines,
    ccm24FiniteEulerRadialTransport_log_intertwines,
    ccm24ArchimedeanRadialFourier_log_readback,
    ccm24FiniteEulerRadialTransport_log_intertwines]
  exact (ccm24SemilocalHardyTitchmarsh_intertwines S
    (ccm24ArchimedeanRadialLogEquiv v)).symm

/-! ## Original radial Sonin data -/

noncomputable def ccm24ArchimedeanRadialSupportClosedSubspace
    (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ ccm24ArchimedeanRadialL2 :=
  ClosedSubmodule.mapEquiv
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24LogRadialSupportClosedSubspace lambda)

noncomputable def ccm24ArchimedeanRadialFourierSupportClosedSubspace
    (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ ccm24ArchimedeanRadialL2 :=
  ClosedSubmodule.mapEquiv
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24ArchimedeanFourierSupportClosedSubspace lambda)

noncomputable def ccm24SemilocalRadialSupportClosedSubspace
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule ℂ (ccm24SemilocalRadialL2 S) :=
  ClosedSubmodule.mapEquiv
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24LogRadialSupportClosedSubspace lambda)

noncomputable def ccm24SemilocalRadialFourierSupportClosedSubspace
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule ℂ (ccm24SemilocalRadialL2 S) :=
  ClosedSubmodule.mapEquiv
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24SemilocalFourierSupportClosedSubspace lambda S)

theorem mem_ccm24ArchimedeanRadialSupport_iff_log
    (lambda : CCM24SoninScale) (u : ccm24ArchimedeanRadialL2) :
    u ∈ ccm24ArchimedeanRadialSupportClosedSubspace lambda ↔
      ccm24ArchimedeanRadialLogEquiv u ∈
        ccm24LogRadialSupportClosedSubspace lambda := by
  exact ClosedSubmodule.mem_mapEquiv_iff
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24LogRadialSupportClosedSubspace lambda) u

theorem mem_ccm24ArchimedeanRadialFourierSupport_iff_log
    (lambda : CCM24SoninScale) (u : ccm24ArchimedeanRadialL2) :
    u ∈ ccm24ArchimedeanRadialFourierSupportClosedSubspace lambda ↔
      ccm24ArchimedeanRadialLogEquiv u ∈
        ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  exact ClosedSubmodule.mem_mapEquiv_iff
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24ArchimedeanFourierSupportClosedSubspace lambda) u

theorem mem_ccm24SemilocalRadialSupport_iff_log
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : ccm24SemilocalRadialL2 S) :
    u ∈ ccm24SemilocalRadialSupportClosedSubspace lambda S ↔
      ccm24SemilocalRadialLogEquiv S u ∈
        ccm24LogRadialSupportClosedSubspace lambda := by
  exact ClosedSubmodule.mem_mapEquiv_iff
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24LogRadialSupportClosedSubspace lambda) u

theorem mem_ccm24SemilocalRadialFourierSupport_iff_log
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : ccm24SemilocalRadialL2 S) :
    u ∈ ccm24SemilocalRadialFourierSupportClosedSubspace lambda S ↔
      ccm24SemilocalRadialLogEquiv S u ∈
        ccm24SemilocalFourierSupportClosedSubspace lambda S := by
  exact ClosedSubmodule.mem_mapEquiv_iff
    ccm24HaarLogEquiv.symm.toContinuousLinearEquiv
    (ccm24SemilocalFourierSupportClosedSubspace lambda S) u

/-- The pullback Fourier-support subspace is genuinely the inverse image of
the radial support under the original source radial Fourier transform. -/
theorem mem_ccm24ArchimedeanRadialFourierSupport_iff_fourier
    (lambda : CCM24SoninScale) (u : ccm24ArchimedeanRadialL2) :
    u ∈ ccm24ArchimedeanRadialFourierSupportClosedSubspace lambda ↔
      ccm24ArchimedeanRadialFourier u ∈
        ccm24ArchimedeanRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24ArchimedeanRadialFourierSupport_iff_log,
    mem_ccm24ArchimedeanRadialSupport_iff_log,
    ccm24ArchimedeanRadialFourier_log_readback,
    mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]

/-- The same genuine Fourier-support characterization on the finite-S
radial carrier. -/
theorem mem_ccm24SemilocalRadialFourierSupport_iff_fourier
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : ccm24SemilocalRadialL2 S) :
    u ∈ ccm24SemilocalRadialFourierSupportClosedSubspace lambda S ↔
      ccm24SemilocalRadialFourier S u ∈
        ccm24SemilocalRadialSupportClosedSubspace lambda S := by
  rw [mem_ccm24SemilocalRadialFourierSupport_iff_log,
    mem_ccm24SemilocalRadialSupport_iff_log,
    ccm24SemilocalRadialFourier_log_readback,
    mem_ccm24SemilocalFourierSupportClosedSubspace_iff]

/-- Proof 317 data on the original multiplicative-Haar radial carriers.  Its
common-log image is exactly the already concrete finite-Euler Sonin data. -/
noncomputable def concreteCCM24OriginalRadialSoninTransportData
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData
      ℂ ccm24ArchimedeanRadialL2 (ccm24SemilocalRadialL2 S) where
  sourceSupport := ccm24ArchimedeanRadialSupportClosedSubspace lambda
  sourceFourierSupport :=
    ccm24ArchimedeanRadialFourierSupportClosedSubspace lambda
  targetSupport := ccm24SemilocalRadialSupportClosedSubspace lambda S
  targetFourierSupport :=
    ccm24SemilocalRadialFourierSupportClosedSubspace lambda S
  theta := ccm24FiniteEulerRadialTransportEquiv S
  maps_sonin_intersection := by
    ext u
    rw [_root_.ConnesWeilRH.CC20Concrete.transportedClosedSubmodule]
    change
      u ∈ ClosedSubmodule.mapEquiv
          (ccm24FiniteEulerRadialTransportEquiv S)
          (ccm24ArchimedeanRadialSupportClosedSubspace lambda ⊓
            ccm24ArchimedeanRadialFourierSupportClosedSubspace lambda) ↔
        u ∈ ccm24SemilocalRadialSupportClosedSubspace lambda S ⊓
          ccm24SemilocalRadialFourierSupportClosedSubspace lambda S
    rw [ClosedSubmodule.mem_mapEquiv_iff]
    change
      (((ccm24FiniteEulerRadialTransportEquiv S).symm u ∈
            ccm24ArchimedeanRadialSupportClosedSubspace lambda) ∧
          ((ccm24FiniteEulerRadialTransportEquiv S).symm u ∈
            ccm24ArchimedeanRadialFourierSupportClosedSubspace lambda)) ↔
        ((u ∈ ccm24SemilocalRadialSupportClosedSubspace lambda S) ∧
          (u ∈ ccm24SemilocalRadialFourierSupportClosedSubspace lambda S))
    rw [mem_ccm24ArchimedeanRadialSupport_iff_log,
      mem_ccm24ArchimedeanRadialFourierSupport_iff_log,
      mem_ccm24SemilocalRadialSupport_iff_log,
      mem_ccm24SemilocalRadialFourierSupport_iff_log]
    change
      ccm24HaarLogEquiv
          ((ccm24FiniteEulerRadialTransportEquiv S).symm u) ∈
            ccm24ArchimedeanSoninClosedSubspace lambda ↔
        ccm24HaarLogEquiv u ∈ ccm24SemilocalSoninClosedSubspace lambda S
    have hintertwine :
        ccm24HaarLogEquiv
            ((ccm24FiniteEulerRadialTransportEquiv S).symm u) =
          (ccm24FiniteEulerTransportEquiv S).symm
            (ccm24HaarLogEquiv u) := by
      simp [ccm24FiniteEulerRadialTransportEquiv]
    rw [hintertwine, ← ccm24FiniteEulerTransport_maps_sonin lambda S]
    exact (ClosedSubmodule.mem_mapEquiv_iff
      (ccm24FiniteEulerTransportEquiv S)
      (ccm24ArchimedeanSoninClosedSubspace lambda)
      (ccm24HaarLogEquiv u)).symm

theorem concreteCCM24OriginalRadialSoninTransportData_log_theta
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (u : ccm24ArchimedeanRadialL2) :
    ccm24SemilocalRadialLogEquiv S
        ((concreteCCM24OriginalRadialSoninTransportData lambda S).theta u) =
      (concreteCCM24SoninTransportData lambda S).theta
        (ccm24ArchimedeanRadialLogEquiv u) :=
  ccm24FiniteEulerRadialTransport_log_intertwines S u

end CC20Concrete
end Source
end ConnesWeilRH
