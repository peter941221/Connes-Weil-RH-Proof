/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerEquiv

/-!
# Parameterized Euler preservation of radial support

Every synchronized factor and every term of its Neumann inverse uses a
translation toward smaller logarithmic coordinates.  Hence the moving
transport preserves the literal CCM24 radial support subspace in both
directions.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedRadialSupport

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerEquiv

theorem parameterizedPrimeEulerContraction_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ) (p : CCM24VisiblePrime)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedPrimeEulerContraction alpha p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  unfold parameterizedPrimeEulerContraction
  exact (ccm24LogRadialSupportClosedSubspace lambda).smul_mem _
    (ccm24PrimeEulerContraction_mem_logRadialSupport lambda p hu)

theorem parameterizedPrimeEulerFactor_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ) (p : CCM24VisiblePrime)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedPrimeEulerFactor alpha p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  unfold parameterizedPrimeEulerFactor
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  exact (ccm24LogRadialSupportClosedSubspace lambda).sub_mem hu
    (parameterizedPrimeEulerContraction_mem_radialSupport
      lambda alpha p hu)

theorem parameterizedPrimeEulerInverse_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ) (p : CCM24VisiblePrime)
    (halpha : |alpha| ≤ 1) {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedPrimeEulerInverse alpha p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  have hsummable : Summable
      (fun n : ℕ => parameterizedPrimeEulerContraction alpha p ^ n) :=
    summable_geometric_of_norm_lt_one
      (norm_parameterizedPrimeEulerContraction_lt_one alpha p halpha)
  unfold parameterizedPrimeEulerInverse
  have heval :
      (∑' n : ℕ, parameterizedPrimeEulerContraction alpha p ^ n) u =
        ∑' n : ℕ, (parameterizedPrimeEulerContraction alpha p ^ n) u := by
    simpa using
      (ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum hsummable
  rw [heval]
  apply tsum_mem (ccm24LogRadialSupportClosedSubspace lambda).isClosed
  intro n
  induction n with
  | zero => simpa using hu
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact parameterizedPrimeEulerContraction_mem_radialSupport
        lambda alpha p ih

theorem parameterizedFiniteEulerFactor_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedFiniteEulerFactor alpha S u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  induction S generalizing u with
  | nil => simpa [parameterizedFiniteEulerFactor] using hu
  | cons p S ih =>
      rw [parameterizedFiniteEulerFactor,
        ContinuousLinearMap.mul_apply]
      exact parameterizedPrimeEulerFactor_mem_radialSupport
        lambda alpha p (ih hu)

theorem parameterizedFiniteEulerInverse_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedFiniteEulerInverse alpha S u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  induction S generalizing u with
  | nil => simpa [parameterizedFiniteEulerInverse] using hu
  | cons p S ih =>
      rw [parameterizedFiniteEulerInverse,
        ContinuousLinearMap.mul_apply]
      exact ih (parameterizedPrimeEulerInverse_mem_radialSupport
        lambda alpha p halpha hu)

theorem parameterizedFiniteEulerEquiv_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    parameterizedFiniteEulerEquiv alpha S halpha u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  rw [parameterizedFiniteEulerEquiv_apply]
  exact parameterizedFiniteEulerFactor_mem_radialSupport
    lambda alpha S hu

theorem parameterizedFiniteEulerEquiv_symm_mem_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    (parameterizedFiniteEulerEquiv alpha S halpha).symm u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  rw [parameterizedFiniteEulerEquiv_symm_apply]
  exact parameterizedFiniteEulerInverse_mem_radialSupport
    lambda alpha S halpha hu

/-- The actual moving Euler equivalence maps the fixed radial support
subspace onto itself. -/
theorem parameterizedFiniteEulerEquiv_maps_radialSupport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ClosedSubmodule.mapEquiv (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24LogRadialSupportClosedSubspace lambda) =
      ccm24LogRadialSupportClosedSubspace lambda := by
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24LogRadialSupportClosedSubspace lambda) u).1 hu
    have hout := parameterizedFiniteEulerEquiv_mem_radialSupport
      lambda alpha S halpha hpre
    rw [(parameterizedFiniteEulerEquiv alpha S halpha).apply_symm_apply]
      at hout
    exact hout
  · intro hu
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24LogRadialSupportClosedSubspace lambda) u).2
    exact parameterizedFiniteEulerEquiv_symm_mem_radialSupport
      lambda alpha S halpha hu

end CCM24FiniteSParameterizedRadialSupport
end CCM25Concrete
end Source
end ConnesWeilRH
