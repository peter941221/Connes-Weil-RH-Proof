/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaSchur
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds

/-!
# Contractivity of the normalized Schur frame

The complementary Euler corner is a strict contraction, but that fact is
not itself the cascade contract.  This module supplies the missing producer:
the graph frame is contractive after the canonical inverse square-root, and
the upper Euler normalization turns the Schur frame into a contraction.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaSchur

open CC20Concrete
open CCM24FiniteSJuliaCausal

section Generic

variable {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem ProjectedUnitaryColligation.graphCoordinate_left_complement
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) :
    complement data.projection * data.graphCoordinate =
      data.graphCoordinate := by
  unfold ProjectedUnitaryColligation.graphCoordinate
  calc
    complement data.projection *
          (data.scalar * data.resolvent * data.U10) =
        data.scalar *
          ((complement data.projection * data.resolvent) * data.U10) := by
      calc
        complement data.projection *
              (data.scalar * data.resolvent * data.U10) =
            (complement data.projection * data.scalar) *
              data.resolvent * data.U10 := by noncomm_ring
        _ = (data.scalar * complement data.projection) *
              data.resolvent * data.U10 := by
          rw [← data.scalar_central (complement data.projection)]
        _ = data.scalar *
              ((complement data.projection * data.resolvent) * data.U10) := by
          noncomm_ring
    _ = data.scalar * (data.resolvent * data.U10) := by
      rw [data.resolvent_left_support]
    _ = data.graphCoordinate := by
      rfl

theorem ProjectedUnitaryColligation.projection_mul_graphCoordinate
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) :
    data.projection * data.graphCoordinate = 0 := by
  have hleft := data.graphCoordinate_left_complement
  calc
    data.projection * data.graphCoordinate =
        data.projection *
          (complement data.projection * data.graphCoordinate) := by
      rw [hleft]
    _ = (data.projection * complement data.projection) *
          data.graphCoordinate := by
      noncomm_ring
    _ = 0 := by
      rw [data.projection_mul_complement]
      simp

theorem ProjectedUnitaryColligation.graphCoordinate_adjoint_mul_projection
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) :
    ContinuousLinearMap.adjoint data.graphCoordinate * data.projection = 0 := by
  have h := congrArg
    (fun T : K →L[ℂ] K => ContinuousLinearMap.adjoint T)
    (data.projection_mul_graphCoordinate)
  dsimp at h
  rw [ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint_comp] at h
  rw [← ContinuousLinearMap.star_eq_adjoint data.projection,
    data.projection_selfAdjoint] at h
  simpa using h

theorem ProjectedUnitaryColligation.graphFrame_norm_le_one
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) :
    ‖(data.projection + data.graphCoordinate) ∘L
        data.graphCosine‖ ≤ 1 := by
  have hprojection : IsStarProjection data.projection := by
    refine
      { isIdempotentElem := by
          simpa only [ContinuousLinearMap.mul_def] using
            data.projection_idempotent
        isSelfAdjoint := by
          simpa only [ContinuousLinearMap.star_eq_adjoint] using
            data.projection_selfAdjoint }
  have hgram :
      ContinuousLinearMap.adjoint
          (data.projection + data.graphCoordinate) *
        (data.projection + data.graphCoordinate) =
      data.projection +
        ContinuousLinearMap.adjoint data.graphCoordinate *
          data.graphCoordinate := by
    have hstar :
        ContinuousLinearMap.adjoint
            (data.projection + data.graphCoordinate) =
          ContinuousLinearMap.adjoint data.projection +
            ContinuousLinearMap.adjoint data.graphCoordinate := by
      exact ContinuousLinearMap.adjoint.map_add _ _
    have hprojection_adjoint :
        ContinuousLinearMap.adjoint data.projection = data.projection :=
      data.projection_selfAdjoint
    have hprojection_idempotent :
        data.projection * data.projection = data.projection := by
      simpa only [ContinuousLinearMap.mul_def] using
        data.projection_idempotent
    rw [hstar, hprojection_adjoint]
    calc
      (data.projection + ContinuousLinearMap.adjoint data.graphCoordinate) *
            (data.projection + data.graphCoordinate) =
          data.projection * data.projection +
            data.projection * data.graphCoordinate +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.projection +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.graphCoordinate := by
        noncomm_ring
      _ = data.projection +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.graphCoordinate := by
        rw [hprojection_idempotent,
          data.projection_mul_graphCoordinate,
          data.graphCoordinate_adjoint_mul_projection]
        simp
  have hgram_le :
      ContinuousLinearMap.adjoint
          (data.projection + data.graphCoordinate) *
        (data.projection + data.graphCoordinate) ≤
      ContinuousLinearMap.id ℂ K +
        ContinuousLinearMap.adjoint data.graphCoordinate *
          data.graphCoordinate := by
    rw [hgram]
    have hprojection_le : data.projection ≤
        ContinuousLinearMap.id ℂ K := by
      simpa only [ContinuousLinearMap.one_def] using hprojection.le_one
    exact add_le_add_left hprojection_le _
  have hcosine_nonneg : 0 ≤ data.graphCosine := by
    unfold ProjectedUnitaryColligation.graphCosine
    exact CFC.rpow_nonneg
  have hcosine_self : IsSelfAdjoint data.graphCosine :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp
      hcosine_nonneg |>.isSelfAdjoint
  have hgram_nonneg :
      0 ≤ ContinuousLinearMap.adjoint data.graphCoordinate *
        data.graphCoordinate :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self data.graphCoordinate)
  have hgram_strictly_positive :
      IsStrictlyPositive
        (ContinuousLinearMap.id ℂ K +
          ContinuousLinearMap.adjoint data.graphCoordinate *
            data.graphCoordinate) := by
    exact IsStrictlyPositive.add_nonneg isStrictlyPositive_one hgram_nonneg
  have hconjugated :
      data.graphCosine *
          (ContinuousLinearMap.adjoint
            (data.projection + data.graphCoordinate) *
              (data.projection + data.graphCoordinate)) *
            data.graphCosine ≤
      data.graphCosine *
          (ContinuousLinearMap.id ℂ K +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.graphCoordinate) * data.graphCosine :=
    hcosine_self.conjugate_le_conjugate hgram_le
  have hcosine_gram :
      data.graphCosine *
          (ContinuousLinearMap.id ℂ K +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.graphCoordinate) * data.graphCosine =
        ContinuousLinearMap.id ℂ K := by
    change
      (ContinuousLinearMap.id ℂ K +
          ContinuousLinearMap.adjoint data.graphCoordinate *
            data.graphCoordinate) ^ (-1 / 2 : ℝ) *
          (ContinuousLinearMap.id ℂ K +
            ContinuousLinearMap.adjoint data.graphCoordinate *
              data.graphCoordinate) *
        (ContinuousLinearMap.id ℂ K +
          ContinuousLinearMap.adjoint data.graphCoordinate *
            data.graphCoordinate) ^ (-1 / 2 : ℝ) =
        1
    convert CFC.conjugate_rpow_neg_one_half
      (ContinuousLinearMap.id ℂ K +
        ContinuousLinearMap.adjoint data.graphCoordinate *
        data.graphCoordinate) hgram_strictly_positive using 1;
      norm_num
  rw [hcosine_gram] at hconjugated
  have hcontract :
      (ContinuousLinearMap.adjoint
          ((data.projection + data.graphCoordinate) ∘L
            data.graphCosine)) ∘L
        ((data.projection + data.graphCoordinate) ∘L
          data.graphCosine) ≤ ContinuousLinearMap.id ℂ K := by
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp,
      hcosine_self.adjoint_eq, mul_assoc] using hconjugated
  exact norm_le_one_of_adjoint_comp_self_le_id _ hcontract

theorem ProjectedUnitaryColligation.schurFrame_eq_projection_comp_euler_comp_graphFrame
    (data : ProjectedUnitaryColligation (K →L[ℂ] K)) (cosine : K →L[ℂ] K) :
    data.schurFrame cosine =
      data.projection *
          (1 - data.scalar * data.transport) *
            (data.projection + data.graphCoordinate) * cosine := by
  have hleft := data.graphCoordinate_left_complement
  have hzero := data.projection_mul_graphCoordinate
  have hscalar_projection :
      data.projection * data.scalar = data.scalar * data.projection := by
    exact (data.scalar_central data.projection).symm
  have htransport_graph :
      data.projection * data.transport * data.graphCoordinate =
        (data.projection * data.transport *
          complement data.projection) * data.graphCoordinate := by
    calc
      data.projection * data.transport * data.graphCoordinate =
          data.projection * data.transport *
            (complement data.projection * data.graphCoordinate) := by
        rw [hleft]
      _ = (data.projection * data.transport *
            complement data.projection) * data.graphCoordinate := by
        noncomm_ring
  have hscalar_transport_projection :
      data.projection * data.scalar * data.transport * data.projection =
        data.scalar * (data.projection * data.transport *
          data.projection) := by
    rw [hscalar_projection]
    noncomm_ring
  have hscalar_transport_graph :
      data.projection * data.scalar * data.transport *
          data.graphCoordinate =
        data.scalar *
          (data.projection * data.transport *
            complement data.projection) * data.graphCoordinate := by
    calc
      data.projection * data.scalar * data.transport *
            data.graphCoordinate =
          data.scalar *
            (data.projection * data.transport *
              data.graphCoordinate) := by
        rw [hscalar_projection]
        noncomm_ring
      _ = data.scalar *
            (data.projection * data.transport *
              complement data.projection) * data.graphCoordinate := by
        rw [htransport_graph]
        noncomm_ring
  unfold ProjectedUnitaryColligation.schurFrame
    ProjectedUnitaryColligation.graphTransfer
    ProjectedUnitaryColligation.U00
    ProjectedUnitaryColligation.U01
  calc
    (data.projection - data.scalar *
          (data.projection * data.transport * data.projection +
            (data.projection * data.transport *
              complement data.projection) *
              data.graphCoordinate)) * cosine =
        (data.projection *
          (1 - data.scalar * data.transport) *
            (data.projection + data.graphCoordinate)) * cosine := by
      congr 1
      symm
      calc
        data.projection *
              (1 - data.scalar * data.transport) *
                (data.projection + data.graphCoordinate) =
            data.projection * data.projection +
              data.projection * data.graphCoordinate -
              data.projection * data.scalar * data.transport *
                data.projection -
              data.projection * data.scalar * data.transport *
                data.graphCoordinate := by
          noncomm_ring
        _ = data.projection - data.scalar *
              (data.projection * data.transport * data.projection +
                (data.projection * data.transport *
                  complement data.projection) *
                  data.graphCoordinate) := by
          rw [data.projection_idempotent, hzero,
            hscalar_transport_projection, hscalar_transport_graph]
          noncomm_ring

end Generic

section Concrete

theorem PrimeEulerProjectedJuliaInput.schurFrame_eq_euler_comp_graphFrame
    (data : PrimeEulerProjectedJuliaInput) :
    data.toColligation.schurFrame data.toColligation.graphCosine =
      data.projection *
          (ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap *
            (data.projection + data.toColligation.graphCoordinate) *
              data.toColligation.graphCosine := by
  have hgeneric :=
    ProjectedUnitaryColligation.schurFrame_eq_projection_comp_euler_comp_graphFrame
      data.toColligation data.toColligation.graphCosine
  have htransport :
      (1 - data.toColligation.scalar * data.toColligation.transport) =
        (ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    change (1 - data.toColligation.scalar *
        data.toColligation.transport) u =
      ccm24PrimeEulerTransportEquiv data.prime u
    rw [ccm24PrimeEulerTransportEquiv_apply]
    simp only [PrimeEulerProjectedJuliaInput.toColligation,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rfl
  rw [htransport] at hgeneric
  exact hgeneric

theorem PrimeEulerProjectedJuliaInput.normalizedSchurFrame_norm_le_one
    (data : PrimeEulerProjectedJuliaInput) :
    ‖data.normalizedSchurFrame‖ ≤ 1 := by
  have hdenom : 0 < 1 + ccm24PrimeEulerCoefficient data.prime := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (ccm24PrimeEulerCoefficient_nonneg data.prime)
  have hscalar :
      ‖((1 + (ccm24PrimeEulerCoefficient data.prime : ℂ))⁻¹)‖ =
        (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ := by
    have hcast :
        (1 + (ccm24PrimeEulerCoefficient data.prime : ℂ)) =
          ((1 + ccm24PrimeEulerCoefficient data.prime : ℝ) : ℂ) := by
      norm_num
    rw [norm_inv, hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenom]
  have hprojection : IsStarProjection data.projection := by
    refine
      { isIdempotentElem := by
          simpa only [ContinuousLinearMap.mul_def] using
            data.projection_idempotent
        isSelfAdjoint := by
          simpa only [ContinuousLinearMap.star_eq_adjoint] using
            data.projection_selfAdjoint }
  have hprojection_norm : ‖data.projection‖ ≤ 1 :=
    IsStarProjection.norm_le _ hprojection
  have htransport :
      ‖(ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap‖ ≤
        1 + ccm24PrimeEulerCoefficient data.prime := by
    apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt hdenom)
    intro u
    change ‖ccm24PrimeEulerTransportEquiv data.prime u‖ ≤
      (1 + ccm24PrimeEulerCoefficient data.prime) * ‖u‖
    exact CCM24FiniteSTransportBounds.primeEulerTransport_upper_bound
      data.prime u
  have hgraph :
      ‖(data.projection + data.toColligation.graphCoordinate) ∘L
          data.toColligation.graphCosine‖ ≤ 1 :=
    data.toColligation.graphFrame_norm_le_one
  have hframe :
      ‖data.toColligation.schurFrame data.toColligation.graphCosine‖ ≤
        1 + ccm24PrimeEulerCoefficient data.prime := by
    rw [data.schurFrame_eq_euler_comp_graphFrame]
    calc
      ‖data.projection *
          (ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap *
            ((data.projection + data.toColligation.graphCoordinate) ∘L
              data.toColligation.graphCosine)‖ ≤
          ‖data.projection *
              (ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap‖ *
            ‖((data.projection + data.toColligation.graphCoordinate) ∘L
              data.toColligation.graphCosine)‖ := by
        simpa only [ContinuousLinearMap.mul_def] using
          (ContinuousLinearMap.opNorm_comp_le
            (data.projection *
              (ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap)
            ((data.projection + data.toColligation.graphCoordinate) ∘L
              data.toColligation.graphCosine))
      _ ≤ (‖data.projection‖ *
            ‖(ccm24PrimeEulerTransportEquiv data.prime).toContinuousLinearMap‖) *
            ‖((data.projection + data.toColligation.graphCoordinate) ∘L
              data.toColligation.graphCosine)‖ := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 * (1 + ccm24PrimeEulerCoefficient data.prime)) * 1 := by
        gcongr
      _ = 1 + ccm24PrimeEulerCoefficient data.prime := by ring
  rw [PrimeEulerProjectedJuliaInput.normalizedSchurFrame,
    primeEulerSchurNormalizer]
  calc
    ‖((1 + (ccm24PrimeEulerCoefficient data.prime : ℂ))⁻¹ •
        ContinuousLinearMap.id ℂ _) ∘L
          data.toColligation.schurFrame data.toColligation.graphCosine‖ ≤
        ‖((1 + (ccm24PrimeEulerCoefficient data.prime : ℂ))⁻¹ •
            ContinuousLinearMap.id ℂ _)‖ *
          ‖data.toColligation.schurFrame data.toColligation.graphCosine‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖((1 + (ccm24PrimeEulerCoefficient data.prime : ℂ))⁻¹)‖ *
          ‖ContinuousLinearMap.id ℂ _‖ *
          ‖data.toColligation.schurFrame data.toColligation.graphCosine‖ := by
      rw [norm_smul]
    _ ≤ (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ *
          (1 + ccm24PrimeEulerCoefficient data.prime) := by
      rw [hscalar]
      have hid : ‖ContinuousLinearMap.id ℂ
          CC20Concrete.cc20GlobalLogCrossingL2‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      have hinv : 0 ≤
          (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ :=
        (inv_nonneg.mpr (le_of_lt hdenom))
      calc
        (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ *
              ‖ContinuousLinearMap.id ℂ
                CC20Concrete.cc20GlobalLogCrossingL2‖ *
              ‖data.toColligation.schurFrame
                data.toColligation.graphCosine‖ ≤
            (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ *
              1 * ‖data.toColligation.schurFrame
                data.toColligation.graphCosine‖ := by
          gcongr
        _ ≤ (1 + ccm24PrimeEulerCoefficient data.prime)⁻¹ *
              (1 + ccm24PrimeEulerCoefficient data.prime) := by
          simpa only [mul_one, one_mul] using
            (mul_le_mul_of_nonneg_left hframe hinv)
    _ = 1 := by field_simp [ne_of_gt hdenom]

theorem PrimeEulerProjectedJuliaInput.normalizedSchurFrame_contract
    (data : PrimeEulerProjectedJuliaInput) :
    ContinuousLinearMap.adjoint data.normalizedSchurFrame ∘L
        data.normalizedSchurFrame ≤
      ContinuousLinearMap.id ℂ _ :=
  CCM24FiniteSJuliaBessel.adjoint_comp_self_le_id_of_norm_le_one
    data.normalizedSchurFrame
    data.normalizedSchurFrame_norm_le_one

end Concrete

end CCM24FiniteSJuliaSchur
end CCM25Concrete
end Source
end ConnesWeilRH
