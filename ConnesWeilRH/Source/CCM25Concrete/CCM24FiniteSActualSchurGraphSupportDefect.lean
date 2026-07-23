/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurForwardPhysicalDifference

/-!
# Graph-support defect in the actual Schur readback

The Euler graph equations do not justify silently assuming that the graph
cosine is supported by the projected carrier.  This module names the exact
complementary support defect and proves its algebraic contribution to the
Schur frame and inverse-Euler readback.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphSupportDefect

open CCM24FiniteSJuliaSchur

/-! ## Exact graph support defect -/

def graphSupportDefect
    {A : Type*} [Ring A] [StarRing A]
    (data : ProjectedUnitaryColligation A) (cosine : A) : A :=
  complement data.projection * cosine

theorem eulerGraphAction_on_graphFrame_eq_schur_add_graphSupportDefect
    {A : Type*} [Ring A] [StarRing A]
    (data : ProjectedUnitaryColligation A) (cosine : A) :
    data.eulerGraphAction cosine (data.graphSine cosine) =
      (data.schurFrame cosine + graphSupportDefect data cosine, 0) := by
  apply Prod.ext
  · unfold ProjectedUnitaryColligation.eulerGraphAction
    unfold ProjectedUnitaryColligation.schurFrame
      ProjectedUnitaryColligation.graphTransfer
      ProjectedUnitaryColligation.graphSine graphSupportDefect complement
    noncomm_ring
  · exact data.graphSine_lower_equation cosine

theorem eulerTransport_on_projectedGraphFrame_eq_schurFrame
    {A : Type*} [Ring A] [StarRing A]
    (data : ProjectedUnitaryColligation A) (cosine : A) :
    (1 - data.scalar * data.transport) *
        (data.projection * cosine + data.graphSine cosine) =
      data.schurFrame cosine := by
  have hU01_projection : data.U01 * data.projection = 0 := by
    unfold ProjectedUnitaryColligation.U01
    calc
      (data.projection * data.transport * complement data.projection) *
          data.projection =
        data.projection * data.transport *
          (complement data.projection * data.projection) := by
            noncomm_ring
      _ = 0 := by
        rw [data.complement_mul_projection]
        simp
  have hU11_projection : data.U11 * data.projection = 0 := by
    unfold ProjectedUnitaryColligation.U11
    calc
      (complement data.projection * data.transport *
          complement data.projection) * data.projection =
        complement data.projection * data.transport *
          (complement data.projection * data.projection) := by
            noncomm_ring
      _ = 0 := by
        rw [data.complement_mul_projection]
        simp
  have hprojection_resolvent :
      data.projection * data.resolvent = 0 := by
    calc
      data.projection * data.resolvent =
          data.projection *
            (complement data.projection * data.resolvent) := by
              rw [data.resolvent_left_support]
      _ = (data.projection * complement data.projection) *
          data.resolvent := by
            noncomm_ring
      _ = 0 := by
        rw [data.projection_mul_complement]
        simp
  have hprojection_graphCoordinate :
      data.projection * data.graphCoordinate = 0 := by
    unfold ProjectedUnitaryColligation.graphCoordinate
    calc
      data.projection *
          (data.scalar * data.resolvent * data.U10) =
        (data.projection * data.scalar) * data.resolvent * data.U10 := by
          noncomm_ring
      _ = (data.scalar * data.projection) * data.resolvent * data.U10 := by
        rw [data.scalar_central data.projection]
      _ = data.scalar *
          (data.projection * data.resolvent) * data.U10 := by
            noncomm_ring
      _ = 0 := by
        rw [hprojection_resolvent]
        simp
  have hprojection_graphSine :
      data.projection * data.graphSine cosine = 0 := by
    unfold ProjectedUnitaryColligation.graphSine
    calc
      data.projection * (data.graphCoordinate * cosine) =
          (data.projection * data.graphCoordinate) * cosine := by
            noncomm_ring
      _ = 0 := by
        rw [hprojection_graphCoordinate]
        simp
  have hU00_graphSine : data.U00 * data.graphSine cosine = 0 := by
    calc
      data.U00 * data.graphSine cosine =
          (data.U00 * data.projection) * data.graphSine cosine := by
            rw [data.U00_mul_projection]
      _ = data.U00 *
          (data.projection * data.graphSine cosine) := by
            noncomm_ring
      _ = 0 := by
        rw [hprojection_graphSine]
        simp
  have hU10_graphSine : data.U10 * data.graphSine cosine = 0 := by
    calc
      data.U10 * data.graphSine cosine =
          (data.U10 * data.projection) * data.graphSine cosine := by
            rw [data.U10_mul_projection]
      _ = data.U10 *
          (data.projection * data.graphSine cosine) := by
            noncomm_ring
      _ = 0 := by
        rw [hprojection_graphSine]
        simp
  have hU00_projection :
      data.U00 * (data.projection * cosine) = data.U00 * cosine := by
    calc
      data.U00 * (data.projection * cosine) =
          (data.U00 * data.projection) * cosine := by
            noncomm_ring
      _ = data.U00 * cosine := by
        rw [data.U00_mul_projection]
  have hU10_projection :
      data.U10 * (data.projection * cosine) = data.U10 * cosine := by
    calc
      data.U10 * (data.projection * cosine) =
          (data.U10 * data.projection) * cosine := by
            noncomm_ring
      _ = data.U10 * cosine := by
        rw [data.U10_mul_projection]
  have hU01_projection_cosine :
      data.U01 * (data.projection * cosine) = 0 := by
    calc
      data.U01 * (data.projection * cosine) =
          (data.U01 * data.projection) * cosine := by
            noncomm_ring
      _ = 0 := by
        rw [hU01_projection]
        simp
  have hU11_projection_cosine :
      data.U11 * (data.projection * cosine) = 0 := by
    calc
      data.U11 * (data.projection * cosine) =
          (data.U11 * data.projection) * cosine := by
            noncomm_ring
      _ = 0 := by
        rw [hU11_projection]
        simp
  have htransport_apply :
      data.transport *
          (data.projection * cosine + data.graphSine cosine) =
        data.U00 * cosine + data.U01 * data.graphSine cosine +
          data.U10 * cosine + data.U11 * data.graphSine cosine := by
    rw [data.transport_eq_sum_corners]
    calc
      (data.U00 + data.U01 + data.U10 + data.U11) *
          (data.projection * cosine + data.graphSine cosine) =
        (data.U00 * (data.projection * cosine) +
            data.U00 * data.graphSine cosine) +
          (data.U01 * (data.projection * cosine) +
            data.U01 * data.graphSine cosine) +
          (data.U10 * (data.projection * cosine) +
            data.U10 * data.graphSine cosine) +
          (data.U11 * (data.projection * cosine) +
            data.U11 * data.graphSine cosine) := by
              noncomm_ring
      _ = data.U00 * cosine + data.U01 * data.graphSine cosine +
          data.U10 * cosine + data.U11 * data.graphSine cosine := by
            rw [hU00_projection, hU00_graphSine,
              hU01_projection_cosine, hU10_projection,
              hU10_graphSine, hU11_projection_cosine]
            simp
  calc
    (1 - data.scalar * data.transport) *
        (data.projection * cosine + data.graphSine cosine) =
      data.projection * cosine + data.graphSine cosine -
        data.scalar * (data.transport *
          (data.projection * cosine + data.graphSine cosine)) := by
            noncomm_ring
    _ = data.projection * cosine + data.graphSine cosine -
        data.scalar * (data.U00 * cosine +
          data.U01 * data.graphSine cosine + data.U10 * cosine +
          data.U11 * data.graphSine cosine) := by
      rw [htransport_apply]
    _ = (data.projection * cosine - data.scalar *
          (data.U00 * cosine + data.U01 * data.graphSine cosine)) +
        (data.graphSine cosine - data.scalar *
          (data.U10 * cosine +
            complement data.projection * data.transport *
              complement data.projection * data.graphSine cosine)) := by
      unfold ProjectedUnitaryColligation.U11
      noncomm_ring
    _ = data.schurFrame cosine := by
      have hlower := data.graphSine_lower_equation cosine
      rw [hlower]
      simp only [add_zero]
      unfold ProjectedUnitaryColligation.schurFrame
        ProjectedUnitaryColligation.graphTransfer
        ProjectedUnitaryColligation.graphSine
      noncomm_ring

/-! ## Inverse-Euler readback -/

theorem inverse_on_schurFrame_eq_graphFrame_sub_supportDefect
    {A : Type*} [Ring A] [StarRing A]
    (data : ProjectedUnitaryColligation A) (cosine : A)
    (inverse : A)
    (hinverse : inverse *
        (1 - data.scalar * data.transport) = 1) :
    inverse * data.schurFrame cosine =
      cosine + data.graphSine cosine -
        graphSupportDefect data cosine := by
  have htransport :=
    eulerTransport_on_projectedGraphFrame_eq_schurFrame data cosine
  calc
    inverse * data.schurFrame cosine =
        inverse * ((1 - data.scalar * data.transport) *
          (data.projection * cosine + data.graphSine cosine)) := by
      rw [htransport]
    _ = (inverse * (1 - data.scalar * data.transport)) *
          (data.projection * cosine + data.graphSine cosine) := by
      rw [← mul_assoc]
    _ = data.projection * cosine + data.graphSine cosine := by
      rw [hinverse, one_mul]
    _ = cosine + data.graphSine cosine -
          graphSupportDefect data cosine := by
      unfold graphSupportDefect complement
      noncomm_ring

end CCM24FiniteSActualSchurGraphSupportDefect
end CCM25Concrete
end Source
end ConnesWeilRH
