/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDefectOrder

/-!
# R3 leakage defect: telescoping against alternating powers

The positive leakage defect is `p - T`, where `p` is the doubled-shift
radial projection and `T = p * q * p` is the alternating product.  The
projection absorptions on both sides imply that, after the first step, this
defect is exactly the adjacent power difference `T^(n+1) - T^(n+2)`.

This is an operator identity on the actual finite-S carrier.  It does not
assert Hilbert--Schmidt smoothing for the selected root times the defect.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open scoped ComplexConjugate InnerProductSpace

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct_pow_succ
    (b : ℝ) (n : ℕ) :
    doubledShiftRadialProjection b *
        (doubledShiftAlternatingProduct b) ^ (n + 1) =
      (doubledShiftAlternatingProduct b) ^ (n + 1) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_add, pow_one] using
        doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct b
  | succ n ih =>
      change doubledShiftRadialProjection b *
          (doubledShiftAlternatingProduct b) ^ ((n + 1) + 1) =
        (doubledShiftAlternatingProduct b) ^ ((n + 1) + 1)
      calc
        doubledShiftRadialProjection b *
            (doubledShiftAlternatingProduct b) ^ ((n + 1) + 1) =
          doubledShiftRadialProjection b *
            (doubledShiftAlternatingProduct b *
              (doubledShiftAlternatingProduct b) ^ (n + 1)) := by
                rw [pow_succ']
        _ = (doubledShiftRadialProjection b *
              doubledShiftAlternatingProduct b) *
                (doubledShiftAlternatingProduct b) ^ (n + 1) := by
                  rw [mul_assoc]
        _ = doubledShiftAlternatingProduct b *
              (doubledShiftAlternatingProduct b) ^ (n + 1) := by
                rw [doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct]
        _ = (doubledShiftAlternatingProduct b) ^ ((n + 1) + 1) := by
          exact (pow_succ' (doubledShiftAlternatingProduct b) (n + 1)).symm

theorem doubledShiftRadialProjection_sub_alternatingProduct_comp_pow_succ
    (b : ℝ) (n : ℕ) :
    (doubledShiftRadialProjection b - doubledShiftAlternatingProduct b) *
        (doubledShiftAlternatingProduct b) ^ (n + 1) =
      (doubledShiftAlternatingProduct b) ^ (n + 1) -
        (doubledShiftAlternatingProduct b) ^ (n + 2) := by
  have hp := doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct_pow_succ
    b n
  calc
    (doubledShiftRadialProjection b - doubledShiftAlternatingProduct b) *
        (doubledShiftAlternatingProduct b) ^ (n + 1) =
      doubledShiftRadialProjection b *
          (doubledShiftAlternatingProduct b) ^ (n + 1) -
        doubledShiftAlternatingProduct b *
          (doubledShiftAlternatingProduct b) ^ (n + 1) := by
            rw [sub_mul]
    _ = (doubledShiftAlternatingProduct b) ^ (n + 1) -
        (doubledShiftAlternatingProduct b) ^ (n + 2) := by
          rw [hp]
          rw [show (doubledShiftAlternatingProduct b) ^ (n + 2) =
                doubledShiftAlternatingProduct b *
                  (doubledShiftAlternatingProduct b) ^ (n + 1) by
            simpa only [show n + 2 = (n + 1) + 1 by omega] using
              pow_succ' (doubledShiftAlternatingProduct b) (n + 1)]

theorem doubledShiftAlternatingProduct_pow_succ_comp_radialProjection
    (b : ℝ) (n : ℕ) :
    (doubledShiftAlternatingProduct b) ^ (n + 1) *
        doubledShiftRadialProjection b =
      (doubledShiftAlternatingProduct b) ^ (n + 1) := by
  exact doubledShiftAlternatingProduct_pow_right_radialProjection b n

theorem doubledShiftAlternatingProduct_pow_succ_comp_sub_defect
    (b : ℝ) (n : ℕ) :
    (doubledShiftAlternatingProduct b) ^ (n + 1) *
        (doubledShiftRadialProjection b - doubledShiftAlternatingProduct b) =
      (doubledShiftAlternatingProduct b) ^ (n + 1) -
        (doubledShiftAlternatingProduct b) ^ (n + 2) := by
  have hp := doubledShiftAlternatingProduct_pow_succ_comp_radialProjection b n
  calc
    (doubledShiftAlternatingProduct b) ^ (n + 1) *
          (doubledShiftRadialProjection b -
            doubledShiftAlternatingProduct b) =
        (doubledShiftAlternatingProduct b) ^ (n + 1) *
            doubledShiftRadialProjection b -
          (doubledShiftAlternatingProduct b) ^ (n + 1) *
            doubledShiftAlternatingProduct b := by
              rw [mul_sub]
    _ = (doubledShiftAlternatingProduct b) ^ (n + 1) -
        (doubledShiftAlternatingProduct b) ^ (n + 2) := by
      rw [hp]
      rw [show (doubledShiftAlternatingProduct b) ^ (n + 2) =
            (doubledShiftAlternatingProduct b) ^ (n + 1) *
              doubledShiftAlternatingProduct b by
        simpa only [show n + 2 = (n + 1) + 1 by omega] using
          pow_succ (doubledShiftAlternatingProduct b) (n + 1)]

theorem doubledShiftRadialProjection_sub_alternatingProduct_apply_pow_succ_eq_step
  (b : ℝ) (n : ℕ) (v : Carrier) :
    ((doubledShiftRadialProjection b - doubledShiftAlternatingProduct b) *
        (doubledShiftAlternatingProduct b) ^ (n + 1)) v =
      ((doubledShiftAlternatingProduct b) ^ (n + 1) -
        (doubledShiftAlternatingProduct b) ^ (n + 2)) v := by
  simpa only [ContinuousLinearMap.mul_apply] using
    congrArg (fun L : Op => L v)
      (doubledShiftRadialProjection_sub_alternatingProduct_comp_pow_succ b n)

end Dev
end ConnesWeilRH
