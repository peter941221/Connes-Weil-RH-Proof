import ConnesWeilRH.Dev.C1RouteAExpIntervalUpper2512
import ConnesWeilRH.Dev.C1RouteAOwnerExpProduction2508

/-! Record 2514: production exponential upper at a safe strip cell.

The endpoint ratio controls the derivative factors, the lower cell ratio
controls the bump exponent, and the 2508 Taylor envelope supplies the
certified replacement exponential.  This is a pointwise panel consumer; it
does not yet assemble the cell remainder ladder.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def ownerProductionExpUpper2514
    (index : ℕ) (i : Fin 30) : ℝ :=
  expNegOneUpper2498 ^
      (⌊30 /
        (1 - (ownerCellLowerRatio2501 stripRadius2303
          (stripRadius2303 / 320) index i) ^ 2)⌋₊ : ℕ) *
    (expTaylor20
        (30 /
          (1 - (ownerCellLowerRatio2501 stripRadius2303
            (stripRadius2303 / 320) index i) ^ 2) -
          (⌊30 /
            (1 - (ownerCellLowerRatio2501 stripRadius2303
              (stripRadius2303 / 320) index i) ^ 2)⌋₊ : ℕ)) +
      expTaylor20Error)

theorem ownerPanelProductionExpUpper_safeCell2514
    (sigma x : ℝ) (index : ℕ) (hlo : 196 ≤ index) (hhi : index ≤ 443)
    (hcoordinate : x ∈ Set.Icc
      (-stripRadius2303 + index * (stripRadius2303 / 320))
      (-stripRadius2303 + (index + 1) * (stripRadius2303 / 320))) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
        ((|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|) *
          ownerProductionExpUpper2514 index i)
        ((|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|) *
          ownerProductionExpUpper2514 index i *
          (60 * ownerCellEndpointRatio2488 stripRadius2303
            (stripRadius2303 / 320) index i *
            (1 - (ownerCellEndpointRatio2488 stripRadius2303
              (stripRadius2303 / 320) index i) ^ 2)⁻¹ ^ 2 /
            ownerRad_2463 i + |ownerMod_2463 i|))
        ((|(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|) *
          ownerProductionExpUpper2514 index i *
          ((60 * ((1 - (ownerCellEndpointRatio2488 stripRadius2303
              (stripRadius2303 / 320) index i) ^ 2)⁻¹ ^ 2 +
              4 * (ownerCellEndpointRatio2488 stripRadius2303
                (stripRadius2303 / 320) index i) ^ 2 *
                (1 - (ownerCellEndpointRatio2488 stripRadius2303
                  (stripRadius2303 / 320) index i) ^ 2)⁻¹ ^ 3) /
              (ownerRad_2463 i) ^ 2) +
            (60 * ownerCellEndpointRatio2488 stripRadius2303
              (stripRadius2303 / 320) index i *
              (1 - (ownerCellEndpointRatio2488 stripRadius2303
                (stripRadius2303 / 320) index i) ^ 2)⁻¹ ^ 2 /
              ownerRad_2463 i) ^ 2 + (ownerMod_2463 i) ^ 2 +
            2 * |ownerMod_2463 i| *
              (60 * ownerCellEndpointRatio2488 stripRadius2303
                (stripRadius2303 / 320) index i *
                (1 - (ownerCellEndpointRatio2488 stripRadius2303
                  (stripRadius2303 / 320) index i) ^ 2)⁻¹ ^ 2 /
                ownerRad_2463 i))) := by
  let t : Fin 30 → ℝ := fun i =>
    ownerCellEndpointRatio2488 stripRadius2303 (stripRadius2303 / 320) index i
  let a : Fin 30 → ℝ := fun i =>
    ownerCellLowerRatio2501 stripRadius2303 (stripRadius2303 / 320) index i
  let coefficientBound : Fin 30 → ℝ := fun i =>
    |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|
  let upper : Fin 30 → ℝ := fun i => ownerProductionExpUpper2514 index i
  apply ownerPanelWeightedSecondDeriv_le_sumIntervalExpUpper_auto2513
    sigma x t a coefficientBound upper
  · intro i
    have hs := (ownerCellSafeEndpoint_true_iff2488 stripRadius2303
      (stripRadius2303 / 320) index).mp
      (ownerCellSafeEndpoint_production2488 hlo hhi)
    have hmax := abs_le_max_abs_endpoints_of_mem_Icc2488 hcoordinate
    exact lt_of_le_of_lt hmax (max_lt (hs i).1 (hs i).2)
  · intro i
    exact ownerCellEndpointRatio_nonneg2488 stripRadius2303
      (stripRadius2303 / 320) index i
  · intro i
    have hs := (ownerCellSafeEndpoint_true_iff2488 stripRadius2303
      (stripRadius2303 / 320) index).mp
      (ownerCellSafeEndpoint_production2488 hlo hhi)
    exact ownerCellEndpointRatio_lt_one2488 stripRadius2303
      (stripRadius2303 / 320) index i (hs i).1 (hs i).2
  · intro i
    exact (ownerCoordinateNormalizedBound_of_endpointBound2488
      (fun j => ownerCellEndpointRatio2488 stripRadius2303
        (stripRadius2303 / 320) index j) hcoordinate
      (fun j => ownerCellEndpointRatio_endpointBound2488 stripRadius2303
        (stripRadius2303 / 320) index j)) i
  · intro i
    exact ownerCellLowerRatio_nonneg2501 stripRadius2303
      (stripRadius2303 / 320) index i
  · intro i
    exact ownerCellLowerRatio_lt_one_production2507 hlo hhi i
  · intro i
    have hstep : 0 ≤ stripRadius2303 / 320 := by
      norm_num [stripRadius2303]
    exact ownerCellLowerRatio_le_normalizedAbs2501 i
      (ownerRadPos_2465 i) hstep hcoordinate
  · intro i
    exact Complex.norm_le_abs_re_add_abs_im _
  · intro i
    simpa [t, a, coefficientBound, upper,
      ownerProductionExpUpper2514, neg_div] using
      ownerCellExpSplitUpper_production2508 hlo hhi i

end ConnesWeilRH.Dev
