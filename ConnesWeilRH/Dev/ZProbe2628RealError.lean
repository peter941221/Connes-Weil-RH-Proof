import ConnesWeilRH.Dev.ZProbe2628CenterSum
import ConnesWeilRH.Dev.C1RouteAMomentActualEdge2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open MeasureTheory

theorem actualGlobalRealError2628 :
    |(storedWidth 0 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
          (capturedNodes2584 0).re x) -
      ((totalCenters2628 : ℚ) : ℝ)| ≤
      ((2 : ℚ) / 10 ^ 68 +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) := by
  have hsum := panelIntegrals2628_sum_eq_global
  have hcenter := partitionCentersSum2628
  have herr := panelErrorSum2628
  have heps := probeEpsReplay2628
  calc
    |(storedWidth 0 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
          (capturedNodes2584 0).re x) -
        ((totalCenters2628 : ℚ) : ℝ)| =
      |∑ p ∈ Finset.range 180,
        (panelIntegral2628 p - (partitionCenter2628 p : ℝ))| := by
      rw [← hsum, ← hcenter]
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := herr
    _ ≤ ((2 : ℚ) / 10 ^ 68 +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) := by
      norm_num

theorem actualFullRealError2628 :
    |(storedWidth 0 ^ 2) * (∫ x in (-1 : ℝ)..1,
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
          (capturedNodes2584 0).re x) -
      ((totalCenters2628 : ℚ) : ℝ)| ≤
      ((2 : ℚ) / 10 ^ 68 +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) := by
  let f : ℝ → ℝ := realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
    (capturedNodes2584 0).re
  have hleft := probeIntervalIntegrable2628 (storedWidth 0 ^ 2)
    (capturedNodes2584 0).re (-1) (-(9 / 10 : ℝ))
  have hmid := probeIntervalIntegrable2628 (storedWidth 0 ^ 2)
    (capturedNodes2584 0).re (-(9 / 10 : ℝ)) (9 / 10)
  have hright := probeIntervalIntegrable2628 (storedWidth 0 ^ 2)
    (capturedNodes2584 0).re (9 / 10) 1
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hmid hright
  have houter := intervalIntegral.integral_add_adjacent_intervals hleft
    (probeIntervalIntegrable2628 (storedWidth 0 ^ 2)
      (capturedNodes2584 0).re (-(9 / 10 : ℝ)) 1)
  have hedge := actualMomentEntry000_bothEdgeCharge_le2620
  have hpanel :
      |(storedWidth 0 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628 : ℚ) : ℝ)| ≤
        ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := by
    have hpanel0 :
        |(storedWidth 0 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),
            realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)
              (capturedNodes2584 0).re x) -
            ((totalCenters2628 : ℚ) : ℝ)| ≤
          ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := by
      rw [← panelIntegrals2628_sum_eq_global, ← partitionCentersSum2628]
      rw [← Finset.sum_sub_distrib]
      exact panelErrorSum2628
    convert hpanel0 using 1 <;> norm_num [f]
  have hdecomp :
      (storedWidth 0 ^ 2) * (∫ x in (-1 : ℝ)..1, f x) -
          ((totalCenters2628 : ℚ) : ℝ) =
        ((storedWidth 0 ^ 2) *
          ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
            (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth 0 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628 : ℚ) : ℝ)) := by
    dsimp [f] at hsplit2 houter ⊢
    rw [← houter, ← hsplit2]
    ring
  rw [hdecomp]
  calc
    |((storedWidth 0 ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))) +
        ((storedWidth 0 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628 : ℚ) : ℝ))| ≤
      |(storedWidth 0 ^ 2) *
        ((∫ x in (-1 : ℝ)..(-(9 / 10 : ℝ)), f x) +
          (∫ x in (9 / 10 : ℝ)..1, f x))| +
        |(storedWidth 0 ^ 2) * (∫ x in (-(9 / 10 : ℝ))..(9 / 10 : ℝ), f x) -
          ((totalCenters2628 : ℚ) : ℝ)| := abs_add_le _ _
    _ ≤ (2 : ℝ) / 10 ^ 68 +
           ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := by
      exact add_le_add hedge hpanel
    _ = ((2 : ℚ) / 10 ^ 68 +
        ∑ p ∈ Finset.range 180, (1 : ℚ) / 10 ^ dec2628 p : ℚ) := by
      norm_num

end ConnesWeilRH.Dev
