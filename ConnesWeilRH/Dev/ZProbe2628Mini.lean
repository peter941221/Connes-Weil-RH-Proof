import ConnesWeilRH.Dev.ZProbe2628Integrability
import ConnesWeilRH.Dev.C1RouteAMomentActualEdge2620
import ConnesWeilRH.Dev.C1RouteAMomentActualPanel2622Panel000
import ConnesWeilRH.Dev.C1RouteAMomentActualPanel2622Panel001

namespace ConnesWeilRH.Dev

open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

-- [P5] mini partition rehearsal over panels 000-001
theorem probeMiniPartition2628 :
    |(storedWidth 0 ^ 2) *
        ((∫ position in (-1 : ℝ)..(-(22 / 25 : ℝ)),
            realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
              position) +
          (∫ position in (9 / 10 : ℝ)..1,
            realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
              position)) -
      (((momentPanelIntegralCenter2622P000 +
          momentPanelIntegralCenter2622P001 : ℚ) : ℝ))| ≤
      (((2 : ℚ) / 10 ^ 68 +
        ((1 : ℚ) / 10 ^ 73 + (1 : ℚ) / 10 ^ 73) : ℚ) : ℝ) := by
  have hcast : ((momentPanelIntegralCenter2622P000 +
      momentPanelIntegralCenter2622P001 : ℚ) : ℝ) =
    ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ) +
      ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ) := by
    simp [Rat.cast_add]
  rw [hcast]
  have hint := probeIntervalIntegrable2628 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
  have hedge := actualMomentEntry000_bothEdgeCharge_le2620
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (f := realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re)
    (μ := volume) (a := (-1 : ℝ)) (b := (-(9 / 10 : ℝ))) (c := (-(22 / 25 : ℝ)))
    (hint _ _) (hint _ _)
  have hmid : ∑ k ∈ Finset.range 2,
      ∫ position in ((-9 / 10 : ℝ) + k / 100)..((-9 / 10 : ℝ) + (k + 1) / 100),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re position
      = ∫ position in (-(9 / 10) : ℝ)..(-(22 / 25) : ℝ),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
          position := by
    have hstep := intervalIntegral.sum_integral_adjacent_intervals
      (f := realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re)
      (μ := volume) (a := fun p : ℕ => (-9 / 10 : ℝ) + p / 100) (n := 2)
      (by
        intro k hk
        exact hint _ _)
    convert hstep using 1 <;> norm_num
  have hshape : (storedWidth 0 ^ 2) *
      ((∫ position in (-1 : ℝ)..(-(22 / 25 : ℝ)),
          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
            position) +
        (∫ position in (9 / 10 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
            position))
      = (storedWidth 0 ^ 2) *
          ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position) +
            (∫ position in (9 / 10 : ℝ)..1,
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position))
        + (((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ))
          + ((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ)))
        + (((momentPanelIntegralCenter2622P000 : ℚ) : ℝ) +
          ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ)) := by
    rw [← hjoin, ← hmid, mul_add, mul_add, Finset.mul_sum]
    simp only [Finset.sum_range_succ, Finset.sum_empty, zero_add]
    ring
  have hd0 : |(storedWidth 0 ^ 2) *
      (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
          position) -
      ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ)| ≤ (1 : ℝ) / 10 ^ 73 := by
    rw [show ((-9 / 10 : ℝ) + 0 / 100) = -(9 / 10 : ℝ) from by norm_num,
      show ((-9 / 10 : ℝ) + 1 / 100) = -(89 / 100 : ℝ) from by norm_num]
    exact actualMomentPanel000_integral_error_le2622
  have hd1 : |(storedWidth 0 ^ 2) *
      (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
          position) -
      ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ)| ≤ (1 : ℝ) / 10 ^ 73 := by
    rw [show ((-9 / 10 : ℝ) + 1 / 100) = -(89 / 100 : ℝ) from by norm_num,
      show ((-9 / 10 : ℝ) + 2 / 100) = -(22 / 25 : ℝ) from by norm_num]
    exact actualMomentPanel001_integral_error_le2622
  have htri : |(storedWidth 0 ^ 2) *
      ((∫ position in (-1 : ℝ)..(-(22 / 25 : ℝ)),
          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
            position) +
        (∫ position in (9 / 10 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
            position)) -
      (((momentPanelIntegralCenter2622P000 : ℚ) : ℝ) +
        ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ))| ≤
      (2 : ℝ) / 10 ^ 68 + ((1 : ℝ) / 10 ^ 73 + (1 : ℝ) / 10 ^ 73) := by
    rw [hshape]
    have hcancel : (storedWidth 0 ^ 2) *
        ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
            realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
              position) +
          (∫ position in (9 / 10 : ℝ)..1,
            realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
              position))
        + (((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ))
          + ((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ)))
        + (((momentPanelIntegralCenter2622P000 : ℚ) : ℝ) +
          ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ))
        - (((momentPanelIntegralCenter2622P000 : ℚ) : ℝ) +
          ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ))
        = (storedWidth 0 ^ 2) *
          ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position) +
            (∫ position in (9 / 10 : ℝ)..1,
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position))
          + (((storedWidth 0 ^ 2) *
                (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position) -
              ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ))
            + ((storedWidth 0 ^ 2) *
                (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position) -
              ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ))) := by
      ring
    rw [hcancel]
    calc
      |(storedWidth 0 ^ 2) *
          ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position) +
            (∫ position in (9 / 10 : ℝ)..1,
              realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                position)) +
        (((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ)) +
          ((storedWidth 0 ^ 2) *
              (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
                realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                  position) -
            ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ)))|
          ≤ |(storedWidth 0 ^ 2) *
              ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position) +
                (∫ position in (9 / 10 : ℝ)..1,
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position))| +
            |((storedWidth 0 ^ 2) *
                (∫ position in ((-9 / 10 : ℝ) + 0 / 100)..((-9 / 10 : ℝ) + 1 / 100),
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position) -
              ((momentPanelIntegralCenter2622P000 : ℚ) : ℝ)) +
              ((storedWidth 0 ^ 2) *
                (∫ position in ((-9 / 10 : ℝ) + 1 / 100)..((-9 / 10 : ℝ) + 2 / 100),
                  realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re
                    position) -
                ((momentPanelIntegralCenter2622P001 : ℚ) : ℝ))| :=
        abs_add_le _ _
      _ ≤ (2 : ℝ) / 10 ^ 68 + ((1 : ℝ) / 10 ^ 73 + (1 : ℝ) / 10 ^ 73) := by
        exact add_le_add hedge ((abs_add_le _ _).trans (add_le_add hd0 hd1))
  exact htri.trans (by norm_num)

end ConnesWeilRH.Dev
