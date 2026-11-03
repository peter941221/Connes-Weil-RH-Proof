import ConnesWeilRH.Dev.C1RouteARationalCellBump3287
import ConnesWeilRH.Dev.C1RouteARationalFamily3282

namespace ConnesWeilRH.Dev

def ratCellFamilyRect3288 (index : ℕ) (family : Fin 30) : RatRect3276 :=
  RatRect3276.mul
    (RatRect3276.mul (ratCoefficientRect3282 family)
      (ratRealRect3281 (ratCellBumpInterval3287 index family)))
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)) 9)

theorem ratRect_mul_zero_real3288 (rect : RatRect3276) :
    RatRect3276.mul rect (ratRealRect3281 ({ lo := 0, hi := 0 } : RatInterval3276)) =
      ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) := by
  cases rect
  norm_num [RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
    RatInterval3276.add, ratRealRect3281]

theorem ratRect_zero_mul3288 (rect : RatRect3276) :
    RatRect3276.mul
        ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) rect =
      ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) := by
  cases rect
  norm_num [RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
    RatInterval3276.add]

theorem ratCanonicalFamilyRect_mem3288
    {index : ℕ} (hindex : index < 40960) (family : Fin 30) :
    (ratCellFamilyRect3288 index family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family)
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index)) := by
  by_cases hactive : |record2680Center3212 index| <
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2
  · exact ratCanonicalFamilyRect_mem3282 hindex family hactive
      (ratCellBumpInterval_mem3287 family hindex)
  · have hbump : ratCellBumpInterval3287 index family =
        ({ lo := 0, hi := 0 } : RatInterval3276) := by
      dsimp [ratCellBumpInterval3287]
      have hactiveRat : ¬ |record2680CenterRat3279 index| <
          storedWidthRat3287 family ^ 2 := by
        intro h
        apply hactive
        have hreal : (|record2680CenterRat3279 index| : ℝ) <
            (storedWidthRat3287 family ^ 2 : ℝ) := by
          exact_mod_cast h
        simpa [Rat.cast_abs, Rat.cast_pow, record2680CenterRat_cast3279,
          storedWidthRat_cast3287] using hreal
      simp [hactiveRat]
    unfold ratCellFamilyRect3288
    rw [hbump]
    have hzero : C1RouteAOwnerScaleAudit.widthBump
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index) = 0 := by
      rw [C1RouteAOwnerScaleAudit.widthBump, if_neg hactive]
    rw [ratRect_mul_zero_real3288, ratRect_zero_mul3288]
    unfold RatRect3276.Mem RatRect3276.toReal ComplexRect2427.Mem
    dsimp
    rw [externalFamilyValue2344, if_neg hactive]
    norm_num

end ConnesWeilRH.Dev
