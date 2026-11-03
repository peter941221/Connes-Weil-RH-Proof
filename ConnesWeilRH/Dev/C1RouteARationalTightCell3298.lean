import ConnesWeilRH.Dev.C1RouteARationalRealProjection3298
import ConnesWeilRH.Dev.C1RouteARationalCellWeight3289

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def ratRealIntervalSum3298 {α : Type*}
    (rect : α → RatInterval3276) (s : Finset α) : RatInterval3276 :=
  { lo := ∑ i ∈ s, (rect i).lo
    hi := ∑ i ∈ s, (rect i).hi }

theorem ratRealIntervalSum_mem3298 {α : Type*}
    {rect : α → RatInterval3276} {term : α → ℝ} {s : Finset α}
    (hterm : ∀ i ∈ s, (rect i).Mem (term i)) :
    (ratRealIntervalSum3298 rect s).Mem (∑ i ∈ s, term i) := by
  unfold ratRealIntervalSum3298 RatInterval3276.Mem
    RatInterval3276.toReal RealInterval2429.Mem
  dsimp
  simp only [Rat.cast_sum]
  constructor
  · exact Finset.sum_le_sum fun i hi => by
      have h := hterm i hi
      change (rect i).lo ≤ term i ∧ term i ≤ (rect i).hi at h
      exact h.1
  · exact Finset.sum_le_sum fun i hi => by
      have h := hterm i hi
      change (rect i).lo ≤ term i ∧ term i ≤ (rect i).hi at h
      exact h.2

theorem ratInterval_zero_mul3298 (rect : RatInterval3276) :
    RatInterval3276.mul ({ lo := 0, hi := 0 } : RatInterval3276) rect =
      ({ lo := 0, hi := 0 } : RatInterval3276) := by
  cases rect
  norm_num [RatInterval3276.mul]

def ratCellRealFamilyInterval3298 (index : ℕ) (family : Fin 30) : RatInterval3276 :=
  ratRealFamilyInterval3298
    (ratCoefficientRect3282 family)
    (RatRect3276.powSq
      (ratPhaseRect3279 (record2680PhaseAngleRat3279 index family)) 9)
    (ratCellBumpInterval3298 index family)

theorem ratCellRealFamilyInterval_mem3298
    {index : ℕ} (family : Fin 30) (hindex : index < 40960) :
    (ratCellRealFamilyInterval3298 index family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family)
        (storedWidth family ^ 2)
        (record2680Center3212 index)).re := by
  by_cases hactive : |record2680Center3212 index| < storedWidth family ^ 2
  · apply ratRealFamilyInterval_external_mem3298
    · exact ratCoefficientRect_mem3282 family
    · exact record2680CanonicalPhasePowRect_mem3279 hindex family hactive
    · exact ratCellBumpInterval_mem3298 family hindex
  · have hbump : ratCellBumpInterval3298 index family =
        ({ lo := 0, hi := 0 } : RatInterval3276) := by
      dsimp [ratCellBumpInterval3298]
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
    unfold ratCellRealFamilyInterval3298 ratRealFamilyInterval3298
    rw [hbump]
    rw [ratInterval_zero_mul3298]
    unfold RatInterval3276.Mem RatInterval3276.toReal RealInterval2429.Mem
    dsimp
    rw [externalFamilyValue2344, if_neg hactive]
    norm_num

def ratCellRealSum3298 (index : ℕ) : RatInterval3276 :=
  ratRealIntervalSum3298
    (ratCellRealFamilyInterval3298 index) Finset.univ

theorem ratCellRealSum_mem3298
    {index : ℕ} (hindex : index < 40960) :
    (ratCellRealSum3298 index).Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index)).re := by
  unfold ratCellRealSum3298
  have hsum := ratRealIntervalSum_mem3298
    (s := (Finset.univ : Finset (Fin 30)))
    (rect := ratCellRealFamilyInterval3298 index)
    (term := fun family =>
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 index)).re)
    (by intro family _; exact ratCellRealFamilyInterval_mem3298 family hindex)
  simpa [externalPhysical2344] using hsum

def ratCellValueUpperTight3298 (index : ℕ) : ℝ :=
  (RatInterval3276.mul
    (ratCellWeightInterval3289 index)
    (ratCellRealSum3298 index)).hi

theorem ratCellValueUpperTight3298_spec
    {index : ℕ} (hindex : index < 40960) :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 index) ≤
      ratCellValueUpperTight3298 index := by
  have hweight := ratCellWeightInterval_mem3289 hindex
  have hsum := ratCellRealSum_mem3298 hindex
  unfold ratCellValueUpperTight3298 weightedExternal3201
  have hmul := RatInterval3276.mem_mul hweight hsum
  change _ ≤ ((RatInterval3276.mul
    (ratCellWeightInterval3289 index)
    (ratCellRealSum3298 index)).hi : ℝ)
  convert hmul.2 using 1 <;> norm_num <;> ring

end ConnesWeilRH.Dev
