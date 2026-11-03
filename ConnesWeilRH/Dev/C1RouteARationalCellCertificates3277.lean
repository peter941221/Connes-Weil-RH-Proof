import ConnesWeilRH.Dev.C1RouteARationalManifest3276
import ConnesWeilRH.Dev.C1RouteAConcreteOwner40960AggregateUpper3213

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-!
This module is the finite-cell certificate interface for the Route A midpoint
upper bound.  A certificate contains only rational endpoint data.  The two
containment hypotheses remain explicit: this prevents a JSON sidecar or an
unverified numeral from being treated as a theorem.
-/

def ratCellWeightRect3277 (weight : RatInterval3276) : RatRect3276 :=
  { reLo := weight.lo
    reHi := weight.hi
    imLo := 0
    imHi := 0 }

def ratCellValueUpper3277 (weight : RatInterval3276)
    (aggregate : RatRect3276) : ℝ :=
  (RatRect3276.mul (ratCellWeightRect3277 weight) aggregate).toReal.reHi

theorem ratCellValueUpper3277_spec
    {sigma x : ℝ} {weight : RatInterval3276} {aggregate : RatRect3276}
    (hweight : weight.Mem (Real.exp (sigma * x)))
    (haggregate : aggregate.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x)) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
        capturedModulations2584 x ≤ ratCellValueUpper3277 weight aggregate := by
  exact weightedExternal_le_rat_rect_reHi3276 hweight haggregate

theorem ratCellValueUpper3277_family_spec
    {sigma x : ℝ} {weight : RatInterval3276}
    {rect : Fin 30 → RatRect3276}
    (hweight : weight.Mem (Real.exp (sigma * x)))
    (hrect : ∀ family,
      (rect family).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2) x)) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
        capturedModulations2584 x ≤
      ratCellValueUpper3277 weight
        (RatRect3276.sumFinset rect Finset.univ) := by
  exact weightedExternal_le_rat_family_rect_reHi3276 hweight hrect

theorem record2680_40960_midpoint_upper_of_rat_cell_certificates3277
    {weight : ℕ → RatInterval3276}
    {familyRect : ℕ → Fin 30 → RatRect3276}
    (hweight : ∀ index < 40960,
      (weight index).Mem
        (Real.exp (-(1 / 2 : ℝ) * record2680Center3212 index)))
    (hfamilyRect : ∀ index < 40960, ∀ family,
      (familyRect index family).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2)
          (record2680Center3212 index))) :
    ∀ index < 40960,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤
      ratCellValueUpper3277 (weight index)
        (RatRect3276.sumFinset (familyRect index) Finset.univ) := by
  intro index hindex
  apply ratCellValueUpper3277_family_spec
  · have hw := hweight index hindex
    convert hw using 1 <;> ring
  · intro family
    exact hfamilyRect index hindex family

theorem intervalIntegral_record2680_40960_global_aggregate_upper_of_rat_cell_certificates3277
    {weight : ℕ → RatInterval3276}
    {familyRect : ℕ → Fin 30 → RatRect3276}
    {secondUpper fourthUpper sixthBound : ℕ → ℝ}
    (hweight : ∀ index < 40960,
      (weight index).Mem
        (Real.exp (-(1 / 2 : ℝ) * record2680Center3212 index)))
    (hfamilyRect : ∀ index < 40960, ∀ family,
      (familyRect index family).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient family)
          (capturedModulations2584 family) (storedWidth family ^ 2)
          (record2680Center3212 index)))
    (hsecond : ∀ index < 40960,
      iteratedDeriv 2
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ secondUpper index)
    (hfourth : ∀ index < 40960,
      iteratedDeriv 4
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index) ≤ fourthUpper index)
    (hderiv : ∀ index < 40960, ∀ coordinate,
      ‖iteratedDeriv 6
        (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ ≤ sixthBound index)
    (hsixthBound : ∀ index < 40960, 0 ≤ sixthBound index) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212
          (fun index => ratCellValueUpper3277 (weight index)
            (RatRect3276.sumFinset (familyRect index) Finset.univ))
          secondUpper fourthUpper sixthBound) := by
  apply intervalIntegral_record2680_40960_global_aggregate_upper3213
  · exact record2680_40960_midpoint_upper_of_rat_cell_certificates3277
      hweight hfamilyRect
  · exact hsecond
  · exact hfourth
  · exact hderiv
  · exact hsixthBound

end ConnesWeilRH.Dev
