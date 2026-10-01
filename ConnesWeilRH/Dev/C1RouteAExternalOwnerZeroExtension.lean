import ConnesWeilRH.Dev.C1RouteAExternalOwnerDerivatives

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def familySecondValue2346 (coefficient : ℂ) (modulation radius position : ℝ) : ℂ :=
  if |position| < radius then
    externalFamilyValue2344 coefficient modulation radius position *
      familySecondFactor2345 modulation radius position
  else 0

theorem externalFamilyValue2344_contDiff (coefficient : ℂ) (modulation radius : ℝ)
    (hradius : 0 < radius) :
    ContDiff ℝ ∞ (externalFamilyValue2344 coefficient modulation radius) := by
  have heq : externalFamilyValue2344 coefficient modulation radius =
      (fun position => coefficient * (widthBump radius position : ℂ) *
        Complex.exp ((modulation * position : ℝ) * Complex.I)) := by
    funext position
    exact externalFamilyValue2344_eq_familyTerm _ _ _ _
  rw [heq]
  exact familyTerm_contDiff coefficient modulation radius hradius

theorem externalFamilyValue2344_secondDerivative_strictOutside
    (coefficient : ℂ) (modulation radius position : ℝ) (houtside : radius < |position|) :
    deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position = 0 := by
  have heq : externalFamilyValue2344 coefficient modulation radius =ᶠ[𝓝 position]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) houtside]
      with coordinate hcoordinate
    simp [externalFamilyValue2344, not_lt.mpr hcoordinate.le]
  rw [heq.deriv.deriv_eq]
  simp

theorem externalFamilyValue2344_secondDerivative_outside
    (coefficient : ℂ) (modulation radius position : ℝ) (hradius : 0 < radius)
    (houtside : radius ≤ |position|) :
    deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position = 0 := by
  let second := deriv (deriv (externalFamilyValue2344 coefficient modulation radius))
  have hcontinuous : Continuous second :=
    (ContDiff.deriv' ((externalFamilyValue2344_contDiff coefficient modulation radius hradius).of_le
      (by decide : (2 : WithTop (WithTop ℕ)) ≤ ∞))).continuous_deriv
      (by decide : (1 : WithTop (WithTop ℕ)) ≤ (1 : WithTop (WithTop ℕ)))
  have hclosed : IsClosed {coordinate | second coordinate = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hright : Set.Ici radius ⊆ {coordinate | second coordinate = 0} := by
    rw [← closure_Ioi]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    exact externalFamilyValue2344_secondDerivative_strictOutside coefficient modulation radius
      coordinate (lt_of_lt_of_le hcoordinate (le_abs_self coordinate))
  have hleft : Set.Iic (-radius) ⊆ {coordinate | second coordinate = 0} := by
    rw [← closure_Iio]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    apply externalFamilyValue2344_secondDerivative_strictOutside coefficient modulation radius
    change coordinate < -radius at hcoordinate
    have habs := neg_le_abs coordinate
    linarith
  rcases le_abs.mp houtside with hposition | hposition
  · exact hright hposition
  · apply hleft
    change position ≤ -radius
    linarith

theorem externalFamilyValue2344_secondDerivative_global
    (coefficient : ℂ) (modulation radius position : ℝ) (hradius : 0 < radius) :
    deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position =
      familySecondValue2346 coefficient modulation radius position := by
  by_cases hinside : |position| < radius
  · rw [familySecondValue2346, if_pos hinside]
    exact externalFamilyValue2344_secondDerivative_inside coefficient modulation hradius hinside
  · rw [familySecondValue2346, if_neg hinside]
    exact externalFamilyValue2344_secondDerivative_outside coefficient modulation radius position
      hradius (not_lt.mp hinside)

theorem externalPhysical2344_secondDerivative_global
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (position : ℝ) :
    deriv (deriv (externalPhysical2344 coefficients modulations)) position =
      ∑ index : Fin 30, familySecondValue2346 (coefficients index) (modulations index)
        (storedWidth index ^ 2) position := by
  let family := fun index : Fin 30 =>
    externalFamilyValue2344 (coefficients index) (modulations index) (storedWidth index ^ 2)
  have hsmooth : ∀ index, ContDiff ℝ ∞ (family index) := fun index =>
    externalFamilyValue2344_contDiff _ _ _ (pow_pos (storedWidth_pos index) 2)
  have hderivSmooth : ∀ index, ContDiff ℝ (1 : WithTop (WithTop ℕ)) (deriv (family index)) :=
    fun index => ContDiff.deriv' ((hsmooth index).of_le
      (by decide : (1 + 1 : WithTop (WithTop ℕ)) ≤ ∞))
  have hfirst : deriv (externalPhysical2344 coefficients modulations) =
      fun coordinate => ∑ index : Fin 30, deriv (family index) coordinate := by
    funext coordinate
    exact (HasDerivAt.sum (u := Finset.univ) (fun index _ =>
      ((hsmooth index).differentiable (by decide)).differentiableAt.hasDerivAt)).deriv
  rw [hfirst]
  rw [deriv_fun_sum (fun index _ =>
    ((hderivSmooth index).differentiable (by decide)).differentiableAt)]
  apply Finset.sum_congr rfl
  intro index _
  exact externalFamilyValue2344_secondDerivative_global _ _ _ _
    (pow_pos (storedWidth_pos index) 2)

theorem correctedPhysical_secondDerivative_global2346
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (position : ℝ) :
    deriv (deriv (correctedPhysical coefficients modulations)) position =
      ∑ index : Fin 30, familySecondValue2346 (coefficients index) (modulations index)
        (storedWidth index ^ 2) position := by
  rw [← externalPhysical2344_eq_correctedPhysical]
  exact externalPhysical2344_secondDerivative_global coefficients modulations position

end ConnesWeilRH.Dev
