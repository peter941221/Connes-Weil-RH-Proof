import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped Topology BigOperators Matrix
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

noncomputable def momentFamily2351 (modulations : Fin 30 → ℝ) (index : Fin 30) : ℝ → ℂ :=
  externalFamilyValue2344 1 (modulations index) (storedWidth index ^ 2)

noncomputable def momentEntry2351 (modulations : Fin 30 → ℝ) (index : Fin 30)
    (node : ℂ) : ℂ :=
  ∫ position : ℝ, Complex.exp (node * (position : ℂ)) * momentFamily2351 modulations index position

noncomputable def ownerMomentMatrix2351 (modulations : Fin 30 → ℝ)
    (nodes : Fin 30 → ℂ) : Matrix (Fin 30) (Fin 30) ℂ :=
  fun row column => momentEntry2351 modulations column (nodes row)

noncomputable def ownerMomentSolution2351 (modulations : Fin 30 → ℝ)
    (nodes target : Fin 30 → ℂ) : Fin 30 → ℂ :=
  (ownerMomentMatrix2351 modulations nodes)⁻¹ *ᵥ target

theorem momentFamily2351_hasCompactSupport (modulations : Fin 30 → ℝ) (index : Fin 30) :
    HasCompactSupport (momentFamily2351 modulations index) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(storedWidth index ^ 2)) (storedWidth index ^ 2)) isCompact_Icc
  intro position hposition
  have hinside : |position| < storedWidth index ^ 2 := by
    by_contra houtside
    exact hposition (by simp [momentFamily2351, externalFamilyValue2344, houtside])
  exact ⟨(abs_lt.mp hinside).1.le, (abs_lt.mp hinside).2.le⟩

theorem momentIntegrand2351_integrable (modulations : Fin 30 → ℝ)
    (index : Fin 30) (node : ℂ) :
    Integrable (fun position : ℝ =>
      Complex.exp (node * (position : ℂ)) * momentFamily2351 modulations index position) := by
  have hweight : Continuous (fun position : ℝ => Complex.exp (node * (position : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.ofRealCLM.continuous)
  have hfamily : Continuous (momentFamily2351 modulations index) :=
    (externalFamilyValue2344_contDiff 1 _ _ (pow_pos (storedWidth_pos index) 2)).continuous
  exact (hweight.mul hfamily).integrable_of_hasCompactSupport
    (momentFamily2351_hasCompactSupport modulations index).mul_left

theorem correctedPhysical_laplaceAt_mulVec2351
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (nodes : Fin 30 → ℂ) (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest coefficients modulations) (nodes row) =
      (ownerMomentMatrix2351 modulations nodes *ᵥ coefficients) row := by
  unfold laplaceAt
  simp only [exponentialWeight_apply]
  change (∫ position : ℝ, Complex.exp (nodes row * (position : ℂ)) *
    (correctedPhysicalCompactLogTest coefficients modulations).test position) = _
  rw [correctedPhysicalCompactLogTest_toFun]
  have hsum : (fun position : ℝ => Complex.exp (nodes row * (position : ℂ)) *
      correctedPhysical coefficients modulations position) =
      (fun position : ℝ => ∑ index : Fin 30, coefficients index *
        (Complex.exp (nodes row * (position : ℂ)) *
          momentFamily2351 modulations index position)) := by
    funext position
    unfold correctedPhysical physicalFamilySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    simp only [momentFamily2351, externalFamilyValue2344_eq_familyTerm, one_mul]
    ring
  rw [hsum, integral_finsetSum _ (fun index _ =>
    (momentIntegrand2351_integrable modulations index (nodes row)).const_mul (coefficients index))]
  simp only [integral_const_mul, ownerMomentMatrix2351, Matrix.mulVec, dotProduct, momentEntry2351]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem ownerMomentSolution2351_mulVec (modulations : Fin 30 → ℝ)
    (nodes target : Fin 30 → ℂ) (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det) :
    ownerMomentMatrix2351 modulations nodes *ᵥ ownerMomentSolution2351 modulations nodes target =
      target := by
  unfold ownerMomentSolution2351
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem ownerMomentSolution2351_realizes (modulations : Fin 30 → ℝ)
    (nodes target : Fin 30 → ℂ) (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      (ownerMomentSolution2351 modulations nodes target) modulations) (nodes row) = target row := by
  rw [correctedPhysical_laplaceAt_mulVec2351, ownerMomentSolution2351_mulVec _ _ _ hdet]

theorem ownerMomentSolution2351_unique (modulations : Fin 30 → ℝ)
    (nodes target : Fin 30 → ℂ) (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det)
    (coefficients : Fin 30 → ℂ)
    (hvalues : ∀ row : Fin 30,
      laplaceAt (correctedPhysicalCompactLogTest coefficients modulations) (nodes row) =
        target row) :
    coefficients = ownerMomentSolution2351 modulations nodes target := by
  have hmatrix : ownerMomentMatrix2351 modulations nodes *ᵥ coefficients = target := by
    funext row
    rw [← correctedPhysical_laplaceAt_mulVec2351]
    exact hvalues row
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  exact hmatrix.trans (ownerMomentSolution2351_mulVec _ _ _ hdet).symm

theorem existsUnique_actualOwnerMomentCoefficients2351 (modulations : Fin 30 → ℝ)
    (nodes target : Fin 30 → ℂ) (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det) :
    ∃! coefficients : Fin 30 → ℂ, ∀ row : Fin 30,
      laplaceAt (correctedPhysicalCompactLogTest coefficients modulations) (nodes row) =
        target row := by
  exact ⟨ownerMomentSolution2351 modulations nodes target,
    ownerMomentSolution2351_realizes _ _ _ hdet,
    fun coefficients hvalues => ownerMomentSolution2351_unique _ _ _ hdet coefficients hvalues⟩

end ConnesWeilRH.Dev
