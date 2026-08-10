import ConnesWeilRH.Source.CCM25Concrete.SelectedWeilFormula
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete

open SelectedWeilSquare
open SelectedWeilSquare.SelectedWeilSquareOwner
open CompactLogConvolution

/-- The archimedean coefficient log(4*pi) + gamma is positive. -/
lemma archimedeanCoefficient_pos :
    0 < Real.log (4 * Real.pi) + Real.eulerMascheroniConstant := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h4 : (1 : ℝ) < 4 * Real.pi := by nlinarith
  have hlog : 0 < Real.log (4 * Real.pi) := Real.log_pos h4
  have hgam : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  nlinarith

/-- The real part of the archimedean term splits into the leading positive piece
(proportional to Re((f*f)(0)) = |f|^2) plus the real part of the archimedean
integral. -/
theorem archimedeanTerm_re_eq_lead_add_integral
    (owner : SelectedWeilSquareOwner) :
    (owner.archimedeanTerm).re
      = (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
           (owner.convolutionSquare.test 0).re
        + (∫ y in Ioi (0 : ℝ), owner.archimedeanIntegrand y).re := by
  rw [archimedeanTerm, Complex.add_re]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A complex number with positive real part is nonzero. -/
theorem complex_ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := by
  intro hz
  rw [hz] at h
  norm_num at h

/-- Sufficiency: if the leading positive piece is positive and the absolute value
of the archimedean integral's real part is below it, the archimedean term is
nonzero.  This reduces the whole wall-A 1.4 closure to the single bound hI. -/
theorem archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound
    (owner : SelectedWeilSquareOwner)
    (hA : 0 < (owner.convolutionSquare.test 0).re)
    (hI : |(∫ y in Ioi (0 : ℝ), owner.archimedeanIntegrand y).re|
          < (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
            (owner.convolutionSquare.test 0).re) :
    owner.archimedeanTerm ≠ 0 := by
  apply complex_ne_zero_of_re_pos
  rw [archimedeanTerm_re_eq_lead_add_integral]
  let C : ℝ := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant
  let A : ℝ := (owner.convolutionSquare.test 0).re
  let J : ℝ := (∫ y in Ioi (0 : ℝ), owner.archimedeanIntegrand y).re
  have hCpos : 0 < C := archimedeanCoefficient_pos
  have hApos : 0 < A := hA
  have hJ : |J| < C * A := by simpa [C, A, J] using hI
  have hlos : -(C * A) < J := by simpa using (abs_lt.mp hJ).1
  nlinarith
