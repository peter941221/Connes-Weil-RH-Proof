/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability

/-!
# Record 1122: generic archimedean legality for every CompactLogTest

Discharges the per-pair archimedean legality hypothesis that record 1121
booked as a T2-side obligation
(docs/proofs/1122_archimedean_legality_discharge_preregistration.md):
`IntegrableOn (archimedeanIntegrand F) (Ioi 0)` holds for EVERY
`CompactLogTest F` - not just convolution squares.

Mechanism (mirror of `SelectedArchimedeanIntegrability.lean` with the
square dressing removed): continuity on `Ioi 0` (positive denominator),
finiteness at `0+` by L'Hopital on the real and imaginary parts
(numerator `0 = 0` is the identity `2*F 0 - 2*F 0`), and an exponentially
decaying tail beyond the compact support
(`C1SameOwnerWeil.supportRadius` + `support_subset_Icc`).

Payoff: `pairTest_legality` kills the 1121 named hypothesis, and the
`_free` headlines restate `gate_sum_span` / `gate_qform_span` /
`hrep_of_gateMatrix_eq` with the `hI` argument removed.  No sign theorem
and no RH statement is asserted here.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ArchimedeanIntegrabilityGeneric

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open C1GateMatrixRepresentation
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open scoped BigOperators ContDiff

noncomputable section

/-! ## The generic archimedean numerator -/

theorem archimedeanNumerator_contDiff (F : CompactLogTest) :
    ContDiff ℝ ∞ (archimedeanNumerator F) := by
  unfold archimedeanNumerator
  fun_prop

noncomputable def archimedeanNumeratorRe (F : CompactLogTest) (y : ℝ) : ℝ :=
  (archimedeanNumerator F y).re

noncomputable def archimedeanNumeratorIm (F : CompactLogTest) (y : ℝ) : ℝ :=
  (archimedeanNumerator F y).im

theorem archimedeanNumeratorRe_contDiff (F : CompactLogTest) :
    ContDiff ℝ ∞ (archimedeanNumeratorRe F) :=
  Complex.reCLM.contDiff.comp (archimedeanNumerator_contDiff F)

theorem archimedeanNumeratorIm_contDiff (F : CompactLogTest) :
    ContDiff ℝ ∞ (archimedeanNumeratorIm F) :=
  Complex.imCLM.contDiff.comp (archimedeanNumerator_contDiff F)

@[simp] theorem archimedeanNumeratorRe_zero (F : CompactLogTest) :
    archimedeanNumeratorRe F 0 = 0 := by
  simp [archimedeanNumeratorRe]

@[simp] theorem archimedeanNumeratorIm_zero (F : CompactLogTest) :
    archimedeanNumeratorIm F 0 = 0 := by
  simp [archimedeanNumeratorIm]

/-! ## Continuity and the finite limit at `0+` -/

theorem archimedeanIntegrand_continuousOn_Ioi (F : CompactLogTest) :
    ContinuousOn (archimedeanIntegrand F) (Ioi (0 : ℝ)) := by
  intro y hy
  have hnum : ContinuousAt (archimedeanNumerator F) y :=
    (archimedeanNumerator_contDiff F).continuous.continuousAt
  have hden : ContinuousAt
      (fun x : ℝ =>
        ((SelectedWeilSquareOwner.archimedeanDenominator x : ℝ) : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp
      SelectedWeilSquareOwner.archimedeanDenominator_contDiff.continuous.continuousAt
  apply ContinuousAt.continuousWithinAt
  exact hnum.div hden
    (by exact_mod_cast
      (SelectedWeilSquareOwner.archimedeanDenominator_pos hy).ne')

theorem tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT
    (F : CompactLogTest) :
    Tendsto
      (fun y =>
        archimedeanNumeratorRe F y /
          SelectedWeilSquareOwner.archimedeanDenominator y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv (archimedeanNumeratorRe F) 0 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := deriv (archimedeanNumeratorRe F))
    (g' := fun y => Real.exp y + Real.exp (-y))
  · exact Filter.Eventually.of_forall fun y =>
      (((archimedeanNumeratorRe_contDiff F).differentiable (by simp)) y).hasDerivAt
  · exact Filter.Eventually.of_forall
      SelectedWeilSquareOwner.hasDerivAt_archimedeanDenominator
  · exact Filter.Eventually.of_forall
      SelectedWeilSquareOwner.archimedeanDenominator_deriv_ne_zero
  · simpa using
      Filter.Tendsto.mono_left
        (archimedeanNumeratorRe_contDiff F).continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · simpa using
      Filter.Tendsto.mono_left
        SelectedWeilSquareOwner.archimedeanDenominator_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · have hnum :=
      (archimedeanNumeratorRe_contDiff F).continuous_deriv (by simp)
    have hden : Continuous (fun y : ℝ => Real.exp y + Real.exp (-y)) := by
      fun_prop
    simpa only [Pi.div_apply, Real.exp_zero, neg_zero, add_zero,
      one_add_one_eq_two] using
      ((hnum.tendsto 0).div (hden.tendsto 0) (by norm_num)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

theorem tendsto_archimedeanNumeratorIm_div_denominator_nhdsGT
    (F : CompactLogTest) :
    Tendsto
      (fun y =>
        archimedeanNumeratorIm F y /
          SelectedWeilSquareOwner.archimedeanDenominator y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deriv (archimedeanNumeratorIm F) 0 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := deriv (archimedeanNumeratorIm F))
    (g' := fun y => Real.exp y + Real.exp (-y))
  · exact Filter.Eventually.of_forall fun y =>
      (((archimedeanNumeratorIm_contDiff F).differentiable (by simp)) y).hasDerivAt
  · exact Filter.Eventually.of_forall
      SelectedWeilSquareOwner.hasDerivAt_archimedeanDenominator
  · exact Filter.Eventually.of_forall
      SelectedWeilSquareOwner.archimedeanDenominator_deriv_ne_zero
  · simpa using
      Filter.Tendsto.mono_left
        (archimedeanNumeratorIm_contDiff F).continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · simpa using
      Filter.Tendsto.mono_left
        SelectedWeilSquareOwner.archimedeanDenominator_contDiff.continuous.continuousAt.tendsto
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · have hnum :=
      (archimedeanNumeratorIm_contDiff F).continuous_deriv (by simp)
    have hden : Continuous (fun y : ℝ => Real.exp y + Real.exp (-y)) := by
      fun_prop
    simpa only [Pi.div_apply, Real.exp_zero, neg_zero, add_zero,
      one_add_one_eq_two] using
      ((hnum.tendsto 0).div (hden.tendsto 0) (by norm_num)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

/-- The archimedean integrand has a finite limit at `0+` for every compact
log test. -/
noncomputable def archimedeanIntegrandLimit (F : CompactLogTest) : ℂ :=
  (deriv (archimedeanNumeratorRe F) 0 / 2 : ℂ) +
    (deriv (archimedeanNumeratorIm F) 0 / 2 : ℂ) * Complex.I

theorem tendsto_archimedeanIntegrand_nhdsGT (F : CompactLogTest) :
    Tendsto (archimedeanIntegrand F) (𝓝[>] (0 : ℝ))
      (𝓝 (archimedeanIntegrandLimit F)) := by
  have hre := tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT F
  have him := tendsto_archimedeanNumeratorIm_div_denominator_nhdsGT F
  have hre' := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have him' := Complex.continuous_ofReal.continuousAt.tendsto.comp him
  have hsum := hre'.add (him'.mul_const Complex.I)
  convert hsum using 1
  · funext y
    apply Complex.ext <;>
      simp [archimedeanIntegrand, archimedeanNumeratorRe,
        archimedeanNumeratorIm]
  · simp [archimedeanIntegrandLimit]

/-! ## The exponential tail beyond the compact support -/

theorem eventually_archimedeanIntegrand_eq_tail (F : CompactLogTest) :
    ∀ᶠ y in atTop,
      archimedeanIntegrand F y =
        (-2 * F.test 0) * (Real.exp (-y) : ℂ) *
          ((SelectedWeilSquareOwner.archimedeanTailRatio y : ℝ) : ℂ) := by
  filter_upwards [eventually_gt_atTop (max 1 (supportRadius F))] with y hy
  have hy0 : 0 < y :=
    (lt_of_lt_of_le (by norm_num) (le_max_left 1 (supportRadius F))).trans hy
  have hyradius : supportRadius F < |y| := by
    simpa [abs_of_pos hy0] using
      lt_of_le_of_lt (le_max_right 1 (supportRadius F)) hy
  have hyR : supportRadius F < y := by
    have habs : |y| = y := abs_of_pos hy0
    linarith
  have hyzero : F.test y = 0 := by
    by_contra hne
    exact hyR.not_le
      (support_subset_Icc F (Function.mem_support.mpr hne)).2
  have hnegzero : F.test (-y) = 0 := by
    by_contra hne
    have hge := (support_subset_Icc F
      (Function.mem_support.mpr hne)).1
    linarith
  have hden : SelectedWeilSquareOwner.archimedeanDenominator y ≠ 0 :=
    (SelectedWeilSquareOwner.archimedeanDenominator_pos hy0).ne'
  have hexp : Real.exp y ≠ 0 := Real.exp_ne_zero y
  simp only [archimedeanIntegrand, archimedeanNumerator, hyzero, hnegzero,
    add_zero, mul_zero, zero_sub]
  rw [SelectedWeilSquareOwner.archimedeanTailRatio]
  push_cast
  field_simp [hden, hexp, Real.exp_neg]
  have hcexp : Complex.exp (-(y : ℂ)) * Complex.exp (y : ℂ) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [mul_assoc, hcexp, mul_one]

theorem archimedeanIntegrand_isBigO_exp_neg (F : CompactLogTest) :
    archimedeanIntegrand F =O[atTop]
      (fun y : ℝ => (Real.exp (-y) : ℂ)) := by
  have hratio_lt : ∀ᶠ y in atTop,
      SelectedWeilSquareOwner.archimedeanTailRatio y < 2 :=
    (tendsto_order.1
      SelectedWeilSquareOwner.tendsto_archimedeanTailRatio_atTop).2 2
      (by norm_num)
  have hratio_nonneg : ∀ᶠ y in atTop,
      0 ≤ SelectedWeilSquareOwner.archimedeanTailRatio y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact div_nonneg (Real.exp_pos y).le
      (SelectedWeilSquareOwner.archimedeanDenominator_pos hy).le
  apply Asymptotics.IsBigO.of_bound
    (2 * ‖(-2 : ℂ) * F.test 0‖)
  filter_upwards [eventually_archimedeanIntegrand_eq_tail F,
    hratio_lt, hratio_nonneg] with y heq hlt hnonneg
  rw [heq, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-y))]
  have hratio_abs : |SelectedWeilSquareOwner.archimedeanTailRatio y| ≤ 2 := by
    simpa [abs_of_nonneg hnonneg] using hlt.le
  calc
    ‖(-2 : ℂ) * F.test 0‖ * Real.exp (-y) *
          |SelectedWeilSquareOwner.archimedeanTailRatio y|
        ≤ ‖(-2 : ℂ) * F.test 0‖ * Real.exp (-y) * 2 :=
      mul_le_mul_of_nonneg_left hratio_abs
        (mul_nonneg (norm_nonneg _) (Real.exp_pos (-y)).le)
    _ = (2 * ‖(-2 : ℂ) * F.test 0‖) * Real.exp (-y) := by ring

/-! ## The headline -/

/-- Every compact log test carries a legal archimedean integrand. -/
theorem integrableOn_archimedeanIntegrand (F : CompactLogTest) :
    IntegrableOn (archimedeanIntegrand F) (Ioi (0 : ℝ)) := by
  rw [integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin]
  refine ⟨?_, ?_,
    (archimedeanIntegrand_continuousOn_Ioi F).locallyIntegrableOn
      measurableSet_Ioi⟩
  · have hexpReal : IntegrableOn (fun y : ℝ => Real.exp (-1 * y))
        (Ioi (0 : ℝ)) :=
      exp_neg_integrableOn_Ioi 0 (by norm_num)
    have hexpComplex : IntegrableOn (fun y : ℝ => (Real.exp (-y) : ℂ))
        (Ioi (0 : ℝ)) := by
      simpa [Function.comp_def] using
        Complex.ofRealCLM.integrableOn_comp hexpReal
    have hexpFilter : IntegrableAtFilter (fun y : ℝ => (Real.exp (-y) : ℂ))
        atTop :=
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, hexpComplex⟩
    have hmeas : StronglyMeasurableAtFilter (archimedeanIntegrand F) atTop :=
      ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0,
        (archimedeanIntegrand_continuousOn_Ioi F).aestronglyMeasurable
          measurableSet_Ioi⟩
    exact (archimedeanIntegrand_isBigO_exp_neg F).integrableAtFilter hmeas
      hexpFilter
  · have hmeas : StronglyMeasurableAtFilter (archimedeanIntegrand F)
        (𝓝[>] (0 : ℝ)) :=
      (archimedeanIntegrand_continuousOn_Ioi F)
        |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0
    exact (tendsto_archimedeanIntegrand_nhdsGT F).integrableAtFilter hmeas
      (volume.finiteAt_nhdsWithin 0 (Ioi (0 : ℝ)))

/-! ## Payoff: the 1121 named hypothesis, discharged -/

/-- The per-pair archimedean legality booked by record 1121 holds for every
pair of window tests: `pairTest w i j` is itself a `CompactLogTest`. -/
theorem pairTest_legality {k : ℕ} (w : Fin k → CompactLogTest) (i j : Fin k) :
    IntegrableOn (archimedeanIntegrand (pairTest w i j)) (Ioi (0 : ℝ)) :=
  integrableOn_archimedeanIntegrand _

/-- `gate_sum_span` without the legality hypothesis. -/
theorem gate_sum_span_free {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) :
    ICgate ((spanObj w y).convolutionSquare) =
      ∑ p : Fin k × Fin k, y p.1 * y p.2 * ICgate (pairTest w p.1 p.2) :=
  gate_sum_span w y hw (fun i j => pairTest_legality w i j)

/-- `gate_qform_span` without the legality hypothesis. -/
theorem gate_qform_span_free {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (gateMatrix w *ᵥ y) :=
  gate_qform_span w y hw (fun i j => pairTest_legality w i j)

/-- `hrep_of_gateMatrix_eq` without the legality hypothesis: the literal T2
representation slot consumed by the 1118/1119/1120 absolute headlines. -/
theorem hrep_of_gateMatrix_eq_free {k : ℕ} (w : Fin k → CompactLogTest)
    (y : Fin k → ℝ) (M_true : Matrix (Fin k) (Fin k) ℝ)
    (hM : gateMatrix w = M_true) {B : ℝ}
    (hw : ∀ i, Function.support (w i).test ⊆ Ioo (-B) B) :
    ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (M_true *ᵥ y) :=
  hrep_of_gateMatrix_eq w y M_true hM hw (fun i j => pairTest_legality w i j)

end
end C1ArchimedeanIntegrabilityGeneric
end Source
end ConnesWeilRH
