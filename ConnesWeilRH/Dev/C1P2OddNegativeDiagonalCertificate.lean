import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1P2EvenOddGateDecomposition
import ConnesWeilRH.Dev.C1HealthyDetectorEvenOddPair

/-!
# P2 odd negative diagonal certificate

The narrow Archimedean budget applies directly to an odd owner.  If its
convolution square stays inside the open log-2 window and has positive mass,
then the complete same-owner gate is strictly negative because the visible
prime sum vanishes.  This is the parity-compatible negative diagonal socket
for the even/odd two-span consumer; nodal and detector-preservation data are
separate obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2OddNegativeDiagonalCertificate

open C1LaneRNarrowArch
open C1P2EvenOddGateDecomposition
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open Set

theorem odd_ICgate_neg_of_narrow_budget
    (g : CompactLogTest)
    (hodd : ∀ x : ℝ, g.test (-x) = -g.test x)
    (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1) (hRlog2 : R < Real.log 2)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Ioo (-R) R)
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) < 0)
    (hmass : 0 < (g.convolutionSquare.test 0).re) :
    ICgate g.convolutionSquare < 0 := by
  have harch := archimedeanTerm_neg_of_narrow_budget
    g R hRpos hRlt hsupport hbudget hmass
  have hopen : Function.support g.convolutionSquare.test ⊆
      Ioo (-Real.log 2) (Real.log 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlower, hupper⟩
    constructor <;> linarith
  have hprime := finitePrimeSum_eq_zero_of_support_subset_open_log_two
    g.convolutionSquare hopen
  unfold ICgate
  rw [hprime]
  simpa using harch

private theorem oddPart_test_ne_zero_of_asymmetric_laplace_data
    (h : CompactLogTest) (rho : ℂ)
    (hrho : CompactLogTest.laplaceAt h rho = 1)
    (hneg : CompactLogTest.laplaceAt h (-rho) = -1) :
    (C1HealthyDetectorEvenOddPair.oddPart h).test ≠ 0 := by
  intro hzero
  have hzeroLap :
      CompactLogTest.laplaceAt
          (C1HealthyDetectorEvenOddPair.oddPart h) rho = 0 := by
    simp [CompactLogTest.laplaceAt,
      CompactLogTest.exponentialWeight_apply, hzero]
  rw [C1HealthyDetectorEvenOddPair.laplaceAt_oddPart,
    C1HealthyDetectorEvenOddPair.laplaceAt_reflection, hrho, hneg] at hzeroLap
  norm_num at hzeroLap

private theorem convolutionSquare_mass_pos_of_test_ne_zero
    (g : CompactLogTest) (hg : g.test ≠ 0) :
    0 < (g.convolutionSquare.test 0).re := by
  rw [g.convolutionSquare_zero_eq_integral_normSq]
  have hpoint : ∃ x : ℝ, g.test x ≠ 0 := by
    by_contra! hpoint
    apply hg
    ext x
    exact hpoint x
  obtain ⟨x, hx⟩ := hpoint
  have hcont : Continuous
      (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_normSq.comp g.test.continuous
  have hcompact : HasCompactSupport
      (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      g.compactSupport.comp_left (by simp)
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (f_cont := hcont)
    (f_int := hcont.integrable_of_hasCompactSupport hcompact)
    (f_nonneg := fun y => Complex.normSq_nonneg (g.test y))
    (f_x := (Complex.normSq_pos.mpr hx).ne')

theorem oddPart_negative_gate_of_symmetric_node_data
    (h : CompactLogTest) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1) (hRlog2 : R < Real.log 2)
    (hsupport : Function.support h.test ⊆ Set.Ioo (-(R / 2)) (R / 2))
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) < 0)
    (rho : ℂ)
    (hrho : CompactLogTest.laplaceAt h rho = 1)
    (hneg : CompactLogTest.laplaceAt h (-rho) = -1)
    (hhalf : CompactLogTest.laplaceAt h (1 / 2 : ℂ) =
      CompactLogTest.laplaceAt h (-(1 / 2 : ℂ)))
    (hone : CompactLogTest.laplaceAt h 1 =
      CompactLogTest.laplaceAt h (-1)) :
    (∀ x : ℝ,
        (C1HealthyDetectorEvenOddPair.oddPart h).test (-x) =
          -(C1HealthyDetectorEvenOddPair.oddPart h).test x) ∧
      CompactLogTest.laplaceAt (C1HealthyDetectorEvenOddPair.oddPart h)
          (1 / 2 : ℂ) = 0 ∧
      CompactLogTest.laplaceAt (C1HealthyDetectorEvenOddPair.oddPart h) 1 = 0 ∧
      CompactLogTest.laplaceAt (C1HealthyDetectorEvenOddPair.oddPart h) rho ≠ 0 ∧
      ICgate (C1HealthyDetectorEvenOddPair.oddPart h).convolutionSquare < 0 := by
  let g := C1HealthyDetectorEvenOddPair.oddPart h
  have hgodd : ∀ x : ℝ, g.test (-x) = -g.test x := by
    exact C1HealthyDetectorEvenOddPair.test_neg_oddPart h
  have hgsupport : Function.support g.test ⊆ Set.Icc (-(R / 2)) (R / 2) := by
    exact C1HealthyDetectorEvenOddPair.support_oddPart_subset_Icc h (R / 2)
      hsupport
  have hsq : Function.support g.convolutionSquare.test ⊆ Set.Ioo (-R) R := by
    have hsq' := CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo
      g hgsupport
    intro x hx
    rcases hsq' hx with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hmass : 0 < (g.convolutionSquare.test 0).re := by
    apply convolutionSquare_mass_pos_of_test_ne_zero
    exact oddPart_test_ne_zero_of_asymmetric_laplace_data h rho hrho hneg
  have hgate := odd_ICgate_neg_of_narrow_budget g hgodd R hRpos hRlt hRlog2
    hsq hbudget hmass
  have hhalf' : CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 := by
    rw [C1HealthyDetectorEvenOddPair.laplaceAt_oddPart,
      C1HealthyDetectorEvenOddPair.laplaceAt_reflection, hhalf]
    ring
  have hone' : CompactLogTest.laplaceAt g 1 = 0 := by
    rw [C1HealthyDetectorEvenOddPair.laplaceAt_oddPart,
      C1HealthyDetectorEvenOddPair.laplaceAt_reflection, hone]
    ring
  have hdet : CompactLogTest.laplaceAt g rho ≠ 0 := by
    rw [C1HealthyDetectorEvenOddPair.laplaceAt_oddPart,
      C1HealthyDetectorEvenOddPair.laplaceAt_reflection, hrho, hneg]
    norm_num
  exact ⟨hgodd, hhalf', hone', hdet, hgate⟩

theorem exists_odd_negative_diagonal_of_offLineZero
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ g : CompactLogTest,
      (∀ x : ℝ, g.test (-x) = -g.test x) ∧
        CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 ∧
        CompactLogTest.laplaceAt g 1 = 0 ∧
        CompactLogTest.laplaceAt g rho ≠ 0 ∧
        ICgate g.convolutionSquare < 0 := by
  have hRpos : 0 < narrowArchRadius := narrowArchRadius_pos
  have hRlt : narrowArchRadius < 1 := narrowArchRadius_lt_one
  have hRlog2 : narrowArchRadius < Real.log 2 := by
    have hexp : narrowArchRadius < Real.exp (-4) := by
      rw [narrowArchRadius]
      apply Real.exp_lt_exp.mpr
      nlinarith [narrowArchCoefficient_pos]
    have hhalf : Real.exp (-4) < (1 / 2 : ℝ) := by
      rw [← Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      nlinarith [Real.log_two_lt_d9]
    exact lt_trans hexp (lt_trans hhalf (by nlinarith [Real.log_two_gt_d9]))
  have hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + narrowArchRadius -
          (1 / 2 : ℝ) * Real.log (1 / narrowArchRadius) < 0 := by
    simpa [narrowArchCoefficient] using narrowArchRadius_budget_lt
  rcases C1HealthyDetectorEvenOddPair.exists_pairNode_correction_of_offLineZero
      hrho hoff (lower := -(narrowArchRadius / 2))
      (upper := narrowArchRadius / 2) (by linarith) (by linarith) with
    ⟨h, hsupport, hrho1, hneg1, _hzero, hhalf, hnhalf, hone, hnone⟩
  have hhalfEq : CompactLogTest.laplaceAt h (1 / 2 : ℂ) =
      CompactLogTest.laplaceAt h (-(1 / 2 : ℂ)) := hhalf.trans hnhalf.symm
  have honeEq : CompactLogTest.laplaceAt h 1 =
      CompactLogTest.laplaceAt h (-1) := hone.trans hnone.symm
  have hresult := oddPart_negative_gate_of_symmetric_node_data h narrowArchRadius
    hRpos hRlt hRlog2 hsupport hbudget rho hrho1 hneg1 hhalfEq honeEq
  rcases hresult with ⟨hgodd, hghalf, hgone, hdetect, hgate⟩
  exact ⟨C1HealthyDetectorEvenOddPair.oddPart h,
    hgodd, hghalf, hgone, hdetect, hgate⟩

end C1P2OddNegativeDiagonalCertificate
end Source
end ConnesWeilRH
