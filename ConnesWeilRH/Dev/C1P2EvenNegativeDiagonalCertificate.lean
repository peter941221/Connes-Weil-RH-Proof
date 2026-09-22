import ConnesWeilRH.Dev.C1P2OddNegativeDiagonalCertificate

/-!
# P2 even negative diagonal certificate

The same narrow same-owner gate estimate applies to an even component.  A
finite residual correction with a nonzero auxiliary value at `2` and zeros at
the healthy nodes produces a nonzero even part while leaving the detector
nodes unchanged.  This is the even companion socket for the parity branch.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2EvenNegativeDiagonalCertificate

open C1HealthyDetectorEvenOddPair
open C1LaneRNarrowArch
open C1LocalConfigurationDomination
open C1P2OddNegativeDiagonalCertificate
open C1SameOwnerWeil
open C1
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open Set

noncomputable def evenNodeSet (rho : ℂ) : Finset ℂ :=
  {rho, -rho, 0, 1 / 2, -(1 / 2 : ℂ), 1, -1, 2, -2}

noncomputable def evenNodeTarget (rho : ℂ)
    (z : FiniteMellinNode (evenNodeSet rho)) : ℂ :=
  if z.1 = 2 then 1 else 0

private theorem rho_ne_two
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ 2 := by
  intro h
  have hlt := sourceNontrivialZero_re_lt_one hrho
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith

private theorem neg_rho_ne_two
    {rho : ℂ} (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    -rho ≠ 2 := by
  intro h
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith

theorem exists_even_negative_diagonal_of_offLineZero
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < 1) (hRlog2 : R < Real.log 2)
    (hbudget :
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
          (1 / 2 : ℝ) * Real.log (1 / R) < 0) :
    ∃ f : CompactLogTest,
      (∀ x : ℝ, f.test (-x) = f.test x) ∧
        CompactLogTest.laplaceAt f 0 = 0 ∧
        CompactLogTest.laplaceAt f (1 / 2 : ℂ) = 0 ∧
        CompactLogTest.laplaceAt f 1 = 0 ∧
        ICgate f.convolutionSquare < 0 := by
  rcases CompactLogTest.exists_residualWindow_correction (evenNodeSet rho)
      (lower := -(R / 2)) (upper := R / 2) (by linarith) (by linarith)
      (evenNodeTarget (rho := rho)) with ⟨h, hsupport, hvalues⟩
  have hrho0 : CompactLogTest.laplaceAt h rho = 0 := by
    have hv := hvalues
      (⟨rho, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    rw [show evenNodeTarget rho (⟨rho, by simp [evenNodeSet]⟩) = 0 by
      dsimp [evenNodeTarget]
      rw [if_neg (rho_ne_two hrho)]] at hv
    exact hv
  have hnegrho : CompactLogTest.laplaceAt h (-rho) = 0 := by
    have hv := hvalues
      (⟨-rho, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    rw [show evenNodeTarget rho (⟨-rho, by simp [evenNodeSet]⟩) = 0 by
      dsimp [evenNodeTarget]
      rw [if_neg (neg_rho_ne_two hrho)]] at hv
    exact hv
  have hhalf : CompactLogTest.laplaceAt h (1 / 2 : ℂ) = 0 := by
    have hv := hvalues
      (⟨1 / 2, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have hnhalf : CompactLogTest.laplaceAt h (-(1 / 2 : ℂ)) = 0 := by
    have hv := hvalues
      (⟨-(1 / 2 : ℂ), by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have hone : CompactLogTest.laplaceAt h 1 = 0 := by
    have hv := hvalues
      (⟨1, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have hnone : CompactLogTest.laplaceAt h (-1) = 0 := by
    have hv := hvalues
      (⟨-1, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have hzero : CompactLogTest.laplaceAt h 0 = 0 := by
    have hv := hvalues
      (⟨0, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have htwo : CompactLogTest.laplaceAt h 2 = 1 := by
    have hv := hvalues
      (⟨2, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  have hntwo : CompactLogTest.laplaceAt h (-2) = 0 := by
    have hv := hvalues
      (⟨-2, by simp [evenNodeSet]⟩ : FiniteMellinNode (evenNodeSet rho))
    norm_num [evenNodeTarget] at hv
    exact hv
  let f := evenPart h
  have hfEven : ∀ x : ℝ, f.test (-x) = f.test x := test_even_evenPart h
  have hfsupport : Function.support f.test ⊆ Set.Icc (-(R / 2)) (R / 2) :=
    support_evenPart_subset_Icc h (R / 2) hsupport
  have hsq : Function.support f.convolutionSquare.test ⊆ Ioo (-R) R := by
    have hsq' := CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo
      f hfsupport
    intro x hx
    rcases hsq' hx with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hmass : 0 < (f.convolutionSquare.test 0).re := by
    apply convolutionSquare_mass_pos_of_test_ne_zero
    intro hfzero
    have hzero : CompactLogTest.laplaceAt f 2 = 0 := by
      simp [f, CompactLogTest.laplaceAt, CompactLogTest.exponentialWeight_apply,
        hfzero]
    rw [laplaceAt_evenPart, laplaceAt_reflection, htwo, hntwo] at hzero
    norm_num at hzero
  have hgate := ICgate_neg_of_narrow_budget f R hRpos hRlt hRlog2 hsq hbudget hmass
  have hf0 : CompactLogTest.laplaceAt f 0 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_reflection, neg_zero, hzero]
    simp
  have hfhalf : CompactLogTest.laplaceAt f (1 / 2 : ℂ) = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_reflection, hhalf, hnhalf]
    simp
  have hfone : CompactLogTest.laplaceAt f 1 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_reflection, hone, hnone]
    simp
  exact ⟨f, hfEven, hf0, hfhalf, hfone, hgate⟩

end C1P2EvenNegativeDiagonalCertificate
end Source
end ConnesWeilRH
