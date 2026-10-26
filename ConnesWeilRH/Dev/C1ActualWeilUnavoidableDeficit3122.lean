import ConnesWeilRH.Dev.C1RouteBArchimedeanFourierReadback3121
import ConnesWeilRH.Dev.C1RouteANegativeEnergyWitness3093

/-! The exact physical Weil density has a genuine positive deficit on every
nonzero compact-log source, including the actual powered spans. Triple
vanishing at one frequency cannot remove this integral. No global sign is
supplied, and the different Poisson-symbol contract is not used. -/

namespace ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122

open MeasureTheory Filter Set
open CC20YoshidaConvolution CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution CC20YoshidaNearZeros
open C1RouteBPrimeFourierReadback3120 C1RouteBArchimedeanFourierReadback3121
open C1RouteAOwnerAnalyticTransform3092 C1RouteAAnalyticPuncturedWitness3085
open C1RouteBAdaptivePoweredTail3117 C1FourPointSpectralPrefixTransport
open C1TwoPointSpectralDecomposition C1HealthyYoshidaUnscaledOrbit C1SameOwnerWeil
open C1HealthyYoshidaDetector
open ConnesWeilRH.Dev
open scoped FourierTransform Topology BigOperators

noncomputable section

def gateSymbol3122 (g : CompactLogTest) (xi : ℝ) : ℝ :=
  c3Sigma (2 * Real.pi * xi) + primeKernel3120 (globalPrimeIndexSet g.convolutionSquare) xi

def weilDensity3122 (g : CompactLogTest) (xi : ℝ) : ℝ :=
  -(gateSymbol3122 g xi * energy3120 g xi)

def creditDensity3122 (g : CompactLogTest) (xi : ℝ) : ℝ := max (weilDensity3122 g xi) 0

def deficitDensity3122 (g : CompactLogTest) (xi : ℝ) : ℝ := max (-weilDensity3122 g xi) 0

theorem c3Sigma_continuous3122 : Continuous c3Sigma := by
  apply continuous_iff_continuousAt.mpr
  intro xi
  have hd : ContinuousAt Complex.digamma
      (((1 / 4 : ℝ) : ℂ) - ((xi : ℂ) * Complex.I) / 2) :=
    by
      convert (hasDerivAt_digamma_criticalQuarterLine (xi / (2 * Real.pi))).continuousAt using 1
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
      push_cast
      field_simp [Real.pi_ne_zero]
  have harg : ContinuousAt (fun t : ℝ =>
      (((1 / 4 : ℝ) : ℂ) - ((t : ℂ) * Complex.I) / 2)) xi := by fun_prop
  have hcomp : ContinuousAt (fun t : ℝ => Complex.digamma
      (((1 / 4 : ℝ) : ℂ) - ((t : ℂ) * Complex.I) / 2)) xi :=
    hd.comp_of_eq harg rfl
  exact continuousAt_const.sub (Complex.continuous_re.continuousAt.comp hcomp)

theorem gateSymbol_continuous3122 (g : CompactLogTest) : Continuous (gateSymbol3122 g) := by
  unfold gateSymbol3122
  apply Continuous.add
  · exact c3Sigma_continuous3122.comp (by fun_prop)
  · unfold primeKernel3120
    fun_prop

theorem weilDensity_continuous3122 (g : CompactLogTest) : Continuous (weilDensity3122 g) := by
  unfold weilDensity3122 energy3120
  exact ((gateSymbol_continuous3122 g).mul (by fun_prop)).neg

theorem gateSymbol_zero_pos3122 (g : CompactLogTest) : 0 < gateSymbol3122 g 0 := by
  unfold gateSymbol3122 primeKernel3120
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  have hs : 0 ≤ ∑ q ∈ globalPrimeIndexSet g.convolutionSquare, primeWeight3120 q := by
    apply Finset.sum_nonneg
    intro q _
    unfold primeWeight3120
    exact div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.sqrt_nonneg _)
  exact add_pos_of_pos_of_nonneg C1C3SigmaZeroMargin3090.c3Sigma_zero_pos hs

theorem fourier_analytic3122 (g : CompactLogTest) :
    AnalyticOnNhd ℝ (fun xi : ℝ => (𝓕 g.test) xi) univ := by
  have heq : (fun xi : ℝ => (𝓕 g.test) xi) =
      (fun xi : ℝ => laplaceAt g (cyclePoint3120 xi)) := by
    funext xi
    exact fourier_eq_cycle_laplace3120 g xi
  rw [heq]
  intro xi _
  have hp : AnalyticAt ℝ (cyclePoint3120) xi := by
    have h : AnalyticAt ℝ
        (fun t : ℝ => ((-2 * Real.pi : ℝ) : ℂ) * (t : ℂ) * Complex.I) xi :=
      ((analyticAt_const (v := ((-2 * Real.pi : ℝ) : ℂ))).mul
        (Complex.ofRealCLM.analyticAt xi)).mul (analyticAt_const (v := Complex.I))
    convert h using 1
    funext t
    simp only [cyclePoint3120, Complex.ofReal_mul]
  exact ((compactLogLaplace_analytic g _ (mem_univ _)).restrictScalars).comp hp

theorem fourier_global_nonzero3122 (g : CompactLogTest) (hg : g.test ≠ 0) :
    ∃ xi : ℝ, (𝓕 g.test) xi ≠ 0 := by
  have hf : 𝓕 g.test ≠ 0 := by
    intro h
    apply hg
    apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
    simpa using h
  by_contra hnone
  apply hf
  ext xi
  by_contra hxi
  exact hnone ⟨xi, hxi⟩

theorem exists_deficit_frequency3122 (g : CompactLogTest) (hg : g.test ≠ 0) :
    ∃ xi : ℝ, xi ≠ 0 ∧ 0 < gateSymbol3122 g xi ∧ (𝓕 g.test) xi ≠ 0 ∧
      0 < deficitDensity3122 g xi := by
  have hnhds : (gateSymbol3122 g) ⁻¹' Ioi 0 ∈ 𝓝 (0 : ℝ) :=
    (gateSymbol_continuous3122 g).continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (gateSymbol_zero_pos3122 g))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have ha := fourier_analytic3122 g
  have hnot : ¬ ∀ᶠ xi in 𝓝 (0 : ℝ), (𝓕 g.test) xi = 0 := by
    intro hzero
    have heq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ha isPreconnected_univ (by simp : (0 : ℝ) ∈ univ) hzero
    obtain ⟨xi, hxi⟩ := fourier_global_nonzero3122 g hg
    exact hxi (by simpa using heq (mem_univ xi))
  obtain ⟨xi, hne, hxi, hf⟩ :=
    exists_nonzero_point_in_ball_of_analyticAt_not_eventually_zero r hr (ha 0 (mem_univ _)) hnot
  have hs : 0 < gateSymbol3122 g xi := hball (by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hxi)
  refine ⟨xi, hne, hs, hf, ?_⟩
  have he : 0 < energy3120 g xi := by
    unfold energy3120
    exact sq_pos_of_pos (norm_pos_iff.mpr hf)
  unfold deficitDensity3122 weilDensity3122
  simpa only [neg_neg] using (mul_pos hs he).trans_le (le_max_left _ 0)

theorem weilDensity_integrable3122 (g : CompactLogTest) : Integrable (weilDensity3122 g) :=
  (complete_gate_integrable3121 g).neg

theorem credit_integrable3122 (g : CompactLogTest) : Integrable (creditDensity3122 g) :=
  (weilDensity_integrable3122 g).pos_part

theorem deficit_integrable3122 (g : CompactLogTest) : Integrable (deficitDensity3122 g) :=
  (weilDensity_integrable3122 g).neg.pos_part

theorem deficit_integral_pos3122 (g : CompactLogTest) (hg : g.test ≠ 0) :
    0 < ∫ xi : ℝ, deficitDensity3122 g xi := by
  obtain ⟨xi, _, _, _, hx⟩ := exists_deficit_frequency3122 g hg
  apply integral_pos_of_integrable_nonneg_nonzero (x := xi)
    (((weilDensity_continuous3122 g).neg).max continuous_const) (deficit_integrable3122 g)
  · intro t
    exact le_max_right _ _
  · exact ne_of_gt hx

theorem not_weilDensity_pointwise_nonneg3122 (g : CompactLogTest) (hg : g.test ≠ 0) :
    ¬ ∀ xi : ℝ, 0 ≤ weilDensity3122 g xi := by
  intro hnonneg
  obtain ⟨xi, _, _, _, hdeficit⟩ := exists_deficit_frequency3122 g hg
  unfold deficitDensity3122 at hdeficit
  rw [max_eq_right (neg_nonpos.mpr (hnonneg xi))] at hdeficit
  exact (lt_irrefl (0 : ℝ)) hdeficit

theorem density_eq_credit_sub_deficit3122 (g : CompactLogTest) (xi : ℝ) :
    weilDensity3122 g xi = creditDensity3122 g xi - deficitDensity3122 g xi := by
  unfold creditDensity3122 deficitDensity3122
  rcases le_total 0 (weilDensity3122 g xi) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

theorem qw_eq_credit_sub_deficit3122 (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g) :
    qw g = (∫ xi : ℝ, creditDensity3122 g xi) - ∫ xi : ℝ, deficitDensity3122 g xi := by
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple g hvanishes]
  rw [show -archimedeanTerm g.convolutionSquare - finitePrimeSum g.convolutionSquare =
      -(archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare) by ring,
    complete_gate_readback3121, ← integral_neg]
  change (∫ xi : ℝ, weilDensity3122 g xi) = _
  simp_rw [density_eq_credit_sub_deficit3122]
  exact integral_sub (credit_integrable3122 g) (deficit_integrable3122 g)

theorem poweredFamily_span_test_ne_zero3122
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (hlambda : lambda ≠ 0) :
    (poweredFamilySpan3117 rho N nodes n lambda).test ≠ 0 := by
  have htarget : laplaceAt (poweredFamilyOwner3117 rho N nodes n) (rho - 1 / 2) = 1 := by
    exact (poweredFamily_target3117 rho N nodes n
      ⟨rho, mem_healthyUnscaledTargetNodes_rho rho⟩).trans (healthyUnscaledTargetValue_rho rho)
  have hspan : laplaceAt (poweredFamilySpan3117 rho N nodes n lambda) (rho - 1 / 2) =
      -(lambda : ℂ) := by
    change laplaceAt (annihilatorDetectorSpanVector _ _ _) _ = _
    rw [laplaceAt_fullOrbitSpanVector, htarget]
    simp only [sub_self, mul_zero, zero_sub, mul_one]
  intro hzero
  have hz : laplaceAt (poweredFamilySpan3117 rho N nodes n lambda) (rho - 1 / 2) = 0 := by
    unfold laplaceAt
    simp [exponentialWeight_apply, hzero]
  have hc : (lambda : ℂ) = 0 := neg_eq_zero.mp (hspan.symm.trans hz)
  exact hlambda (Complex.ofReal_eq_zero.mp hc)

theorem poweredFamily_deficit_integral_pos3122
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (hlambda : lambda ≠ 0) :
    0 < ∫ xi : ℝ, deficitDensity3122 (poweredFamilySpan3117 rho N nodes n lambda) xi :=
  deficit_integral_pos3122 _ (poweredFamily_span_test_ne_zero3122 rho N nodes n lambda hlambda)

theorem selectedOwner_deficit_integral_pos3122
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest} (geometry : C1G8R0OrbitGeometry.OrbitG8Geometry rho g) :
    0 < ∫ xi : ℝ, deficitDensity3122 g xi :=
  deficit_integral_pos3122 g (routeAOwnerTest_ne_zero geometry)

end
end ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122
