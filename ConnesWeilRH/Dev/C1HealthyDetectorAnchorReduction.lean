import ConnesWeilRH.Dev.C1HealthyDetectorEvenOddPair

/-!
# C1HealthyDetectorAnchorReduction - the anchor collapses to a single test

Record 1083 constructed, for every off-line source zero, an explicit pair
`(f, g) = (evenPart h, oddPart h)` whose rescue-gate obligation is exactly
`0 < arch f.convSq + arch g.convSq`.  This module collapses that obligation
onto the interpolant itself:

1. SCALING: if `F.test = 2 * h.test` pointwise then the convolution square
   scales by `4` and so does the archimedean term
   `arch F.convSq = 4 * arch h.convSq` (pure congruence - the archimedean
   term is a constant-times-`F 0` plus an integral, so no integrability
   input is needed);
2. `anchor_eq_four_mul_of_even_odd_sum`: for an even `f`, an odd `g` and
   `f + g = 2h` pointwise, `arch f.convSq + arch g.convSq = 4 * arch
   h.convSq` EXACTLY - the pair's cross term is dead by the record-1082
   odd kill, and the sum square scales by four;
3. `arch_pair_eq_four_mul`: specialization to `(evenPart h, oddPart h)`;
4. `rootGate_of_tripleVanishing_detecting_rootWindow` - the former kernel (a)
   FORM: a SINGLE test `h` with root-window support, triple vanishing at
   `{0, 1/2, 1}`, detection at `rho`, and `0 < arch h.convSq` satisfies the
   full root-supported healthy detector gate.  The even/odd pair is a
   decomposition device; the anchor positivity obligation lands back on
   `h` itself - the pinned-detector scalar gate of record 1080;
5. `exists_kernelA_final`: the 7-node symmetric interpolant of record 1083
   supplies all hypotheses except the positive archimedean square term.

This is a conditional ROOT-supported strict-negative-detector branch. It does
not produce the active C3/P2 inequality `qw >= 0` for the formal orbit detector.

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorAnchorReduction

open MeasureTheory
open scoped ContDiff
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1
open C1HealthyYoshidaDetector
open C1HealthyDetectorRootSupportExit
open C1HealthyDetectorEvenOddPair
open C1HealthyDetectorArchRescue

private theorem star_two : (star (2 : ℂ)) = 2 := by
  apply Complex.ext
  · simp
  · simp

/-! ### The convolution square scales by four under `test = 2 * h` -/

/-- If two tests differ by the scalar `2` pointwise, their convolution
squares differ by `4`. -/
theorem convolutionSquare_eq_four_mul_of_test_eq_two_mul
    (F h : CompactLogTest) (hpt : ∀ x : ℝ, F.test x = 2 * h.test x) (y : ℝ) :
    F.convolutionSquare.test y = 4 * h.convolutionSquare.test y := by
  rw [CompactLogTest.convolutionSquare_apply,
    CompactLogTest.convolutionSquare_apply]
  have hcongr : (fun t : ℝ => star (F.test (-t)) * F.test (y - t)) =
      (fun t : ℝ => (4 : ℂ) * (star (h.test (-t)) * h.test (y - t))) := by
    funext t
    rw [hpt, hpt, star_mul, star_two]
    ring
  rw [hcongr, MeasureTheory.integral_const_mul]

/-- The archimedean numerator of the square scales by four. -/
theorem archimedeanNumerator_convolutionSquare_eq_four_mul
    (F h : CompactLogTest) (hpt : ∀ x : ℝ, F.test x = 2 * h.test x) (y : ℝ) :
    archimedeanNumerator F.convolutionSquare y =
      4 * archimedeanNumerator h.convolutionSquare y := by
  have hsquare : ∀ x : ℝ, F.convolutionSquare.test x =
      4 * h.convolutionSquare.test x :=
    convolutionSquare_eq_four_mul_of_test_eq_two_mul F h hpt
  simp only [archimedeanNumerator]
  rw [hsquare y, hsquare (-y), hsquare 0]
  simp only [mul_add, mul_sub]
  ring

/-- The archimedean integrand of the square scales by four. -/
theorem archimedeanIntegrand_convolutionSquare_eq_four_mul
    (F h : CompactLogTest) (hpt : ∀ x : ℝ, F.test x = 2 * h.test x) (y : ℝ) :
    archimedeanIntegrand F.convolutionSquare y =
      4 * archimedeanIntegrand h.convolutionSquare y := by
  have hnum := archimedeanNumerator_convolutionSquare_eq_four_mul F h hpt y
  simp only [archimedeanIntegrand, hnum, mul_div_assoc]

/-- SCALING.  The archimedean term of the square scales by four under a
pointwise doubling of the test. -/
theorem archimedeanTerm_convolutionSquare_eq_four_mul
    (F h : CompactLogTest) (hpt : ∀ x : ℝ, F.test x = 2 * h.test x) :
    C1SameOwnerWeil.archimedeanTerm F.convolutionSquare =
      4 * C1SameOwnerWeil.archimedeanTerm h.convolutionSquare := by
  have hEq : ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand F.convolutionSquare y =
      ∫ y in Set.Ioi (0 : ℝ),
        4 * archimedeanIntegrand h.convolutionSquare y :=
    integral_congr_ae (Filter.Eventually.of_forall fun y =>
      archimedeanIntegrand_convolutionSquare_eq_four_mul F h hpt y)
  unfold C1SameOwnerWeil.archimedeanTerm
  rw [convolutionSquare_eq_four_mul_of_test_eq_two_mul F h hpt 0, hEq,
    MeasureTheory.integral_const_mul]
  simp [Complex.mul_re]
  ring

/-! ### The pair's anchor is four times the interpolant's term -/

/-- THE ANCHOR COLLAPSE.  An even test, an odd test whose pointwise sum is
`2 * h`: the two-term anchor is EXACTLY `4 * arch h.convSq`.  The pair's
cross term is dead by the odd kill, and the sum square scales by four. -/
theorem anchor_eq_four_mul_of_even_odd_sum
    {f g h : CompactLogTest}
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hsum : ∀ x : ℝ, (sumTest f g).test x = 2 * h.test x) :
    C1SameOwnerWeil.archimedeanTerm f.convolutionSquare +
      C1SameOwnerWeil.archimedeanTerm g.convolutionSquare =
      4 * C1SameOwnerWeil.archimedeanTerm h.convolutionSquare := by
  rw [← archimedeanTerm_convolutionSquare_eq_four_mul (sumTest f g) h hsum,
    archimedeanTerm_convolutionSquare_sumTest_of_even_odd f g hf hg]

/-- Specialization to the record-1083 even/odd parts of one test. -/
theorem arch_pair_eq_four_mul (h : CompactLogTest) :
    C1SameOwnerWeil.archimedeanTerm (evenPart h).convolutionSquare +
      C1SameOwnerWeil.archimedeanTerm (oddPart h).convolutionSquare =
      4 * C1SameOwnerWeil.archimedeanTerm h.convolutionSquare :=
  anchor_eq_four_mul_of_even_odd_sum (test_even_evenPart h)
    (test_neg_oddPart h)
    (by
      intro x
      simp only [evenPart, oddPart, sumTest_apply, negTest_apply,
        CompactLogTest.reflection_apply]
      ring)

/-- The Laplace value of the even/odd sum is twice the interpolant's. -/
theorem laplaceAt_sumTest_evenOdd (h : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt (sumTest (evenPart h) (oddPart h)) s =
      2 * CompactLogTest.laplaceAt h s := by
  rw [laplaceAt_sumTest, laplaceAt_evenPart, laplaceAt_oddPart,
    laplaceAt_reflection]
  ring

/-! ### Kernel (a) final form -/

/-- KERNEL (a) FINAL FORM.  ONE root-window test with the triple
vanishings, detection at `rho`, and positive archimedean square term
satisfies the full root-supported healthy detector gate.  The even/odd
pair is a decomposition device; the positivity obligation lands back on
`h` itself. -/
theorem rootGate_of_tripleVanishing_detecting_rootWindow
    {rho : ℂ}
    {h : CompactLogTest}
    (hsupp : Function.support h.test ⊆
      Set.Ioo (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hv0 : CompactLogTest.laplaceAt h 0 = 0)
    (vhalf : CompactLogTest.laplaceAt h (1 / 2 : ℂ) = 0)
    (vone : CompactLogTest.laplaceAt h 1 = 0)
    (vdet : CompactLogTest.laplaceAt h rho ≠ 0)
    (harch : 0 < C1SameOwnerWeil.archimedeanTerm h.convolutionSquare) :
    rootSupportedHealthyDetectorGate rho := by
  have hf0 : CompactLogTest.laplaceAt (evenPart h) 0 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_reflection, neg_zero, hv0]
    simp
  have hhalf : CompactLogTest.laplaceAt (evenPart h) (1 / 2 : ℂ) +
      CompactLogTest.laplaceAt (oddPart h) (1 / 2 : ℂ) = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_oddPart, laplaceAt_reflection, vhalf]
    ring
  have hone : CompactLogTest.laplaceAt (evenPart h) 1 +
      CompactLogTest.laplaceAt (oddPart h) 1 = 0 := by
    rw [laplaceAt_evenPart, laplaceAt_oddPart, laplaceAt_reflection, vone]
    ring
  have hdet : CompactLogTest.laplaceAt
      (sumTest (evenPart h) (oddPart h)) rho ≠ 0 := by
    rw [laplaceAt_sumTest_evenOdd]
    exact mul_ne_zero (by norm_num) vdet
  have hsupp' : Function.support (sumTest (evenPart h) (oddPart h)).test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) := by
    refine Set.Subset.trans (support_sumTest_subset (evenPart h) (oddPart h))
      (Set.union_subset ?_ ?_)
    · exact support_evenPart_subset_Icc h (Real.log 2 / 2) hsupp
    · exact support_oddPart_subset_Icc h (Real.log 2 / 2) hsupp
  have hpos : 0 < C1SameOwnerWeil.archimedeanTerm
      (evenPart h).convolutionSquare +
      C1SameOwnerWeil.archimedeanTerm (oddPart h).convolutionSquare := by
    rw [arch_pair_eq_four_mul h]
    exact mul_pos (by norm_num) harch
  exact rootSupportedGate_of_evenBase_oddCorrection (test_even_evenPart h)
    (test_neg_oddPart h) hf0 hhalf hone hdet hsupp' hpos

/-! ### The witness exists: the 7-node interpolant -/

/-- Former kernel (a) statement. For every off-line source zero there is a
single root-window test, triple-vanishing on the criterion set and
detecting at `rho`, whose full root-supported gate follows from the
positivity of its own archimedean square term. This implication supplies no
proof of that sign. -/
theorem exists_kernelA_final
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ h : CompactLogTest,
      Function.support h.test ⊆
        Set.Ioo (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
        CompactLogTest.laplaceAt h 0 = 0 ∧
          CompactLogTest.laplaceAt h (1 / 2 : ℂ) = 0 ∧
            CompactLogTest.laplaceAt h 1 = 0 ∧
              CompactLogTest.laplaceAt h rho ≠ 0 ∧
                (0 < C1SameOwnerWeil.archimedeanTerm h.convolutionSquare →
                  rootSupportedHealthyDetectorGate rho) := by
  classical
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlower : -(Real.log 2 / 2) < 0 := by linarith
  have hupper : (0 : ℝ) < Real.log 2 / 2 := by linarith
  rcases CompactLogTest.exists_residualWindow_correction (pairNodeSet rho)
      (lower := -(Real.log 2 / 2)) (upper := Real.log 2 / 2) hlower hupper
      (pairNodeTarget rho) with ⟨h, hwin, hvals⟩
  have f0 : CompactLogTest.laplaceAt h 0 = 0 := by
    rw [hvals (⟨0, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)), pairNodeTarget_at_zero hrho]
  have fhalf : CompactLogTest.laplaceAt h (1 / 2 : ℂ) = 0 := by
    rw [hvals (⟨1 / 2, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)), pairNodeTarget_at_half hrho hoff]
  have fone : CompactLogTest.laplaceAt h 1 = 0 := by
    rw [hvals (⟨1, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)), pairNodeTarget_at_one hrho]
  have fdet : CompactLogTest.laplaceAt h rho ≠ 0 := by
    intro hc
    have h1 : CompactLogTest.laplaceAt h rho =
        pairNodeTarget rho (⟨rho, by simp [pairNodeSet]⟩ :
          FiniteMellinNode (pairNodeSet rho)) :=
      hvals (⟨rho, by simp [pairNodeSet]⟩ :
        FiniteMellinNode (pairNodeSet rho))
    rw [h1, pairNodeTarget_at_rho rho] at hc
    norm_num at hc
  refine ⟨h, hwin, f0, fhalf, fone, fdet, fun harch =>
    rootGate_of_tripleVanishing_detecting_rootWindow hwin f0 fhalf fone fdet
      harch⟩

end C1HealthyDetectorAnchorReduction
end Source
end ConnesWeilRH
