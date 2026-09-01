import ConnesWeilRH.Dev.C1HealthyDetectorAnchorReduction
import ConnesWeilRH.Dev.C1HealthyDetectorPinning

/-!
# C1HealthyDetectorKernelABridge - kernel (a) IS the record-1080 scalar gate

Record 1084 reduced consumer 3 kernel (a) to `0 < arch h.convSq` for ONE
root-window triple-vanishing detecting test, and record 1080 named the
consumer-2/3 handoff as the scalar gate `selectedDetectorArchimedeanGate`
on a PINNED detector.  This module proves the two open obligations are THE
SAME inequality on THE SAME explicit object:

1. `convolutionSquare_negTest` - pointwise negation leaves the Hermitian
   square unchanged (`star` eats the minus sign);
2. `archimedeanTerm_negTest` - hence the archimedean term of the square is
   INVARIANT under pointwise negation of the test;
3. `exists_pinnedDetector_of_kernelAInterpolant` - for every off-line
   source zero there is an explicit pair `(h, g)` with `h` the 7-node
   symmetric interpolant of records 1083/1084 (triple-vanishing, detecting
   with the exact value `1`, root-window support) and `g = negTest h` a
   PINNED detector in the record-1080 sense (`HealthyMinimalLaplaceRealizes`,
   detection value `-1`, explicit radius `log 2 / 2`, EMPTY visible-prime
   set), such that the record-1080 scalar gate on `g` is EQUIVALENT to
   kernel (a)'s anchor positivity on `h`, and the anchor positivity yields
   the full `HealthyYoshidaDetectorData` package.

Kernel (a) of consumer 3 and the record-1080 handoff gate are therefore the
same single inequality; the remaining content is unchanged (the 1077-1079
measured object, fl2 = -1.294, sink 33.78%).  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorKernelABridge

open MeasureTheory
open scoped ContDiff
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1HealthyDetectorPinning
open C1HealthyDetectorEvenOddPair

/-! ### Pointwise negation does not touch the Hermitian square -/

/-- Pointwise negation of the test leaves the convolution square
pointwise unchanged: `star (-z) * (-w) = star z * w`. -/
theorem convolutionSquare_negTest (h : CompactLogTest) (y : ℝ) :
    (negTest h).convolutionSquare.test y = h.convolutionSquare.test y := by
  rw [CompactLogTest.convolutionSquare_apply,
    CompactLogTest.convolutionSquare_apply]
  have hcongr : (fun t : ℝ => star ((negTest h).test (-t)) * (negTest h).test (y - t)) =
      (fun t : ℝ => star (h.test (-t)) * h.test (y - t)) := by
    funext t
    simp only [negTest_apply, star_neg]
    ring
  rw [hcongr]

/-- The archimedean numerator is unchanged under pointwise negation of
the test. -/
theorem archimedeanNumerator_negTest (h : CompactLogTest) (y : ℝ) :
    archimedeanNumerator (negTest h).convolutionSquare y =
      archimedeanNumerator h.convolutionSquare y := by
  simp only [archimedeanNumerator, convolutionSquare_negTest]

/-- The archimedean integrand is unchanged under pointwise negation of
the test. -/
theorem archimedeanIntegrand_negTest (h : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand (negTest h).convolutionSquare y =
      archimedeanIntegrand h.convolutionSquare y := by
  simp only [archimedeanIntegrand, archimedeanNumerator_negTest h y]

/-- The archimedean term of the Hermitian square is INVARIANT under
pointwise negation of the test (the square is quadratic, the archimedean
term reads it pointwise). -/
theorem archimedeanTerm_negTest (h : CompactLogTest) :
    C1SameOwnerWeil.archimedeanTerm (negTest h).convolutionSquare =
      C1SameOwnerWeil.archimedeanTerm h.convolutionSquare := by
  have hEq : ∫ y in Set.Ioi (0 : ℝ),
      archimedeanIntegrand (negTest h).convolutionSquare y =
        ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand h.convolutionSquare y :=
    integral_congr_ae (Filter.Eventually.of_forall fun y =>
      archimedeanIntegrand_negTest h y)
  unfold C1SameOwnerWeil.archimedeanTerm
  rw [convolutionSquare_negTest h 0, hEq]

/-! ### The bridge: kernel (a) on `h` = the scalar gate on `negTest h` -/

/-- THE KERNEL (a) BRIDGE.  For every off-line source zero there is an
explicit pair `(h, g)`:

* `h` is the 7-node symmetric interpolant of records 1083/1084: root-window
  support, triple vanishing on `{0, 1/2, 1}`, detection with the EXACT
  value `1` at `rho`;
* `g = negTest h` is a PINNED detector in the record-1080 sense:
  `HealthyMinimalLaplaceRealizes`, detection value `-1`, explicit radius
  `log 2 / 2`, EMPTY visible-prime set;
* the record-1080 scalar gate on `g` is EQUIVALENT to kernel (a)'s anchor
  positivity on `h`, and that single inequality yields the FULL
  `HealthyYoshidaDetectorData` package on `g`.

So kernel (a) of consumer 3 and the record-1080 handoff gate are the same
inequality on the same object. -/
theorem exists_pinnedDetector_of_kernelAInterpolant
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ h g : CompactLogTest,
      Function.support h.test ⊆
        Set.Ioo (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
        CompactLogTest.laplaceAt h 0 = 0 ∧
          CompactLogTest.laplaceAt h (1 / 2 : ℂ) = 0 ∧
            CompactLogTest.laplaceAt h 1 = 0 ∧
              CompactLogTest.laplaceAt h rho = 1 ∧
        HealthyMinimalLaplaceRealizes rho g ∧
          CompactLogTest.laplaceAt g rho = -1 ∧
            Function.support g.test ⊆
              Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
              globalPrimeIndexSet g.convolutionSquare = ∅ ∧
                (selectedDetectorArchimedeanGate rho g ↔
                    0 < C1SameOwnerWeil.archimedeanTerm
                      h.convolutionSquare) ∧
                  (0 < C1SameOwnerWeil.archimedeanTerm
                      h.convolutionSquare →
                    HealthyYoshidaDetectorData rho g) := by
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
  have hone : CompactLogTest.laplaceAt h rho = 1 := by
    rw [hvals (⟨rho, by simp [pairNodeSet]⟩ :
      FiniteMellinNode (pairNodeSet rho)), pairNodeTarget_at_rho rho]
  have g0 : CompactLogTest.laplaceAt (negTest h) 0 = 0 := by
    rw [laplaceAt_negTest, f0]
    simp
  have ghalf : CompactLogTest.laplaceAt (negTest h) (1 / 2 : ℂ) = 0 := by
    rw [laplaceAt_negTest, fhalf]
    simp
  have gone : CompactLogTest.laplaceAt (negTest h) 1 = 0 := by
    rw [laplaceAt_negTest, fone]
    simp
  have gdet : CompactLogTest.laplaceAt (negTest h) rho = -1 := by
    rw [laplaceAt_negTest, hone]
  have hpinned : HealthyMinimalLaplaceRealizes rho (negTest h) :=
    ⟨g0, ghalf, gone, by rw [gdet]; norm_num⟩
  have gsupp : Function.support (negTest h).test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) :=
    Set.Subset.trans (support_negTest h)
      (Set.Subset.trans hwin Set.Ioo_subset_Icc_self)
  have gprime : globalPrimeIndexSet (negTest h).convolutionSquare = ∅ :=
    globalPrimeIndexSet_eq_empty_of_support_subset_open_log_two
      ((negTest h).convolutionSquare)
      (convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf
        (negTest h) gsupp)
  have hgateiff : selectedDetectorArchimedeanGate rho (negTest h) ↔
      0 < C1SameOwnerWeil.archimedeanTerm h.convolutionSquare := by
    unfold selectedDetectorArchimedeanGate
    rw [archimedeanTerm_negTest h]
  refine ⟨h, negTest h, hwin, f0, fhalf, fone, hone, hpinned, gdet, gsupp,
    gprime, hgateiff, fun harch => ?_⟩
  exact
    (healthyDetectorData_iff_selectedDetectorArchimedeanGate hpinned
      gsupp).mpr (hgateiff.mpr harch)

end C1HealthyDetectorKernelABridge
end Source
end ConnesWeilRH
