import ConnesWeilRH.Dev.C1HealthyDetectorRootSupportExit
import ConnesWeilRH.Dev.C1HealthyNarrowPlateau

/-!
# C1HealthyDetectorArchRescue - the archimedean-rescue algebra for consumer 3

Consumer 3 of `RH_MAINLINE_FREEZE.md` (after records 1080/1081) reduces to the
single scalar kernel `0 < archimedeanTerm g.convolutionSquare` on a pinned
root-supported triple-vanishing detector.  This module supplies the ALGEBRA a
future certificate plugs into, and discovers the exact symmetry structure of
that kernel:

1. pointwise sums of compact-log tests (`sumTest`), with the Laplace
   additivity readback;
2. the EXACT quadratic decomposition of the archimedean term under
   `g = f + h`:
   `arch (f+h)^* (f+h) = arch f^* f + arch h^* h + arch (cross f h)`,
   where every archimedean integrand involved is integrable because the
   integrand is linear in the test and the three summand squares are
   integrable through the existing selected-owner bridge;
3. THE ODD KILL: if `f` is even and `h` is odd then `cross f h` is an odd
   test, and the archimedean term of ANY odd test vanishes identically
   (numerator and constant term are both forced to zero).  Hence on the
   even/odd class
   `arch (f+h)^* (f+h) = arch f^* f + arch h^* h` EXACTLY;
4. the odd Mellin blindness: an odd test has `laplaceAt h 0 = 0`, so the
   mass-zero node `{0}` of the triple vanishing set falls to the EVEN base;
5. the rescue gate: an even base, an odd correction, the three nodal sums,
   detection, root support, and positivity of the two-term anchor sum imply
   the FULL root-supported healthy detector gate of record 1081.

Structural consequence (record 1082): the symmetry route relocates the open
kernel from "one opaque four-term inequality" to "positivity of the two-term
anchor `arch f^* f + arch h^* h` on the even/odd class" - the cross terms are
dead by symmetry, but the mass-zero node forces a sign-changing even base, so
the anchor is exactly as open as before.  RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorArchRescue

open MeasureTheory
open scoped ContDiff
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open C1SameOwnerWeil
open C1
open C1HealthyYoshidaDetector
open C1HealthyDetectorRootSupportExit

/-! ### Pointwise sums of compact-log tests -/

/-- Pointwise sum of two compact-log tests. -/
noncomputable def sumTest (f g : CompactLogTest) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => f.test x + g.test x
  have hcompact : HasCompactSupport raw := f.compactSupport.add g.compactSupport
  have hsmooth : ContDiff ℝ ∞ raw := by
    fun_prop
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem sumTest_apply (f g : CompactLogTest) (x : ℝ) :
    (sumTest f g).test x = f.test x + g.test x :=
  rfl

/-- Laplace evaluation is additive on pointwise sums. -/
theorem laplaceAt_sumTest (f g : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt (sumTest f g) s =
      CompactLogTest.laplaceAt f s + CompactLogTest.laplaceAt g s := by
  have hsplit : (CompactLogTest.exponentialWeight (sumTest f g) s).test =
      fun x : ℝ => (CompactLogTest.exponentialWeight f s).test x +
        (CompactLogTest.exponentialWeight g s).test x := by
    funext x
    simp [CompactLogTest.exponentialWeight_apply, sumTest_apply]
    ring
  unfold CompactLogTest.laplaceAt
  rw [hsplit, MeasureTheory.integral_add
    (SchwartzMap.integrable (CompactLogTest.exponentialWeight f s).test)
    (SchwartzMap.integrable (CompactLogTest.exponentialWeight g s).test)]

/-! ### The archimedean integrand is linear in the test -/

theorem archimedeanNumerator_sumTest (F G : CompactLogTest) (y : ℝ) :
    archimedeanNumerator (sumTest F G) y =
      archimedeanNumerator F y + archimedeanNumerator G y := by
  simp [archimedeanNumerator, sumTest_apply]
  ring

theorem archimedeanIntegrand_sumTest (F G : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand (sumTest F G) y =
      archimedeanIntegrand F y + archimedeanIntegrand G y := by
  simp only [archimedeanIntegrand, archimedeanNumerator_sumTest, add_div]

/-! ### Integrability through the selected-owner bridge -/

/-- For EVERY compact-log test the archimedean integrand of the genuine
convolution square is integrable on the positive half-line: the pointwise
selected-owner readback transports the existing integrability theorem. -/
theorem integrableOn_archimedeanIntegrand_convolutionSquare (g : CompactLogTest) :
    IntegrableOn (archimedeanIntegrand g.convolutionSquare)
      (Set.Ioi (0 : ℝ)) := by
  have heq : (archimedeanIntegrand g.convolutionSquare) =
      (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanIntegrand :=
    funext (archimedeanIntegrand_square_eq_selected g)
  rw [heq]
  exact
    (SelectedWeilSquareOwner.ofCompactLogTest
      g).archimedeanIntegrand_integrableOn_Ioi

/-! ### The cross test and the exact quadratic decomposition -/

/-- The polarized cross of two tests: `f^* * g + g^* * f`. -/
noncomputable def crossTest (f g : CompactLogTest) : CompactLogTest :=
  sumTest (f.involution.convolution g) (g.involution.convolution f)

@[simp] theorem crossTest_apply (f g : CompactLogTest) (x : ℝ) :
    (crossTest f g).test x =
      (f.involution.convolution g).test x +
        (g.involution.convolution f).test x :=
  rfl

private theorem integrable_pair (f g : CompactLogTest) (y : ℝ) :
    Integrable (fun t : ℝ => f.test t * g.test (y - t)) := by
  have hex : MeasureTheory.ConvolutionExistsAt f.test g.test y
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
    exact HasCompactSupport.convolutionExists_left_of_continuous_right
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
      f.compactSupport f.test.integrable.locallyIntegrable
      (g.test.smooth ⊤).continuous y
  exact hex

/-- The square of a pointwise sum decomposes pointwise into the two squares
plus the polarized cross. -/
theorem convolutionSquare_sumTest_apply (f g : CompactLogTest) (y : ℝ) :
    (sumTest f g).convolutionSquare.test y =
      f.convolutionSquare.test y + g.convolutionSquare.test y +
        (crossTest f g).test y := by
  have hint1 : Integrable (fun t : ℝ => star (f.test (-t)) * f.test (y - t))
      volume := integrable_pair f.involution f y
  have hint2 : Integrable (fun t : ℝ => star (g.test (-t)) * g.test (y - t))
      volume := integrable_pair g.involution g y
  have hint3 : Integrable (fun t : ℝ => star (f.test (-t)) * g.test (y - t))
      volume := integrable_pair f.involution g y
  have hint4 : Integrable (fun t : ℝ => star (g.test (-t)) * f.test (y - t))
      volume := integrable_pair g.involution f y
  have hint34 := hint3.add hint4
  have hcongr :
      (fun t : ℝ =>
          star ((sumTest f g).test (-t)) * (sumTest f g).test (y - t)) =
        (fun t : ℝ => star (f.test (-t)) * f.test (y - t)) +
          ((fun t : ℝ => star (g.test (-t)) * g.test (y - t)) +
            ((fun t : ℝ => star (f.test (-t)) * g.test (y - t)) +
              (fun t : ℝ => star (g.test (-t)) * f.test (y - t)))) := by
    funext t
    simp only [sumTest_apply, star_add, add_mul, mul_add, Pi.add_apply]
    ring
  have hcross :
      (crossTest f g).test y =
        (∫ t : ℝ, star (f.test (-t)) * g.test (y - t)) +
          ∫ t : ℝ, star (g.test (-t)) * f.test (y - t) := by
    rw [crossTest_apply, CompactLogTest.convolution_apply,
      CompactLogTest.convolution_apply]
    simp only [CompactLogTest.involution_apply]
  rw [CompactLogTest.convolutionSquare_apply,
    CompactLogTest.convolutionSquare_apply,
    CompactLogTest.convolutionSquare_apply, hcross, hcongr,
    MeasureTheory.integral_add' hint1 (hint2.add hint34),
    MeasureTheory.integral_add' hint2 hint34,
    MeasureTheory.integral_add' hint3 hint4]
  ring

/-- Integrability of the cross integrand, transported from the three squares
by linearity of the archimedean integrand. -/
theorem integrableOn_archimedeanIntegrand_crossTest (f g : CompactLogTest) :
    IntegrableOn (archimedeanIntegrand (crossTest f g)) (Set.Ioi (0 : ℝ)) := by
  have hint0 := integrableOn_archimedeanIntegrand_convolutionSquare (sumTest f g)
  have hint1 := integrableOn_archimedeanIntegrand_convolutionSquare f
  have hint2 := integrableOn_archimedeanIntegrand_convolutionSquare g
  have hpoint : ∀ y : ℝ,
      archimedeanIntegrand (crossTest f g) y =
        archimedeanIntegrand (sumTest f g).convolutionSquare y -
          (archimedeanIntegrand f.convolutionSquare y +
            archimedeanIntegrand g.convolutionSquare y) := by
    intro y
    have hy := convolutionSquare_sumTest_apply f g y
    have hny := convolutionSquare_sumTest_apply f g (-y)
    have hn0 := convolutionSquare_sumTest_apply f g 0
    simp only [archimedeanIntegrand, archimedeanNumerator]
    rw [hy, hny, hn0]
    simp [mul_add]
    ring
  have hfun : (archimedeanIntegrand (crossTest f g)) =
      fun y : ℝ => archimedeanIntegrand (sumTest f g).convolutionSquare y -
        (archimedeanIntegrand f.convolutionSquare y +
          archimedeanIntegrand g.convolutionSquare y) :=
    funext hpoint
  rw [hfun]
  exact hint0.sub (hint1.add hint2)

/-- EXACT QUADRATIC DECOMPOSITION.  The archimedean term of the convolution
square of a pointwise sum is the sum of the two square terms plus the
archimedean term of the polarized cross. -/
theorem archimedeanTerm_convolutionSquare_sumTest (f g : CompactLogTest) :
    archimedeanTerm (sumTest f g).convolutionSquare =
      archimedeanTerm f.convolutionSquare + archimedeanTerm g.convolutionSquare +
        archimedeanTerm (crossTest f g) := by
  have hint1 := integrableOn_archimedeanIntegrand_convolutionSquare f
  have hint2 := integrableOn_archimedeanIntegrand_convolutionSquare g
  have hintC := integrableOn_archimedeanIntegrand_crossTest f g
  have hpoint : ∀ y : ℝ,
      archimedeanIntegrand (sumTest f g).convolutionSquare y =
        (archimedeanIntegrand f.convolutionSquare +
          (fun z : ℝ => archimedeanIntegrand g.convolutionSquare z +
            archimedeanIntegrand (crossTest f g) z)) y := by
    intro y
    have hy := convolutionSquare_sumTest_apply f g y
    have hny := convolutionSquare_sumTest_apply f g (-y)
    have hn0 := convolutionSquare_sumTest_apply f g 0
    simp only [archimedeanIntegrand, archimedeanNumerator, Pi.add_apply]
    rw [hy, hny, hn0]
    simp [mul_add]
    ring
  have hint234 : IntegrableOn (fun z : ℝ =>
      archimedeanIntegrand g.convolutionSquare z +
        archimedeanIntegrand (crossTest f g) z) (Set.Ioi (0 : ℝ)) volume :=
    hint2.add hintC
  unfold archimedeanTerm
  rw [convolutionSquare_sumTest_apply f g 0]
  have hsplit : ∫ y in Set.Ioi (0 : ℝ),
      archimedeanIntegrand (sumTest f g).convolutionSquare y =
      (∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand f.convolutionSquare y) +
        ((∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand g.convolutionSquare y) +
          ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand (crossTest f g) y) := by
    have step1 : ∫ y in Set.Ioi (0 : ℝ),
        archimedeanIntegrand (sumTest f g).convolutionSquare y =
        ∫ y in Set.Ioi (0 : ℝ),
          (archimedeanIntegrand f.convolutionSquare +
            (fun z : ℝ => archimedeanIntegrand g.convolutionSquare z +
              archimedeanIntegrand (crossTest f g) z)) y :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => hpoint y)
    rw [step1, MeasureTheory.integral_add' hint1 hint234,
      MeasureTheory.integral_add hint2 hintC]
  rw [hsplit]
  simp [Complex.add_re, mul_add]
  ring

/-! ### The odd kill -/

/-- THE ODD KILL.  The archimedean term of any odd test vanishes identically:
the constant term is zero and the whole integrand numerator is zero by
oddness.  No integrability input is needed. -/
theorem archimedeanTerm_eq_zero_of_test_odd (F : CompactLogTest)
    (hodd : ∀ x : ℝ, F.test (-x) = -F.test x) :
    archimedeanTerm F = 0 := by
  have hzero : F.test 0 = 0 := by
    have h := hodd 0
    simp only [neg_zero] at h
    have h3 : -F.test 0 + F.test 0 = 0 := neg_add_cancel _
    rw [← h] at h3
    have h4 : (2 : ℂ) * F.test 0 = 0 := by
      rw [two_mul]
      exact h3
    exact ((mul_eq_zero (b := F.test 0)).mp h4).resolve_left (by norm_num)
  have hint0 : ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand F y = 0 := by
    have hEq : ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand F y =
        ∫ y in Set.Ioi (0 : ℝ), (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [archimedeanIntegrand, archimedeanNumerator, hzero]
      simp [hodd]
    rw [hEq]
    simp
  simp only [archimedeanTerm, hzero, hint0, mul_zero, add_zero]
  rfl

/-! ### The even/odd cross cancellation -/

theorem laplaceAt_neg_of_test_odd (u : CompactLogTest)
    (hodd : ∀ x : ℝ, u.test (-x) = -u.test x) (s : ℂ) :
    CompactLogTest.laplaceAt u s = -CompactLogTest.laplaceAt u (-s) := by
  have hsplit : (CompactLogTest.exponentialWeight u s).test =
      fun x : ℝ => -((CompactLogTest.exponentialWeight u (-s)).test (-x)) := by
    funext x
    simp [CompactLogTest.exponentialWeight_apply, hodd]
  unfold CompactLogTest.laplaceAt
  rw [hsplit, integral_neg, integral_neg_eq_self]

/-- Odd Mellin blindness: an odd test evaluates to zero at the origin, so the
mass-zero node of the triple vanishing set cannot be served by an odd
correction. -/
theorem laplaceAt_eq_zero_of_test_odd (u : CompactLogTest)
    (hodd : ∀ x : ℝ, u.test (-x) = -u.test x) :
    CompactLogTest.laplaceAt u 0 = 0 := by
  have h := laplaceAt_neg_of_test_odd u hodd 0
  simp only [neg_zero] at h
  have h3 : -CompactLogTest.laplaceAt u 0 + CompactLogTest.laplaceAt u 0 = 0 :=
    neg_add_cancel _
  rw [← h] at h3
  have h4 : (2 : ℂ) * CompactLogTest.laplaceAt u 0 = 0 := by
    rw [two_mul]
    exact h3
  exact ((mul_eq_zero (b := CompactLogTest.laplaceAt u 0)).mp h4).resolve_left
    (by norm_num)

/-- The polarized cross of an even test and an odd test is odd. -/
theorem test_neg_crossTest_of_even_odd (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x) :
    ∀ y : ℝ, (crossTest f g).test (-y) = -(crossTest f g).test y := by
  have hfeven : ∀ x : ℝ, f.involution.test (-x) = f.involution.test x := by
    intro x
    simp [CompactLogTest.involution_apply, hf]
  have hgodd : ∀ x : ℝ, g.involution.test (-x) = -g.involution.test x := by
    intro x
    rw [CompactLogTest.involution_apply, CompactLogTest.involution_apply, hg x]
    simp
  have h1 : ∀ y : ℝ,
      (f.involution.convolution g).test (-y) =
        -(f.involution.convolution g).test y := by
    intro y
    rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
    have hsubst : ∫ t : ℝ, f.involution.test t * g.test (-y - t) =
        ∫ t : ℝ, f.involution.test (-t) * g.test (-y + t) := by
      rw [← integral_neg_eq_self
        (fun t : ℝ => f.involution.test t * g.test (-y - t)) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [sub_neg_eq_add]
    rw [hsubst]
    have hpt : ∀ t : ℝ,
        f.involution.test (-t) * g.test (-y + t) =
          -(f.involution.test t * g.test (y - t)) := by
      intro t
      have harg : -y + t = -(y - t) := by ring
      rw [harg, hfeven t, hg (y - t)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t),
      integral_neg]
  have h2 : ∀ y : ℝ,
      (g.involution.convolution f).test (-y) =
        -(g.involution.convolution f).test y := by
    intro y
    rw [CompactLogTest.convolution_apply, CompactLogTest.convolution_apply]
    have hsubst : ∫ t : ℝ, g.involution.test t * f.test (-y - t) =
        ∫ t : ℝ, g.involution.test (-t) * f.test (-y + t) := by
      rw [← integral_neg_eq_self
        (fun t : ℝ => g.involution.test t * f.test (-y - t)) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [sub_neg_eq_add]
    rw [hsubst]
    have hpt : ∀ t : ℝ,
        g.involution.test (-t) * f.test (-y + t) =
          -(g.involution.test t * f.test (y - t)) := by
      intro t
      have harg : -y + t = -(y - t) := by ring
      rw [harg, hgodd t, hf]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t),
      integral_neg]
  intro y
  rw [crossTest_apply, crossTest_apply, h1 y, h2 y]
  ring

/-- HEADLINE: on the even/odd class the archimedean quadratic form is EXACTLY
the two-term anchor - the polarized cross is dead by the odd kill. -/
theorem archimedeanTerm_convolutionSquare_sumTest_of_even_odd (f g : CompactLogTest)
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x) :
    archimedeanTerm (sumTest f g).convolutionSquare =
      archimedeanTerm f.convolutionSquare + archimedeanTerm g.convolutionSquare := by
  rw [archimedeanTerm_convolutionSquare_sumTest f g,
    archimedeanTerm_eq_zero_of_test_odd (crossTest f g)
      (test_neg_crossTest_of_even_odd f g hf hg)]
  ring

/-! ### The rescue gate -/

/-- THE RESCUE GATE.  An even base `f` and an odd correction `g` whose nodal
sums vanish on the triple set, which detects `rho`, which carries root
support, and whose two-term anchor is strictly positive, satisfy the FULL
root-supported healthy detector gate of record 1081.  The certificate side
owes exactly the two anchor terms; the cross terms are dead by symmetry. -/
theorem rootSupportedGate_of_evenBase_oddCorrection
    {rho : ℂ}
    {f g : CompactLogTest}
    (hf : ∀ x : ℝ, f.test (-x) = f.test x)
    (hg : ∀ x : ℝ, g.test (-x) = -g.test x)
    (hf0 : CompactLogTest.laplaceAt f 0 = 0)
    (hhalf : CompactLogTest.laplaceAt f (1 / 2 : ℂ) +
      CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0)
    (hone : CompactLogTest.laplaceAt f 1 + CompactLogTest.laplaceAt g 1 = 0)
    (hdet : CompactLogTest.laplaceAt (sumTest f g) rho ≠ 0)
    (hsupp : Function.support (sumTest f g).test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hpos : 0 < C1SameOwnerWeil.archimedeanTerm f.convolutionSquare +
      C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) :
    rootSupportedHealthyDetectorGate rho := by
  refine ⟨sumTest f g, ?_, hsupp⟩
  have hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet (sumTest f g) := by
    intro p _hp
    change CompactLogTest.laplaceAt (sumTest f g) (criticalVanishingPointValue p) = 0
    rw [laplaceAt_sumTest]
    cases p
    · have hv : criticalVanishingPointValue CriticalVanishingPoint.zero = 0 := rfl
      rw [hv, hf0, laplaceAt_eq_zero_of_test_odd g hg]
      simp
    · have hv : criticalVanishingPointValue CriticalVanishingPoint.half =
        (1 / 2 : ℂ) := rfl
      rw [hv]
      exact hhalf
    · have hv : criticalVanishingPointValue CriticalVanishingPoint.one = 1 := rfl
      rw [hv]
      exact hone
  have hsqSupport : Function.support (sumTest f g).convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
    have hw := CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo
      (sumTest f g) hsupp
    have htwo : (2 : Real) * (Real.log 2 / 2) = Real.log 2 := by ring
    rwa [htwo] at hw
  have harch : 0 < C1SameOwnerWeil.archimedeanTerm
      (sumTest f g).convolutionSquare := by
    rw [archimedeanTerm_convolutionSquare_sumTest_of_even_odd f g hf hg]
    exact hpos
  exact
    { compactSupportSmooth := C1.healthyCC20CompactSupportSmooth (sumTest f g)
      vanishesOnF := hvanishes
      detectsRho := hdet
      weilSquareSumPositive :=
        (weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
          (sumTest f g) hvanishes hsqSupport).mpr harch }

end C1HealthyDetectorArchRescue
end Source
end ConnesWeilRH
