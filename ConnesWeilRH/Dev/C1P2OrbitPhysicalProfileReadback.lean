import ConnesWeilRH.Dev.C1P2SignedBudget

/-!
# P2 orbit physical-profile readback

This leaf exposes the physical kernel sampled by the finite visible-prime
aggregate of the actual `OrbitG8Geometry` owner.  It is an exact same-owner
identity: no Mellin-to-physical implication, sign estimate, or RH conclusion
is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2OrbitPhysicalProfileReadback

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1G8R0OrbitGeometry
open C1P2BilateralProfile
open C1P2SignedBudget
open C1SameOwnerWeil
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The unshifted convolution factor used by the selected orbit owner. -/
def orbitRawFactor {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : CompactLogTest :=
  (convolutionIterate geometry.base geometry.orbitIndex).convolution
    geometry.correction

theorem orbitRawFactor_support_subset
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Function.support (orbitRawFactor geometry).test ⊆
      Set.Ioo (-((geometry.orbitIndex + 2 : Nat) : Real))
        (((geometry.orbitIndex + 2 : Nat) : Real)) := by
  unfold orbitRawFactor
  have h := convolutionIterate_convolution_support_subset_Ioo
    geometry.base geometry.correction geometry.base_support
    geometry.correction_support geometry.orbitIndex
  convert h using 1 <;> norm_num [Nat.cast_add, Nat.cast_one] <;> ring

/-- The exact physical kernel produced by applying the half-density shift
before taking the genuine convolution square. -/
def orbitPhysicalKernel {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) : Complex :=
  integral (μ := volume) fun t : Real =>
    star
        (Complex.exp ((1 / 2 : Complex) * ((-t : Real) : Complex)) *
          (orbitRawFactor geometry).test (-t)) *
        (Complex.exp ((1 / 2 : Complex) * ((x - t : Real) : Complex)) *
          (orbitRawFactor geometry).test (x - t))

/-- The same kernel after the two half-density factors have been combined.
This is the form in which a signed physical estimate can inspect the actual
raw factor without carrying two separate exponential multipliers. -/
def orbitWeightedKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : Real) : Complex :=
  Complex.exp (((x / 2 - t : Real) : Complex)) *
    star ((orbitRawFactor geometry).test (-t)) *
      (orbitRawFactor geometry).test (x - t)

theorem orbitPhysicalKernel_eq_integral_weightedKernel
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    orbitPhysicalKernel geometry x =
      integral (μ := volume) (fun t : Real =>
        orbitWeightedKernelIntegrand geometry x t) := by
  unfold orbitPhysicalKernel orbitWeightedKernelIntegrand
  apply integral_congr_ae
  filter_upwards with t
  have hstar :
      star (Complex.exp ((1 / 2 : Complex) * ((-t : Real) : Complex))) =
        Complex.exp (((-t / 2 : Real) : Complex)) := by
    apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im] <;> ring
  simp only [star_mul]
  rw [hstar]
  have hexp :
      Complex.exp (((-t / 2 : Real) : Complex)) *
          Complex.exp ((1 / 2 : Complex) * ((x - t : Real) : Complex)) =
        Complex.exp (((x / 2 - t : Real) : Complex)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num
    ring
  calc
    star ((orbitRawFactor geometry).test (-t)) *
          Complex.exp (((-t / 2 : Real) : Complex)) *
          (Complex.exp ((1 / 2 : Complex) * ((x - t : Real) : Complex)) *
            (orbitRawFactor geometry).test (x - t)) =
        (Complex.exp (((-t / 2 : Real) : Complex)) *
          Complex.exp ((1 / 2 : Complex) * ((x - t : Real) : Complex))) *
          (star ((orbitRawFactor geometry).test (-t)) *
            (orbitRawFactor geometry).test (x - t)) := by ring
    _ = Complex.exp (((x / 2 - t : Real) : Complex)) *
          (star ((orbitRawFactor geometry).test (-t)) *
            (orbitRawFactor geometry).test (x - t)) := by rw [hexp]
    _ = Complex.exp (((x / 2 - t : Real) : Complex)) *
          star ((orbitRawFactor geometry).test (-t)) *
            (orbitRawFactor geometry).test (x - t) := by ring

/-- Pointwise readback of the actual selected square into its unshifted
base/correction convolution and the explicit half-density kernel. -/
theorem convolutionSquare_eq_orbitPhysicalKernel
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    g.convolutionSquare.test x = orbitPhysicalKernel geometry x := by
  rw [CompactLogTest.convolutionSquare_apply]
  unfold orbitPhysicalKernel
  apply integral_congr_ae
  filter_upwards with t
  have hneg : g.test (-t) =
      (orbitRawFactor geometry).test (-t) *
        Complex.exp ((1 / 2 : Complex) * ((-t : Real) : Complex)) := by
    have h := congrArg (fun f : CompactLogTest => f.test (-t))
      geometry.selected_owner_test
    simpa [orbitRawFactor, selectedOwner_sourceTest, halfDensityShift_apply,
      mul_comm] using h
  have hpos : g.test (x - t) =
      (orbitRawFactor geometry).test (x - t) *
        Complex.exp ((1 / 2 : Complex) * ((x - t : Real) : Complex)) := by
    have h := congrArg (fun f : CompactLogTest => f.test (x - t))
      geometry.selected_owner_test
    simpa [orbitRawFactor, selectedOwner_sourceTest, halfDensityShift_apply,
      mul_comm] using h
  rw [hneg, hpos]
  simp only [map_mul, star_mul, Complex.star_def]
  ring

theorem orbitPhysicalKernel_eq_zero_of_not_mem_doubled_support
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real)
    (hx : x ∉ Set.Ioo
      (-((2 : Real) * ((geometry.orbitIndex + 2 : Nat) : Real)))
      ((2 : Real) * ((geometry.orbitIndex + 2 : Nat) : Real))) :
    orbitPhysicalKernel geometry x = 0 := by
  have hsupport : Function.support g.test ⊆ Set.Icc
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real)) := by
    intro y hy
    exact Set.Ioo_subset_Icc_self (geometry.support_bound hy)
  have hsquare :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have hzero : g.convolutionSquare.test x = 0 := by
    by_contra hne
    exact hx (hsquare (Function.mem_support.mpr hne))
  rw [← convolutionSquare_eq_orbitPhysicalKernel geometry x, hzero]

theorem orbitPhysicalKernel_neg_eq_star
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    orbitPhysicalKernel geometry (-x) =
      star (orbitPhysicalKernel geometry x) := by
  rw [← convolutionSquare_eq_orbitPhysicalKernel geometry (-x),
    ← convolutionSquare_eq_orbitPhysicalKernel geometry x,
    CompactLogTest.convolutionSquare_neg]

theorem bilateralProfile_eq_two_re_orbitPhysicalKernel
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    bilateralProfile g.convolutionSquare x =
      ((2 * (orbitPhysicalKernel geometry x).re : Real) : Complex) := by
  rw [bilateralProfile_convolutionSquare_eq_two_re,
    ← convolutionSquare_eq_orbitPhysicalKernel geometry x]

theorem orbitPhysicalKernel_zero_re_nonnegative
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ (orbitPhysicalKernel geometry 0).re := by
  rw [← convolutionSquare_eq_orbitPhysicalKernel geometry 0]
  exact g.convolutionSquare_zero_re_nonnegative

theorem finitePrimeTerm_eq_orbitPhysicalKernel_re
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    finitePrimeTerm g.convolutionSquare n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (2 * (orbitPhysicalKernel geometry (Real.log n)).re) := by
  rw [C1P2BilateralProfile.finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re,
    bilateralProfile_eq_two_re_orbitPhysicalKernel geometry]
  simp

/-- The bilateral observable at every physical coordinate is the sum of the
two explicit orbit kernels.  In particular this applies at `plus/minus log n` for
every visible prime power. -/
theorem bilateralProfile_eq_orbitPhysicalKernel_add_neg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    bilateralProfile g.convolutionSquare x =
      orbitPhysicalKernel geometry x + orbitPhysicalKernel geometry (-x) := by
  unfold bilateralProfile
  rw [convolutionSquare_eq_orbitPhysicalKernel geometry,
    convolutionSquare_eq_orbitPhysicalKernel geometry]

/-- Exact finite-range readback of the same-owner prime contribution into
the constructor-selected correction's physical kernel. -/
theorem finitePrimeSum_eq_orbitPhysicalKernel_range
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (orbitPhysicalKernel geometry (Real.log n) +
            orbitPhysicalKernel geometry (-Real.log n)).re) := by
  rw [finitePrimeSum_eq_sum_range_of_orbitG8Geometry geometry]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [C1P2BilateralProfile.finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re,
    bilateralProfile_eq_orbitPhysicalKernel_add_neg geometry]

/-- The live B5 gate is exactly an Archimedean term plus the finite weighted
sum of the actual correction kernel.  This is the analytic producer boundary
left after the Mellin/physical separation theorem. -/
theorem orbitWindowSemiLocalGate_iff_physicalKernelBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
              (orbitPhysicalKernel geometry (Real.log n) +
                orbitPhysicalKernel geometry (-Real.log n)).re) ≤ 0 := by
  rw [C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate,
    finitePrimeSum_eq_orbitPhysicalKernel_range geometry]

/-! The physical-kernel and credit/deficit views are two exact readbacks of
the same selected-owner gate.  This is the handoff point for an analytic
estimate stated in whichever coordinates control the actual correction. -/
theorem physicalKernelBudget_iff_signedBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (archimedeanTerm g.convolutionSquare +
          Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
              (orbitPhysicalKernel geometry (Real.log n) +
                orbitPhysicalKernel geometry (-Real.log n)).re) ≤ 0) ↔
      archimedeanTerm g.convolutionSquare +
          signedProfileCredit g (orbitVisiblePrimeRange geometry) ≤
        signedProfileDeficit g (orbitVisiblePrimeRange geometry) := by
  constructor
  · intro h
    exact (orbitWindowSemiLocalGate_iff_signedBudget geometry).mp
      ((orbitWindowSemiLocalGate_iff_physicalKernelBudget geometry).mpr h)
  · intro h
    exact (orbitWindowSemiLocalGate_iff_physicalKernelBudget geometry).mp
      ((orbitWindowSemiLocalGate_iff_signedBudget geometry).mpr h)

/-- The physical-kernel form is already sufficient for the existing B5 exit.
This is only a consumer bridge: the required physical-kernel inequality is
still an analytic producer obligation. -/
theorem sourceRH_of_right_orbitGeometry_physicalKernelBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
                  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                    (orbitPhysicalKernel geometry (Real.log n) +
                      orbitPhysicalKernel geometry (-Real.log n)).re) ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_signedBudget
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  exact (physicalKernelBudget_iff_signedBudget geometry).mp hbudget

end
end C1P2OrbitPhysicalProfileReadback
end Source
end ConnesWeilRH
