/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientContractionBound
import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt
import Mathlib.Analysis.MeanInequalities

/-!
# Root-completed fixed-quotient first jet

Proof 433 bounds the literal fixed-quotient first jet by a physical pair whose
prolate coordinate is not homogeneous under scaling of the selected root.  This
module returns to Proof 405's two-branch scalar owner and splits the positive
detector `C† C` before any Hilbert--Schmidt energy is taken.

The resulting three terms contain the left root and the right root exactly once:
one prolate-range term and the two Leibniz orientations of the second-support
commutator.  This is an exact same-object identity.  No Schatten estimate,
support--Sobolev bound, endpoint telescope, Gate 3U, or RH premise is stored.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedFirstJet

open MeasureTheory
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientFirstJet
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSFixedQuotientCarrier
open CC20Concrete.CompactRootHalfLinePair
open SelectedCrossingKernel

noncomputable local instance sourceSoninIntersectionCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace
      (↑(((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule) ⊓
        ((ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule))) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

variable {A : Type*} [Ring A]

/-- The additive commutator obeys the Leibniz rule in an arbitrary
noncommutative ring. -/
theorem commutator_mul_eq_root_split
    (leftRoot rightRoot operator : A) :
    CCM24FiniteSTwoSidedRootRecombination.commutator
        (leftRoot * rightRoot) operator =
      leftRoot * CCM24FiniteSTwoSidedRootRecombination.commutator
          rightRoot operator +
        CCM24FiniteSTwoSidedRootRecombination.commutator leftRoot operator *
          rightRoot := by
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  noncomm_ring

/-- Projecting the output of a commutator onto the complementary corner
deletes the branch which already lands in the projection range. -/
theorem band_complement_mul_commutator_eq
    (band leftRoot projection : A)
    (hProjection : IsIdempotentElem projection) :
    band * (1 - projection) *
        CCM24FiniteSTwoSidedRootRecombination.commutator leftRoot projection =
      band * (1 - projection) * leftRoot * projection := by
  have hzero : (1 - projection) * projection = 0 := by
    calc
      (1 - projection) * projection = projection - projection * projection := by
        noncomm_ring
      _ = 0 := by rw [hProjection]; noncomm_ring
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    band * (1 - projection) * (leftRoot * projection - projection * leftRoot) =
        band * (1 - projection) * leftRoot * projection -
          band * ((1 - projection) * projection) * leftRoot := by
      noncomm_ring
    _ = band * (1 - projection) * leftRoot * projection := by
      rw [hzero]
      noncomm_ring

/-- If a projection absorbs the next input, a root commutator is exactly the
complementary output corner of that root. -/
theorem commutator_mul_absorbed_eq_complement_mul
    (rightRoot projection inner tail : A)
    (hProjectionInner : projection * inner = inner) :
    CCM24FiniteSTwoSidedRootRecombination.commutator rightRoot projection *
        inner * tail =
      (1 - projection) * rightRoot * inner * tail := by
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    (rightRoot * projection - projection * rightRoot) * inner * tail =
        rightRoot * (projection * inner) * tail -
          projection * rightRoot * inner * tail := by
      noncomm_ring
    _ = rightRoot * inner * tail - projection * rightRoot * inner * tail := by
      rw [hProjectionInner]
    _ = (1 - projection) * rightRoot * inner * tail := by
      noncomm_ring

/-- Proof 405's two surviving branches after the detector product has been
split at root level.  Every summand contains both roots exactly once. -/
def rootCompletedSecondSupportCorner
    (band inner secondSupport leftRoot rightRoot transport : A) : A :=
  band * secondSupport * leftRoot * rightRoot * inner * transport * band +
    band * (1 - secondSupport) * leftRoot *
      CCM24FiniteSTwoSidedRootRecombination.commutator rightRoot
        secondSupport * inner * transport * band +
    band * (1 - secondSupport) *
      CCM24FiniteSTwoSidedRootRecombination.commutator leftRoot
        secondSupport * rightRoot * inner * transport * band

/-- The fixed-quotient detector corner is exactly the root-completed
three-branch expression. -/
theorem detector_innerCorner_transport_eq_rootCompleted
    (band inner secondSupport leftRoot rightRoot transport : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport * inner = inner) :
    band * CCM24FiniteSTwoSidedRootRecombination.commutator
        (leftRoot * rightRoot) inner * inner * transport * band =
      rootCompletedSecondSupportCorner band inner secondSupport leftRoot
        rightRoot transport := by
  rw [detector_innerCorner_transport_eq_secondSupport_twoBranch band inner
    secondSupport (leftRoot * rightRoot) transport hInner hBandInner hSecond
    hSecondInner]
  rw [commutator_mul_eq_root_split]
  unfold rootCompletedSecondSupportCorner
  noncomm_ring

/-- The three root-completed branches recombine before estimation to the
single unsplit root pairing.  The second-support projection is an exact
bookkeeping device here; it is not three independent analytic data. -/
theorem rootCompletedSecondSupportCorner_eq_unsplit
    (band inner secondSupport leftRoot rightRoot transport : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport * inner = inner) :
    rootCompletedSecondSupportCorner band inner secondSupport leftRoot
        rightRoot transport =
      band * leftRoot * rightRoot * inner * transport * band := by
  rw [← detector_innerCorner_transport_eq_rootCompleted band inner
    secondSupport leftRoot rightRoot transport hInner hBandInner hSecond
    hSecondInner]
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    band * (leftRoot * rightRoot * inner -
          inner * (leftRoot * rightRoot)) * inner * transport * band =
        band * leftRoot * rightRoot * (inner * inner) * transport * band -
          (band * inner) * leftRoot * rightRoot * inner * transport * band := by
      noncomm_ring
    _ = band * leftRoot * rightRoot * inner * transport * band := by
      rw [hInner, hBandInner]
      noncomm_ring

/-- Centering the transport at the identity converts the unsplit detector
pair into one fixed projection-commutator sandwich.  This is the algebraic
step which allows a trace-class estimate for the fixed commutator to be used
before any causal-renewal expansion. -/
theorem centeredDetectorPair_eq_fixedCommutatorSandwich
    (band inner detector transport : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0) :
    band * detector * inner * (transport - 1) * band =
      band * CCM24FiniteSTwoSidedRootRecombination.commutator detector inner *
        inner * transport * band := by
  have hleft :
      band * detector * inner * (transport - 1) * band =
        band * detector * inner * transport * band := by
    calc
      band * detector * inner * (transport - 1) * band =
          band * detector * inner * transport * band -
            band * detector * (inner * band) := by
        noncomm_ring
      _ = band * detector * inner * transport * band := by
        rw [hInnerBand]
        noncomm_ring
  rw [hleft]
  symm
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    band * (detector * inner - inner * detector) * inner * transport * band =
        band * detector * (inner * inner) * transport * band -
          (band * inner) * detector * inner * transport * band := by
      noncomm_ring
    _ = band * detector * inner * transport * band := by
      rw [hInner, hBandInner]
      noncomm_ring

/-! A multiplicative trace consumer is the correct quantitative companion to
the root-completed owner.  Unlike the arithmetic-energy bound
`2ab <= a^2 + b^2`, this estimate preserves independent scaling of the two
Hilbert--Schmidt legs. -/

theorem ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) basis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis data.traceProduct‖ ≤
      Real.sqrt (∑' i, ‖data.left (basis i)‖ ^ 2) *
        Real.sqrt (∑' i, ‖data.right (basis i)‖ ^ 2) := by
  have hHolder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (f := fun i => ‖data.left (basis i)‖)
    (g := fun i => ‖data.right (basis i)‖)
    Real.HolderConjugate.two_two
    (fun i => norm_nonneg (data.left (basis i)))
    (fun i => norm_nonneg (data.right (basis i)))
    (by simpa only [Real.rpow_two] using data.left_summable_normSq)
    (by simpa only [Real.rpow_two] using data.right_summable_normSq)
  have hpoint (i : ι) :
      ‖inner ℂ (data.left (basis i)) (data.right (basis i))‖ ≤
        ‖data.left (basis i)‖ * ‖data.right (basis i)‖ :=
    norm_inner_le_norm _ _
  have hinnerNorm : Summable fun i =>
      ‖inner ℂ (data.left (basis i)) (data.right (basis i))‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      hpoint hHolder.1
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, inner ℂ (basis i) (data.traceProduct (basis i))‖ ≤
        ∑' i, ‖inner ℂ (basis i) (data.traceProduct (basis i))‖ := by
      apply norm_tsum_le_tsum_norm
      exact hinnerNorm.congr fun i => by
        rw [data.traceProduct_diagonal]
    _ = ∑' i, ‖inner ℂ (data.left (basis i))
        (data.right (basis i))‖ := by
      apply tsum_congr
      intro i
      rw [data.traceProduct_diagonal]
    _ ≤ ∑' i, ‖data.left (basis i)‖ *
        ‖data.right (basis i)‖ :=
      hinnerNorm.tsum_le_tsum hpoint hHolder.1
    _ ≤ Real.sqrt (∑' i, ‖data.left (basis i)‖ ^ 2) *
        Real.sqrt (∑' i, ‖data.right (basis i)‖ ^ 2) := by
      simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hHolder.2

theorem l2Sum_left_basisEnergy_eq_add
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {basis : HilbertBasis ι ℂ H}
    (first : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) basis)
    (second : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := K) basis) :
    (∑' i, ‖(CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
        first second).left (basis i)‖ ^ 2) =
      (∑' i, ‖first.left (basis i)‖ ^ 2) +
        ∑' i, ‖second.left (basis i)‖ ^ 2 := by
  calc
    _ = ∑' i, (‖first.left (basis i)‖ ^ 2 +
        ‖second.left (basis i)‖ ^ 2) := by
      apply tsum_congr
      intro i
      change ‖WithLp.toLp 2
        (first.left (basis i), second.left (basis i))‖ ^ 2 = _
      exact WithLp.prod_norm_sq_eq_of_L2 _
    _ = _ := first.left_summable_normSq.tsum_add
      second.left_summable_normSq

theorem l2Sum_right_basisEnergy_eq_add
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {basis : HilbertBasis ι ℂ H}
    (first : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) basis)
    (second : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := K) basis) :
    (∑' i, ‖(CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
        first second).right (basis i)‖ ^ 2) =
      (∑' i, ‖first.right (basis i)‖ ^ 2) +
        ∑' i, ‖second.right (basis i)‖ ^ 2 := by
  calc
    _ = ∑' i, (‖first.right (basis i)‖ ^ 2 +
        ‖second.right (basis i)‖ ^ 2) := by
      apply tsum_congr
      intro i
      change ‖WithLp.toLp 2
        (first.right (basis i), second.right (basis i))‖ ^ 2 = _
      exact WithLp.prod_norm_sq_eq_of_L2 _
    _ = _ := first.right_summable_normSq.tsum_add
      second.right_summable_normSq

/-- Postcomposition by a contraction cannot increase Hilbert--Schmidt square
energy in a fixed Hilbert basis. -/
theorem basisEnergy_postcomp_le_of_norm_le_one
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] G)
    (bounded : G →L[ℂ] K)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2)
    (hbounded : ‖bounded‖ ≤ 1) :
    (∑' i, ‖(bounded ∘L operator) (basis i)‖ ^ 2) ≤
      ∑' i, ‖operator (basis i)‖ ^ 2 := by
  have hcomposed := CC20Concrete.PositiveTrace.summable_normSq_postcomp basis
    operator bounded hoperator
  apply hcomposed.tsum_le_tsum _ hoperator
  intro i
  rw [ContinuousLinearMap.comp_apply]
  calc
    ‖bounded (operator (basis i))‖ ^ 2 ≤
        (‖bounded‖ * ‖operator (basis i)‖) ^ 2 := by
      gcongr
      exact bounded.le_opNorm _
    _ ≤ (1 * ‖operator (basis i)‖) ^ 2 := by
      gcongr
    _ = ‖operator (basis i)‖ ^ 2 := by ring

/-- A pointwise bound on a continuous compact kernel gives an explicit
Hilbert--Schmidt square bound in every Hilbert basis. -/
theorem continuousKernel_basisEnergy_le_measure_mul_sq
    {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
      [MeasurableSpace Y] [BorelSpace Y]
    (muX : Measure X) (muY : Measure Y)
    [IsFiniteMeasure muX] [IsFiniteMeasure muY]
    (kernel : ContinuousMap (Y × X) ℂ)
    {ι : Type*} (basis : HilbertBasis ι ℂ (Lp ℂ 2 muX))
    (bound : ℝ) (hbound_nonneg : 0 ≤ bound)
    (hkernel : ∀ y x, ‖kernel (y, x)‖ ≤ bound) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        muX muY kernel (basis i)‖ ^ 2) ≤
      muY.real Set.univ * (muX.real Set.univ * bound ^ 2) := by
  have hsection (y : Y) :
      ‖CC20Concrete.ContinuousKernelHilbertSchmidt.sectionToLp
          muX kernel y‖ ^ 2 ≤
        muX.real Set.univ * bound ^ 2 := by
    unfold CC20Concrete.ContinuousKernelHilbertSchmidt.sectionToLp
    rw [CC20Concrete.ContinuousKernelHilbertSchmidt.norm_continuousMap_toLp_sq]
    have hintegrable : Integrable (fun x : X => ‖kernel (y, x)‖ ^ 2) muX := by
      have hcontinuous : Continuous (fun x : X => ‖kernel (y, x)‖ ^ 2) :=
        (CC20Concrete.ContinuousKernelHilbertSchmidt.kernelSection
          kernel y).continuous.norm.pow 2
      simpa only [Measure.restrict_univ] using
        (hcontinuous.continuousOn.integrableOn_compact
          (μ := muX) isCompact_univ).integrable
    calc
      (∫ x : X, ‖kernel (y, x)‖ ^ 2 ∂muX) ≤
          ∫ _x : X, bound ^ 2 ∂muX := by
        apply integral_mono hintegrable (integrable_const _)
        intro x
        nlinarith [sq_nonneg (‖kernel (y, x)‖ - bound),
          norm_nonneg (kernel (y, x)), hkernel y x]
      _ = muX.real Set.univ * bound ^ 2 := by
        rw [integral_const]
        simp only [smul_eq_mul]
  have hsectionEnergy :
      (∫ y : Y,
          ‖CC20Concrete.ContinuousKernelHilbertSchmidt.sectionToLp
            muX kernel y‖ ^ 2 ∂muY) ≤
        muY.real Set.univ * (muX.real Set.univ * bound ^ 2) := by
    calc
      (∫ y : Y,
          ‖CC20Concrete.ContinuousKernelHilbertSchmidt.sectionToLp
            muX kernel y‖ ^ 2 ∂muY) ≤
          ∫ _y : Y, muX.real Set.univ * bound ^ 2 ∂muY := by
        apply integral_mono
          (CC20Concrete.ContinuousKernelHilbertSchmidt.section_normSq_integrable
            muX muY kernel) (integrable_const _)
        exact hsection
      _ = muY.real Set.univ * (muX.real Set.univ * bound ^ 2) := by
        rw [integral_const]
        simp only [smul_eq_mul]
  refine tsum_le_of_sum_le' ?_ ?_
  · positivity
  intro terms
  exact
    (CC20Concrete.ContinuousKernelHilbertSchmidt.finite_basis_sum_le_section_energy
      muX muY kernel basis terms).trans hsectionEnergy

/-! The three compact half-line kernels now receive explicit homogeneous
support bounds.  The measure-form statements are the reusable interface; the
polynomial forms expose the exact window cost when `a ≤ c`. -/

theorem boundaryOutputInterval_volume_real_eq_sub
    (a c : ℝ) (hac : a ≤ c) :
    (volume : Measure (BoundaryOutputInterval a c)).real Set.univ = c - a := by
  change (volume : Measure (Set.Icc (-c - 0) (-a + 0))).real Set.univ = c - a
  rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem boundaryNegativeInputInterval_volume_real_eq_sub
    (a c : ℝ) (hac : a ≤ c) :
    (volume : Measure (BoundaryNegativeInputInterval a c)).real Set.univ =
      c - a := by
  change (volume : Measure (Set.Icc (a - c - 0) (0 + 0))).real Set.univ = c - a
  rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem boundaryPositiveInputInterval_volume_real_eq_sub
    (a c : ℝ) (hac : a ≤ c) :
    (volume : Measure (BoundaryPositiveInputInterval a c)).real Set.univ =
      c - a := by
  change (volume : Measure (Set.Icc (0 - 0) (c - a + 0))).real Set.univ = c - a
  rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem boundaryFullInputInterval_volume_real_eq_two_mul_sub
    (a c : ℝ) (hac : a ≤ c) :
    (volume : Measure (BoundaryFullInputInterval a c)).real Set.univ =
      2 * (c - a) := by
  change (volume : Measure (Set.Icc (a - c - 0) (c - a + 0))).real Set.univ =
    2 * (c - a)
  rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem negativeBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (negativeBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
        ((volume : Measure (BoundaryNegativeInputInterval a c)).real Set.univ *
          SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) := by
  apply continuousKernel_basisEnergy_le_measure_mul_sq
  · positivity
  · intro y x
    change ‖g.test (x.1 - y.1)‖ ≤ SchwartzMap.seminorm ℂ 0 0 g.test
    exact SchwartzMap.norm_le_seminorm ℂ g.test (x.1 - y.1)

theorem positiveBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (positiveBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
        ((volume : Measure (BoundaryPositiveInputInterval a c)).real Set.univ *
          SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) := by
  apply continuousKernel_basisEnergy_le_measure_mul_sq
  · positivity
  · intro y x
    change ‖g.test (x.1 - y.1)‖ ≤ SchwartzMap.seminorm ℂ 0 0 g.test
    exact SchwartzMap.norm_le_seminorm ℂ g.test (x.1 - y.1)

theorem fullBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryFullInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (fullBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
        ((volume : Measure (BoundaryFullInputInterval a c)).real Set.univ *
          SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) := by
  apply continuousKernel_basisEnergy_le_measure_mul_sq
  · positivity
  · intro y x
    change ‖g.test (x.1 - y.1)‖ ≤ SchwartzMap.seminorm ℂ 0 0 g.test
    exact SchwartzMap.norm_le_seminorm ℂ g.test (x.1 - y.1)

theorem negativeBoundaryRootKernel_basisEnergy_le_supportPolynomial
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryNegativeInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (negativeBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
  calc
    _ ≤ (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
          ((volume : Measure (BoundaryNegativeInputInterval a c)).real Set.univ *
            SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) :=
      negativeBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm
        g a c basis
    _ = (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
      rw [boundaryOutputInterval_volume_real_eq_sub a c hac,
        boundaryNegativeInputInterval_volume_real_eq_sub a c hac]
      ring

theorem positiveBoundaryRootKernel_basisEnergy_le_supportPolynomial
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryPositiveInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (positiveBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
  calc
    _ ≤ (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
          ((volume : Measure (BoundaryPositiveInputInterval a c)).real Set.univ *
            SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) :=
      positiveBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm
        g a c basis
    _ = (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
      rw [boundaryOutputInterval_volume_real_eq_sub a c hac,
        boundaryPositiveInputInterval_volume_real_eq_sub a c hac]
      ring

theorem fullBoundaryRootKernel_basisEnergy_le_supportPolynomial
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ) (hac : a ≤ c)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)))) :
    (∑' i, ‖CC20Concrete.ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (BoundaryFullInputInterval a c))
        (volume : Measure (BoundaryOutputInterval a c))
        (fullBoundaryRootKernel g a c) (basis i)‖ ^ 2) ≤
      2 * (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
  calc
    _ ≤ (volume : Measure (BoundaryOutputInterval a c)).real Set.univ *
          ((volume : Measure (BoundaryFullInputInterval a c)).real Set.univ *
            SchwartzMap.seminorm ℂ 0 0 g.test ^ 2) :=
      fullBoundaryRootKernel_basisEnergy_le_measure_mul_seminorm g a c basis
    _ = 2 * (c - a) ^ 2 * SchwartzMap.seminorm ℂ 0 0 g.test ^ 2 := by
      rw [boundaryOutputInterval_volume_real_eq_sub a c hac,
        boundaryFullInputInterval_volume_real_eq_two_mul_sub a c hac]
      ring

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable abbrev sourceRootCompletedPairCarrier :=
  WithLp 2 (finiteSCarrier × WithLp 2 (finiteSCarrier × finiteSCarrier))

/-- The left root of the support-compressed positive detector. -/
noncomputable def sourceCompressedDetectorLeftRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  radialSupportProjection lambda ∘L (rootConvolution owner).adjoint

/-- The right root of the support-compressed positive detector. -/
noncomputable def sourceCompressedDetectorRightRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  rootConvolution owner ∘L radialSupportProjection lambda

/-- The actual compressed detector is the ordered product of the two named
roots. -/
theorem compressedDetector_eq_sourceCompressedDetectorRoots
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    compressedDetector (radialSupportProjection lambda)
        (detectorOperator owner) =
      sourceCompressedDetectorLeftRoot owner lambda ∘L
        sourceCompressedDetectorRightRoot owner lambda := by
  unfold compressedDetector detectorOperator
    sourceCompressedDetectorLeftRoot sourceCompressedDetectorRightRoot
    rootConvolution CC20Concrete.cc20GlobalConvolutionPositive
  simp only [ContinuousLinearMap.mul_def]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The selected positive detector is the square of the named convolution
root on the literal common-log carrier. -/
theorem detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    detectorOperator owner =
      (rootConvolution owner).adjoint ∘L rootConvolution owner := by
  unfold detectorOperator rootConvolution
    CC20Concrete.cc20GlobalConvolutionPositive
  rfl

theorem sourceCompressedDetectorLeftRoot_adjoint_eq_rightRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceCompressedDetectorLeftRoot owner lambda).adjoint =
      sourceCompressedDetectorRightRoot owner lambda := by
  unfold sourceCompressedDetectorLeftRoot sourceCompressedDetectorRightRoot
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (radialSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]

/-!
Each algebraic branch is now represented by an actual pair of
Hilbert--Schmidt legs.  Five maps occur in the expanded ledger, but only two
root-leg obligations are independent: the left-commutator leg is a projection
of the right-commutator left leg, and the right-commutator right leg is a
projection of the common right leg.  The range leg comes from the existing
prolate-factor witness.  Every leg contains one selected convolution root, so
all resulting energy bounds have the correct quadratic scaling.
-/

noncomputable def sourceRootCompletedRangeLeftLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  (sourceBandProjection lambda ∘L
    sourceFourierSupportProjection lambda ∘L
    sourceCompressedDetectorLeftRoot owner lambda).adjoint

theorem sourceRootCompletedRangeLeftLeg_eq_root_comp_prolateFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRangeLeftLeg owner lambda =
      sourceCompressedDetectorRightRoot owner lambda ∘L
        sourceProlateHilbertSchmidtFactor lambda := by
  unfold sourceRootCompletedRangeLeftLeg
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    sourceCompressedDetectorLeftRoot_adjoint_eq_rightRoot,
    (sourceFourierSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq,
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
  rfl

theorem sourceRootCompletedRangeLeftLeg_summable_of_prolateFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedRangeLeftLeg_eq_root_comp_prolateFactor]
  exact CC20Concrete.PositiveTrace.summable_normSq_postcomp basis
    (sourceProlateHilbertSchmidtFactor lambda)
    (sourceCompressedDetectorRightRoot owner lambda) hfactor

theorem sourceRootCompletedRangeLeftLeg_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2) :
    (∑' i, ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2) ≤
      ‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedRangeLeftLeg_eq_root_comp_prolateFactor]
  have hcomposed := CC20Concrete.PositiveTrace.summable_normSq_postcomp basis
    (sourceProlateHilbertSchmidtFactor lambda)
    (sourceCompressedDetectorRightRoot owner lambda) hfactor
  have hmajorant := hfactor.mul_left
    (‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2)
  calc
    (∑' i,
        ‖(sourceCompressedDetectorRightRoot owner lambda ∘L
          sourceProlateHilbertSchmidtFactor lambda) (basis i)‖ ^ 2) ≤
        ∑' i,
          ‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
            ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
      apply hcomposed.tsum_le_tsum _ hmajorant
      intro i
      rw [ContinuousLinearMap.comp_apply]
      calc
        _ ≤ (‖sourceCompressedDetectorRightRoot owner lambda‖ *
              ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖) ^ 2 := by
          gcongr
          exact (sourceCompressedDetectorRightRoot owner lambda).le_opNorm _
        _ = _ := by ring
    _ = ‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
      rw [tsum_mul_left]

noncomputable def sourceRootCompletedCommonRightLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) : Op :=
  sourceCompressedDetectorRightRoot owner lambda ∘L
    sourceSoninProjection lambda ∘L transport ∘L
    sourceBandProjection lambda

noncomputable def sourceRootCompletedRightCommutatorLeftLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  (sourceBandProjection lambda ∘L
    (1 - sourceFourierSupportProjection lambda) ∘L
    sourceCompressedDetectorLeftRoot owner lambda).adjoint

noncomputable def sourceRootCompletedRightCommutatorRightLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) : Op :=
  CCM24FiniteSTwoSidedRootRecombination.commutator
      (sourceCompressedDetectorRightRoot owner lambda)
      (sourceFourierSupportProjection lambda) ∘L
    sourceSoninProjection lambda ∘L transport ∘L
    sourceBandProjection lambda

noncomputable def sourceRootCompletedLeftCommutatorLeftLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  (sourceBandProjection lambda ∘L
    (1 - sourceFourierSupportProjection lambda) ∘L
    CCM24FiniteSTwoSidedRootRecombination.commutator
      (sourceCompressedDetectorLeftRoot owner lambda)
      (sourceFourierSupportProjection lambda)).adjoint

/-! The two independent root legs have exact source-geometric normal forms.
These identities do not assert a Schatten estimate. -/

/-- The radial support projection absorbs the source quotient band. -/
theorem radialSupportProjection_comp_sourceBandProjection_eq_self
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L sourceBandProjection lambda =
      sourceBandProjection lambda := by
  have hE : IsIdempotentElem (radialSupportProjection lambda) :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hEP : radialSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  unfold sourceBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    radialSupportProjection lambda *
          (radialSupportProjection lambda - sourceSoninProjection lambda) =
        radialSupportProjection lambda - sourceSoninProjection lambda by
      rw [mul_sub, hE, hEP]

/-- The quotient band is also absorbed when the radial support projection is
on the right. -/
theorem sourceBandProjection_comp_radialSupportProjection_eq_self
    (lambda : CCM24SoninScale) :
    sourceBandProjection lambda ∘L radialSupportProjection lambda =
      sourceBandProjection lambda := by
  have hE : IsIdempotentElem (radialSupportProjection lambda) :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hPE : sourceSoninProjection lambda *
      radialSupportProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_radialSupportProjection lambda
  unfold sourceBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (radialSupportProjection lambda - sourceSoninProjection lambda) *
          radialSupportProjection lambda =
        radialSupportProjection lambda - sourceSoninProjection lambda by
      rw [sub_mul, hE, hPE]

/-- The source Sonin projection annihilates its orthogonal quotient band. -/
theorem sourceSoninProjection_comp_sourceBandProjection_eq_zero
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L sourceBandProjection lambda = 0 := by
  have hP : IsIdempotentElem (sourceSoninProjection lambda) :=
    (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hPE : sourceSoninProjection lambda *
      radialSupportProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_radialSupportProjection lambda
  unfold sourceBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceSoninProjection lambda *
          (radialSupportProjection lambda - sourceSoninProjection lambda) =
        0 by
      rw [mul_sub, hPE, hP, sub_self]

/-- The quotient band also annihilates the source Sonin projection in the
opposite order. -/
theorem sourceBandProjection_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) :
    sourceBandProjection lambda ∘L sourceSoninProjection lambda = 0 := by
  have hP : IsIdempotentElem (sourceSoninProjection lambda) :=
    (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hEP : radialSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  unfold sourceBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (radialSupportProjection lambda - sourceSoninProjection lambda) *
        sourceSoninProjection lambda = 0 by
      rw [sub_mul, hEP, hP, sub_self]

/-- The Fourier-support complement cannot see the Sonin part of the radial
band, so its quotient-band input is exactly its radial-support input. -/
theorem sourceFourierComplement_comp_sourceBandProjection_eq_radial
    (lambda : CCM24SoninScale) :
    (1 - sourceFourierSupportProjection lambda) ∘L
        sourceBandProjection lambda =
      (1 - sourceFourierSupportProjection lambda) ∘L
        radialSupportProjection lambda := by
  have hQP : sourceFourierSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  have hzero : (1 - sourceFourierSupportProjection lambda) *
      sourceSoninProjection lambda = 0 := by
    calc
      (1 - sourceFourierSupportProjection lambda) *
          sourceSoninProjection lambda =
        sourceSoninProjection lambda -
          sourceFourierSupportProjection lambda *
            sourceSoninProjection lambda := by noncomm_ring
      _ = 0 := by rw [hQP]; exact sub_self _
  unfold sourceBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (1 - sourceFourierSupportProjection lambda) *
          (radialSupportProjection lambda - sourceSoninProjection lambda) =
        (1 - sourceFourierSupportProjection lambda) *
          radialSupportProjection lambda by
      rw [mul_sub, hzero, sub_zero]

/-- The genuinely independent left energy is the single-root leakage
`C_g E (I-Q) E`.  In particular, it is not supplied by trace legality of the
detector-level second-support product. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_eq_root_fourierLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      rootConvolution owner ∘L radialSupportProjection lambda ∘L
        (1 - sourceFourierSupportProjection lambda) ∘L
          radialSupportProjection lambda := by
  unfold sourceRootCompletedRightCommutatorLeftLeg
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    sourceCompressedDetectorLeftRoot_adjoint_eq_rightRoot,
    (sourceFourierSupportProjection_isStarProjection lambda).one_sub
      |>.isSelfAdjoint.adjoint_eq,
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (sourceFourierComplement_comp_sourceBandProjection_eq_radial lambda) u
  simp only [ContinuousLinearMap.comp_apply] at h ⊢
  unfold sourceCompressedDetectorRightRoot
  rw [h]
  rfl

/-- The compressed Fourier-complement corner is the quotient band minus the
source prolate remainder. -/
theorem radial_fourierComplement_radial_eq_band_sub_prolate
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L
        (1 - sourceFourierSupportProjection lambda) ∘L
        radialSupportProjection lambda =
      sourceBandProjection lambda - sourceProlateRemainder lambda := by
  have hE : IsIdempotentElem (radialSupportProjection lambda) :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  unfold sourceBandProjection sourceProlateRemainder
  simpa only [ContinuousLinearMap.mul_def] using show
    radialSupportProjection lambda *
          (1 - sourceFourierSupportProjection lambda) *
          radialSupportProjection lambda =
        (radialSupportProjection lambda - sourceSoninProjection lambda) -
          (radialSupportProjection lambda *
              sourceFourierSupportProjection lambda *
              radialSupportProjection lambda -
            sourceSoninProjection lambda) by
      calc
        radialSupportProjection lambda *
              (1 - sourceFourierSupportProjection lambda) *
              radialSupportProjection lambda =
            radialSupportProjection lambda * radialSupportProjection lambda -
              radialSupportProjection lambda *
                sourceFourierSupportProjection lambda *
                radialSupportProjection lambda := by noncomm_ring
        _ = radialSupportProjection lambda -
              radialSupportProjection lambda *
                sourceFourierSupportProjection lambda *
                radialSupportProjection lambda := by rw [hE]
        _ = _ := by noncomm_ring

/-- Equivalently, the independent left leg is `C_g (B-K_prol)`.  The existing
Hilbert--Schmidt witness controls `K_prol`; it does not by itself control the
full `B-K_prol` input. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_eq_root_band_sub_prolate
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      rootConvolution owner ∘L
        (sourceBandProjection lambda - sourceProlateRemainder lambda) := by
  rw [sourceRootCompletedRightCommutatorLeftLeg_eq_root_fourierLeakage]
  have hcorner := radial_fourierComplement_radial_eq_band_sub_prolate lambda
  apply ContinuousLinearMap.ext
  intro u
  have hu := DFunLike.congr_fun hcorner u
  simp only [ContinuousLinearMap.comp_apply] at hu ⊢
  rw [hu]

/-- The common right leg is exactly the selected root applied to the
source-Sonin/quotient-band crossing of the supplied transport. -/
theorem sourceRootCompletedCommonRightLeg_eq_root_sonin_transport_band
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) :
    sourceRootCompletedCommonRightLeg owner lambda transport =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        transport ∘L sourceBandProjection lambda := by
  unfold sourceRootCompletedCommonRightLeg
    sourceCompressedDetectorRightRoot
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (radialSupportProjection_comp_sourceSoninProjection lambda)
    (transport (sourceBandProjection lambda u))
  simp only [ContinuousLinearMap.comp_apply] at h ⊢
  rw [h]

/-- At the identity radial transport the common right leg vanishes.  Thus the
finite-Euler obligation is created entirely by the causal Sonin-to-band
crossing, not by a fixed background term. -/
theorem sourceRootCompletedCommonRightLeg_radialSupport_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedCommonRightLeg owner lambda
        (radialSupportProjection lambda) = 0 := by
  rw [sourceRootCompletedCommonRightLeg_eq_root_sonin_transport_band]
  have hzero := sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  apply ContinuousLinearMap.ext
  intro u
  have hE := DFunLike.congr_fun
    (radialSupportProjection_comp_sourceBandProjection_eq_self lambda) u
  have hP := DFunLike.congr_fun hzero u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hE hP ⊢
  rw [hE, hP, map_zero]

/-- For the normalized finite Euler inverse, the common leg has no redundant
support projections: it is the literal causal crossing `C_g P A_S B`. -/
theorem sourceRootCompletedFiniteEulerCommonRightLeg_eq_causalCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedCommonRightLeg owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L
          sourceBandProjection lambda := by
  rw [sourceRootCompletedCommonRightLeg_eq_root_sonin_transport_band]
  have hPE := sourceSoninProjection_comp_radialSupportProjection lambda
  have hEB := radialSupportProjection_comp_sourceBandProjection_eq_self lambda
  apply ContinuousLinearMap.ext
  intro u
  have hPEu := DFunLike.congr_fun hPE
    (normalizedFiniteEulerInverse family
      (radialSupportProjection lambda (sourceBandProjection lambda u)))
  have hEBu := DFunLike.congr_fun hEB u
  simp only [ContinuousLinearMap.comp_apply] at hPEu hEBu ⊢
  rw [hEBu] at hPEu ⊢
  rw [hPEu]

/-- The causal common leg is centered at the identity inverse.  The constant
mass of the Markov probability law cancels because the source Sonin projection
annihilates the quotient band. -/
theorem sourceRootCompletedFiniteEulerCommonRightLeg_eq_centeredCausalCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedCommonRightLeg owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        (normalizedFiniteEulerInverse family -
          ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        sourceBandProjection lambda := by
  rw [sourceRootCompletedFiniteEulerCommonRightLeg_eq_causalCrossing]
  have hPB := sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  apply ContinuousLinearMap.ext
  intro u
  have hPBu := DFunLike.congr_fun hPB u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, ContinuousLinearMap.zero_apply] at hPBu ⊢
  rw [hPBu, map_zero, sub_zero]

/-!
The apparent three left legs must now be recombined.  The prolate range leg is
`C_g K_prol`, while the Fourier-leakage leg is `C_g (B-K_prol)`.  Their sum is
the full root-band leg `C_g B`.  This is the signed normal form used below;
separate square-energy estimates for the two summands are not required by the
operator identity.
-/

/-- Radial compression of the named prolate factor is the actual prolate
remainder. -/
theorem radialSupportProjection_comp_sourceProlateFactor_eq_remainder
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L
        sourceProlateHilbertSchmidtFactor lambda =
      sourceProlateRemainder lambda := by
  have hPQ : sourceSoninProjection lambda *
      sourceFourierSupportProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace,
      ContinuousLinearMap.mul_def] using
      (_root_.ConnesWeilRH.CC20Concrete.intersection_absorbs_right_starProjection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  have hPB : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  have hdecomp : radialSupportProjection lambda =
      sourceBandProjection lambda + sourceSoninProjection lambda := by
    unfold sourceBandProjection
    abel
  rw [sourceProlateRemainder_eq_factor]
  unfold sourceProlateHilbertSchmidtFactor
  simpa only [ContinuousLinearMap.mul_def] using show
    radialSupportProjection lambda * sourceFourierSupportProjection lambda *
          sourceBandProjection lambda =
        sourceBandProjection lambda * sourceFourierSupportProjection lambda *
          sourceBandProjection lambda by
      calc
        radialSupportProjection lambda *
              sourceFourierSupportProjection lambda *
              sourceBandProjection lambda =
            (sourceBandProjection lambda + sourceSoninProjection lambda) *
              sourceFourierSupportProjection lambda *
              sourceBandProjection lambda := by
          rw [hdecomp]
        _ = sourceBandProjection lambda *
              sourceFourierSupportProjection lambda *
              sourceBandProjection lambda +
            sourceSoninProjection lambda *
              sourceFourierSupportProjection lambda *
              sourceBandProjection lambda := by
          noncomm_ring
        _ = sourceBandProjection lambda *
              sourceFourierSupportProjection lambda *
              sourceBandProjection lambda := by
          rw [hPQ, hPB, add_zero]

/-- The already-controlled range leg is exactly the selected root applied to
the actual prolate remainder. -/
theorem sourceRootCompletedRangeLeftLeg_eq_root_prolateRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRangeLeftLeg owner lambda =
      rootConvolution owner ∘L sourceProlateRemainder lambda := by
  rw [sourceRootCompletedRangeLeftLeg_eq_root_comp_prolateFactor]
  apply ContinuousLinearMap.ext
  intro u
  change rootConvolution owner
      (radialSupportProjection lambda
        (sourceProlateHilbertSchmidtFactor lambda u)) =
    rootConvolution owner (sourceProlateRemainder lambda u)
  exact congrArg (rootConvolution owner) (DFunLike.congr_fun
    (radialSupportProjection_comp_sourceProlateFactor_eq_remainder lambda) u)

/-- The prolate and Fourier-leakage left legs recombine to the full selected
root on the quotient band. -/
theorem sourceRootCompletedLeftLegs_add_eq_root_band
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedRangeLeftLeg owner lambda +
        sourceRootCompletedRightCommutatorLeftLeg owner lambda =
      rootConvolution owner ∘L sourceBandProjection lambda := by
  rw [sourceRootCompletedRangeLeftLeg_eq_root_prolateRemainder,
    sourceRootCompletedRightCommutatorLeftLeg_eq_root_band_sub_prolate]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- The left-root commutator leg is only the second-support projection of the
right-commutator left leg.  It therefore carries no independent
Hilbert--Schmidt obligation. -/
theorem sourceRootCompletedLeftCommutatorLeftLeg_eq_projection_comp
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceRootCompletedLeftCommutatorLeftLeg owner lambda =
      sourceFourierSupportProjection lambda ∘L
        sourceRootCompletedRightCommutatorLeftLeg owner lambda := by
  let B := sourceBandProjection lambda
  let Q := sourceFourierSupportProjection lambda
  let L := sourceCompressedDetectorLeftRoot owner lambda
  have hQ : IsIdempotentElem Q :=
    (sourceFourierSupportProjection_isStarProjection lambda).isIdempotentElem
  have hsplit :
      B ∘L (1 - Q) ∘L
          CCM24FiniteSTwoSidedRootRecombination.commutator L Q =
        B ∘L (1 - Q) ∘L L ∘L Q := by
    simpa only [ContinuousLinearMap.mul_def] using
      band_complement_mul_commutator_eq B L Q hQ
  have hadjoint :
      (sourceRootCompletedLeftCommutatorLeftLeg owner lambda).adjoint =
        (sourceFourierSupportProjection lambda ∘L
          sourceRootCompletedRightCommutatorLeftLeg owner lambda).adjoint := by
    unfold sourceRootCompletedLeftCommutatorLeftLeg
      sourceRootCompletedRightCommutatorLeftLeg
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      (sourceFourierSupportProjection_isStarProjection lambda)
        |>.isSelfAdjoint.adjoint_eq]
    exact hsplit
  calc
    sourceRootCompletedLeftCommutatorLeftLeg owner lambda =
        (sourceRootCompletedLeftCommutatorLeftLeg owner lambda).adjoint.adjoint :=
      (ContinuousLinearMap.adjoint_adjoint _).symm
    _ = (sourceFourierSupportProjection lambda ∘L
          sourceRootCompletedRightCommutatorLeftLeg owner lambda).adjoint.adjoint :=
      congrArg ContinuousLinearMap.adjoint hadjoint
    _ = sourceFourierSupportProjection lambda ∘L
          sourceRootCompletedRightCommutatorLeftLeg owner lambda :=
      ContinuousLinearMap.adjoint_adjoint _

/-- The right-root commutator leg is the complementary second-support
projection of the common right leg. -/
theorem sourceRootCompletedRightCommutatorRightLeg_eq_complement_comp
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) :
    sourceRootCompletedRightCommutatorRightLeg owner lambda transport =
      (1 - sourceFourierSupportProjection lambda) ∘L
        sourceRootCompletedCommonRightLeg owner lambda transport := by
  have hSecondInner : sourceFourierSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  unfold sourceRootCompletedRightCommutatorRightLeg
    sourceRootCompletedCommonRightLeg
  simpa only [ContinuousLinearMap.mul_def] using
    commutator_mul_absorbed_eq_complement_mul
      (sourceCompressedDetectorRightRoot owner lambda)
      (sourceFourierSupportProjection lambda)
      (sourceSoninProjection lambda)
      (transport ∘L sourceBandProjection lambda) hSecondInner

theorem sourceRootCompletedLeftCommutatorLeftLeg_summable_of_right
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier)
    (hright : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedLeftCommutatorLeftLeg_eq_projection_comp]
  exact CC20Concrete.PositiveTrace.summable_normSq_postcomp basis
    (sourceRootCompletedRightCommutatorLeftLeg owner lambda)
    (sourceFourierSupportProjection lambda) hright

theorem sourceRootCompletedRightCommutatorRightLeg_summable_of_common
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hcommon : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedRightCommutatorRightLeg_eq_complement_comp]
  exact CC20Concrete.PositiveTrace.summable_normSq_postcomp basis
    (sourceRootCompletedCommonRightLeg owner lambda transport)
    (1 - sourceFourierSupportProjection lambda) hcommon

theorem sourceRootCompletedLeftCommutatorLeftLeg_basisEnergy_le_right
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier)
    (hright : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    (∑' i, ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) ≤
      ∑' i, ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedLeftCommutatorLeftLeg_eq_projection_comp]
  apply basisEnergy_postcomp_le_of_norm_le_one basis _ _ hright
  exact IsStarProjection.norm_le _
    (sourceFourierSupportProjection_isStarProjection lambda)

theorem sourceRootCompletedRightCommutatorRightLeg_basisEnergy_le_common
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hcommon : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    (∑' i, ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2) ≤
      ∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2 := by
  rw [sourceRootCompletedRightCommutatorRightLeg_eq_complement_comp]
  apply basisEnergy_postcomp_le_of_norm_le_one basis _ _ hcommon
  exact IsStarProjection.norm_le _
    (sourceFourierSupportProjection_isStarProjection lambda).one_sub

noncomputable def sourceRootCompletedRangePairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) basis where
  left := sourceRootCompletedRangeLeftLeg owner lambda
  right := sourceRootCompletedCommonRightLeg owner lambda transport
  left_summable_normSq := hleft
  right_summable_normSq := hright

noncomputable def sourceRootCompletedRightCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) basis where
  left := sourceRootCompletedRightCommutatorLeftLeg owner lambda
  right := sourceRootCompletedRightCommutatorRightLeg owner lambda transport
  left_summable_normSq := hleft
  right_summable_normSq := hright

noncomputable def sourceRootCompletedLeftCommutatorPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) basis where
  left := sourceRootCompletedLeftCommutatorLeftLeg owner lambda
  right := sourceRootCompletedCommonRightLeg owner lambda transport
  left_summable_normSq := hleft
  right_summable_normSq := hright

theorem sourceRootCompletedRangePairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    (sourceRootCompletedRangePairData owner lambda basis transport hleft
      hright).traceProduct =
      sourceBandProjection lambda ∘L
        sourceFourierSupportProjection lambda ∘L
        sourceCompressedDetectorLeftRoot owner lambda ∘L
        sourceCompressedDetectorRightRoot owner lambda ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct,
    sourceRootCompletedRangePairData, sourceRootCompletedRangeLeftLeg,
    sourceRootCompletedCommonRightLeg, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_adjoint]

theorem sourceRootCompletedRightCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    (sourceRootCompletedRightCommutatorPairData owner lambda basis transport
      hleft hright).traceProduct =
      sourceBandProjection lambda ∘L
        (1 - sourceFourierSupportProjection lambda) ∘L
        sourceCompressedDetectorLeftRoot owner lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (sourceCompressedDetectorRightRoot owner lambda)
          (sourceFourierSupportProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct,
    sourceRootCompletedRightCommutatorPairData,
    sourceRootCompletedRightCommutatorLeftLeg,
    sourceRootCompletedRightCommutatorRightLeg,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_adjoint]

theorem sourceRootCompletedLeftCommutatorPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hleft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hright : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    (sourceRootCompletedLeftCommutatorPairData owner lambda basis transport
      hleft hright).traceProduct =
      sourceBandProjection lambda ∘L
        (1 - sourceFourierSupportProjection lambda) ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (sourceCompressedDetectorLeftRoot owner lambda)
          (sourceFourierSupportProjection lambda) ∘L
        sourceCompressedDetectorRightRoot owner lambda ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct,
    sourceRootCompletedLeftCommutatorPairData,
    sourceRootCompletedLeftCommutatorLeftLeg,
    sourceRootCompletedCommonRightLeg, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_adjoint]

/-- One orthogonal pair owner for all three root-completed branches. -/
noncomputable def sourceRootCompletedPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := sourceRootCompletedPairCarrier) basis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (sourceRootCompletedRangePairData owner lambda basis transport
      hRangeLeft hCommonRight)
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
      (sourceRootCompletedRightCommutatorPairData owner lambda basis transport
        hRightCommutatorLeft hRightCommutatorRight)
      (sourceRootCompletedLeftCommutatorPairData owner lambda basis transport
        hLeftCommutatorLeft hCommonRight))

/-- The genuine source first-jet corner with both convolution roots exposed
before any square-energy estimate. -/
noncomputable def sourceRootCompletedFixedQuotientCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) : Op :=
  rootCompletedSecondSupportCorner
    (sourceBandProjection lambda)
    (sourceSoninProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceCompressedDetectorLeftRoot owner lambda)
    (sourceCompressedDetectorRightRoot owner lambda)
    transport

/-- The full three-branch owner is one signed two-leg root pairing.  The
orthogonal three-coordinate carrier remains a fixed-`S` trace-legality
witness, not the family-uniform estimator. -/
theorem sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) :
    sourceRootCompletedFixedQuotientCorner owner lambda transport =
      (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
        sourceRootCompletedCommonRightLeg owner lambda transport := by
  have hInner : IsIdempotentElem (sourceSoninProjection lambda) :=
    (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hBandInner : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    have hSupportInner : radialSupportProjection lambda *
        sourceSoninProjection lambda = sourceSoninProjection lambda := by
      simpa only [ContinuousLinearMap.mul_def] using
        radialSupportProjection_comp_sourceSoninProjection lambda
    change (radialSupportProjection lambda - sourceSoninProjection lambda) *
      sourceSoninProjection lambda = 0
    rw [sub_mul, hSupportInner, hInner, sub_self]
  have hSecond : IsIdempotentElem
      (sourceFourierSupportProjection lambda) :=
    (sourceFourierSupportProjection_isStarProjection lambda).isIdempotentElem
  have hSecondInner : sourceFourierSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  unfold sourceRootCompletedFixedQuotientCorner
  rw [rootCompletedSecondSupportCorner_eq_unsplit
    (sourceBandProjection lambda) (sourceSoninProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceCompressedDetectorLeftRoot owner lambda)
    (sourceCompressedDetectorRightRoot owner lambda) transport hInner
    hBandInner hSecond hSecondInner]
  unfold sourceRootCompletedCommonRightLeg
    sourceCompressedDetectorLeftRoot sourceCompressedDetectorRightRoot
  rw [ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
  have hBE : sourceBandProjection lambda *
      radialSupportProjection lambda = sourceBandProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_radialSupportProjection_eq_self lambda
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceBandProjection lambda * radialSupportProjection lambda *
          (rootConvolution owner).adjoint * rootConvolution owner *
          radialSupportProjection lambda * sourceSoninProjection lambda *
          transport * sourceBandProjection lambda =
        sourceBandProjection lambda * (rootConvolution owner).adjoint *
          rootConvolution owner * radialSupportProjection lambda *
          sourceSoninProjection lambda * transport *
          sourceBandProjection lambda by
      rw [hBE]

/-- For the actual normalized Euler inverse, the unsplit owner is centered at
the identity before any renewal atom or norm is exposed. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_centeredUnsplitRootPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
        rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        (normalizedFiniteEulerInverse family -
          ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        sourceBandProjection lambda := by
  rw [sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair,
    sourceRootCompletedFiniteEulerCommonRightLeg_eq_centeredCausalCrossing]

theorem sourceRootCompletedPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    (sourceRootCompletedPairData owner lambda basis transport hRangeLeft
      hCommonRight hRightCommutatorLeft hRightCommutatorRight
      hLeftCommutatorLeft).traceProduct =
      sourceRootCompletedFixedQuotientCorner owner lambda transport := by
  rw [sourceRootCompletedPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    sourceRootCompletedRangePairData_traceProduct_eq owner lambda basis
      transport hRangeLeft hCommonRight,
    sourceRootCompletedRightCommutatorPairData_traceProduct_eq owner lambda
      basis transport hRightCommutatorLeft hRightCommutatorRight,
    sourceRootCompletedLeftCommutatorPairData_traceProduct_eq owner lambda
      basis transport hLeftCommutatorLeft hCommonRight]
  unfold sourceRootCompletedFixedQuotientCorner
    rootCompletedSecondSupportCorner
  simp only [ContinuousLinearMap.mul_def]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  abel

theorem sourceRootCompletedPairData_left_basisEnergy_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    (∑' i, ‖(sourceRootCompletedPairData owner lambda basis transport
        hRangeLeft hCommonRight hRightCommutatorLeft hRightCommutatorRight
        hLeftCommutatorLeft).left (basis i)‖ ^ 2) =
      (∑' i, ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2) +
        ((∑' i, ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
          (basis i)‖ ^ 2) +
        ∑' i, ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
          (basis i)‖ ^ 2) := by
  rw [sourceRootCompletedPairData, l2Sum_left_basisEnergy_eq_add,
    l2Sum_left_basisEnergy_eq_add]
  rfl

theorem sourceRootCompletedPairData_right_basisEnergy_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    (∑' i, ‖(sourceRootCompletedPairData owner lambda basis transport
        hRangeLeft hCommonRight hRightCommutatorLeft hRightCommutatorRight
        hLeftCommutatorLeft).right (basis i)‖ ^ 2) =
      (∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) +
        ((∑' i, ‖sourceRootCompletedRightCommutatorRightLeg owner lambda
          transport (basis i)‖ ^ 2) +
        ∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
          (basis i)‖ ^ 2) := by
  rw [sourceRootCompletedPairData, l2Sum_right_basisEnergy_eq_add,
    l2Sum_right_basisEnergy_eq_add]
  rfl

/-- The root-completed first jet is controlled by the geometric mean of its
two completed Hilbert--Schmidt column energies. -/
theorem sourceRootCompleted_ordinaryTrace_norm_le_geometricEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceRootCompletedFixedQuotientCorner owner lambda transport)‖ ≤
      Real.sqrt (∑' i,
        ‖(sourceRootCompletedPairData owner lambda basis transport hRangeLeft
          hCommonRight hRightCommutatorLeft hRightCommutatorRight
          hLeftCommutatorLeft).left (basis i)‖ ^ 2) *
      Real.sqrt (∑' i,
        ‖(sourceRootCompletedPairData owner lambda basis transport hRangeLeft
          hCommonRight hRightCommutatorLeft hRightCommutatorRight
          hLeftCommutatorLeft).right (basis i)‖ ^ 2) := by
  rw [← sourceRootCompletedPairData_traceProduct_eq owner lambda basis
    transport hRangeLeft hCommonRight hRightCommutatorLeft
    hRightCommutatorRight hLeftCommutatorLeft]
  exact ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy _

/-- The five expanded energies are visible in the conclusion; the reduced
consumer below proves that only two of them are independent.  No
nonhomogeneous prolate energy is hidden inside the pair carrier. -/
theorem sourceRootCompleted_ordinaryTrace_norm_le_explicitGeometricEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hRangeLeft : Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hRightCommutatorRight : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
        (basis i)‖ ^ 2)
    (hLeftCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceRootCompletedFixedQuotientCorner owner lambda transport)‖ ≤
      Real.sqrt
        ((∑' i, ‖sourceRootCompletedRangeLeftLeg owner lambda
          (basis i)‖ ^ 2) +
        ((∑' i, ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
          (basis i)‖ ^ 2) +
        ∑' i, ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
          (basis i)‖ ^ 2)) *
      Real.sqrt
        ((∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
          (basis i)‖ ^ 2) +
        ((∑' i, ‖sourceRootCompletedRightCommutatorRightLeg owner lambda
          transport (basis i)‖ ^ 2) +
        ∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
          (basis i)‖ ^ 2)) := by
  have hbound := sourceRootCompleted_ordinaryTrace_norm_le_geometricEnergy
    owner lambda basis transport hRangeLeft hCommonRight
    hRightCommutatorLeft hRightCommutatorRight hLeftCommutatorLeft
  rw [sourceRootCompletedPairData_left_basisEnergy_eq owner lambda basis
      transport hRangeLeft hCommonRight hRightCommutatorLeft
      hRightCommutatorRight hLeftCommutatorLeft,
    sourceRootCompletedPairData_right_basisEnergy_eq owner lambda basis
      transport hRangeLeft hCommonRight hRightCommutatorLeft
      hRightCommutatorRight hLeftCommutatorLeft] at hbound
  exact hbound

/-- The root-completed first jet needs only the prolate-factor witness and
two genuinely independent root legs.  The other two commutator legs are
orthogonal projections of these inputs and introduce no extra analytic
premise. -/
theorem sourceRootCompleted_ordinaryTrace_norm_le_reducedGeometricEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (transport : Op)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2)
    (hRightCommutatorLeft : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2)
    (hCommonRight : Summable fun i =>
      ‖sourceRootCompletedCommonRightLeg owner lambda transport
        (basis i)‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong basis
        (sourceRootCompletedFixedQuotientCorner owner lambda transport)‖ ≤
      Real.sqrt
        (‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (basis i)‖ ^ 2) +
        2 * (∑' i,
          ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
            (basis i)‖ ^ 2)) *
      Real.sqrt
        (3 * (∑' i,
          ‖sourceRootCompletedCommonRightLeg owner lambda transport
            (basis i)‖ ^ 2)) := by
  have hRangeLeft :=
    sourceRootCompletedRangeLeftLeg_summable_of_prolateFactor owner lambda
      basis hfactor
  have hRightCommutatorRight :=
    sourceRootCompletedRightCommutatorRightLeg_summable_of_common owner
      lambda basis transport hCommonRight
  have hLeftCommutatorLeft :=
    sourceRootCompletedLeftCommutatorLeftLeg_summable_of_right owner lambda
      basis hRightCommutatorLeft
  have hbound :=
    sourceRootCompleted_ordinaryTrace_norm_le_explicitGeometricEnergy owner
      lambda basis transport hRangeLeft hCommonRight hRightCommutatorLeft
      hRightCommutatorRight hLeftCommutatorLeft
  have hRangeEnergy := sourceRootCompletedRangeLeftLeg_basisEnergy_le owner
    lambda basis hfactor
  have hLeftCommutatorEnergy :=
    sourceRootCompletedLeftCommutatorLeftLeg_basisEnergy_le_right owner lambda
      basis hRightCommutatorLeft
  have hRightCommutatorEnergy :=
    sourceRootCompletedRightCommutatorRightLeg_basisEnergy_le_common owner
      lambda basis transport hCommonRight
  have hleft :
      (∑' i, ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2) +
          ((∑' i, ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
            (basis i)‖ ^ 2) +
          ∑' i, ‖sourceRootCompletedLeftCommutatorLeftLeg owner lambda
            (basis i)‖ ^ 2) ≤
        ‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
            (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
              (basis i)‖ ^ 2) +
          2 * (∑' i,
            ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
              (basis i)‖ ^ 2) := by
    linarith
  have hright :
      (∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
          (basis i)‖ ^ 2) +
          ((∑' i,
            ‖sourceRootCompletedRightCommutatorRightLeg owner lambda transport
              (basis i)‖ ^ 2) +
          ∑' i, ‖sourceRootCompletedCommonRightLeg owner lambda transport
            (basis i)‖ ^ 2) ≤
        3 * (∑' i,
          ‖sourceRootCompletedCommonRightLeg owner lambda transport
            (basis i)‖ ^ 2) := by
    linarith
  exact hbound.trans (mul_le_mul (Real.sqrt_le_sqrt hleft)
    (Real.sqrt_le_sqrt hright) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Proof 405's actual fixed-quotient corner equals the root-completed owner.
This removes Proof 433's nonhomogeneous prolate energy from the next analytic
contract without changing the represented operator. -/
theorem sourceFixedQuotientCorner_eq_rootCompleted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) :
    sourceBandProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda =
      sourceRootCompletedFixedQuotientCorner owner lambda transport := by
  rw [compressedDetector_eq_sourceCompressedDetectorRoots]
  have hInner : IsIdempotentElem (sourceSoninProjection lambda) :=
    (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hSupportInner : radialSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  have hBandInner : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    change (radialSupportProjection lambda - sourceSoninProjection lambda) *
      sourceSoninProjection lambda = 0
    calc
      _ = radialSupportProjection lambda * sourceSoninProjection lambda -
          sourceSoninProjection lambda * sourceSoninProjection lambda := by
            noncomm_ring
      _ = 0 := by rw [hSupportInner, hInner]; noncomm_ring
  have hSecond : IsIdempotentElem
      (sourceFourierSupportProjection lambda) :=
    (sourceFourierSupportProjection_isStarProjection lambda).isIdempotentElem
  have hSecondInner : sourceFourierSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.right_starProjection_absorbs_intersection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  simpa only [sourceRootCompletedFixedQuotientCorner,
      ContinuousLinearMap.mul_def] using
    (detector_innerCorner_transport_eq_rootCompleted
      (band := sourceBandProjection lambda)
      (inner := sourceSoninProjection lambda)
      (secondSupport := sourceFourierSupportProjection lambda)
      (leftRoot := sourceCompressedDetectorLeftRoot owner lambda)
      (rightRoot := sourceCompressedDetectorRightRoot owner lambda)
      (transport := transport) hInner hBandInner hSecond hSecondInner)

/-- The normalized finite-Euler transport is the concrete family-uniform
instance of the root-completed first-jet identity. -/
theorem sourceFiniteEulerFixedQuotientCorner_eq_rootCompleted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) ∘L
        sourceBandProjection lambda =
      sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) := by
  exact sourceFixedQuotientCorner_eq_rootCompleted owner lambda
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

/-- The literal normalized finite-Euler first jet is a bounded sandwich of
the fixed source detector commutator.  In particular, all dependence on the
visible prime family occurs in the single contraction `A_S`; no renewal atom
or physical branch is exposed by this identity. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_fixedCommutatorSandwich
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      sourceBandProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (detectorOperator owner) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L
        sourceBandProjection lambda := by
  rw [sourceRootCompletedFiniteEulerCorner_eq_centeredUnsplitRootPair,
    ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  have hInner : IsIdempotentElem (sourceSoninProjection lambda) :=
    (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  have hBandInner : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hInnerBand : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceBandProjection lambda * (rootConvolution owner).adjoint *
          rootConvolution owner * sourceSoninProjection lambda *
          (normalizedFiniteEulerInverse family - 1) *
          sourceBandProjection lambda =
      sourceBandProjection lambda *
          CCM24FiniteSTwoSidedRootRecombination.commutator
            ((rootConvolution owner).adjoint * rootConvolution owner)
            (sourceSoninProjection lambda) *
          sourceSoninProjection lambda * normalizedFiniteEulerInverse family *
          sourceBandProjection lambda by
    calc
      sourceBandProjection lambda * (rootConvolution owner).adjoint *
            rootConvolution owner * sourceSoninProjection lambda *
            (normalizedFiniteEulerInverse family - 1) *
            sourceBandProjection lambda =
          sourceBandProjection lambda *
            ((rootConvolution owner).adjoint * rootConvolution owner) *
            sourceSoninProjection lambda *
            (normalizedFiniteEulerInverse family - 1) *
            sourceBandProjection lambda := by
        noncomm_ring
      _ = sourceBandProjection lambda *
            CCM24FiniteSTwoSidedRootRecombination.commutator
              ((rootConvolution owner).adjoint * rootConvolution owner)
              (sourceSoninProjection lambda) *
            sourceSoninProjection lambda * normalizedFiniteEulerInverse family *
            sourceBandProjection lambda :=
        centeredDetectorPair_eq_fixedCommutatorSandwich
          (sourceBandProjection lambda) (sourceSoninProjection lambda)
          ((rootConvolution owner).adjoint * rootConvolution owner)
          (normalizedFiniteEulerInverse family) hInner hBandInner hInnerBand

end CCM24FiniteSRootCompletedFirstJet
end CCM25Concrete
end Source
end ConnesWeilRH
