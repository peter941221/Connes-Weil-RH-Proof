import ConnesWeilRH.Dev.C1PositiveTraceCutoffObstruction
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# C1 positive-trace cutoff growth

The finite-window positive trace is a Hilbert--Schmidt energy.  This module
starts the concrete growth calculation by moving that energy from the fixed
whole-line carrier to the finite input interval of the continuous kernel.
The move uses only the already-proved Hilbert--Schmidt trace cycle and the
restriction/zero-extension identity; no limit or RH-level premise is added.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffGrowth

open MeasureTheory
open TopologicalSpace
open scoped ComplexConjugate InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open C1PositiveTraceCutoffObstruction
open C1PositiveTraceWindowProducer
open CCM25Concrete.SelectedCrossingKernel
open CCM25Concrete.SelectedCrossingOperatorBridge

noncomputable section

/-- An orthonormal Hilbert basis in a separable metric space has a countable
index.  The disjoint-ball proof is kept local because `exists_hilbertBasis`
itself intentionally allows an arbitrary index set. -/
theorem countable_hilbertBasis_index
    {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [SeparableSpace E]
    (basis : HilbertBasis ι ℂ E) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (basis i) (1 / 3 : ℝ))
  · intro i j hij
    apply Set.disjoint_left.2
    intro z hzi hzj
    have hzi' : dist z (basis i) < (1 / 3 : ℝ) := by
      simpa only [Metric.mem_ball] using hzi
    have hzj' : dist z (basis j) < (1 / 3 : ℝ) := by
      simpa only [Metric.mem_ball] using hzj
    have htriangle : dist (basis i) (basis j) < (2 / 3 : ℝ) := by
      calc
        dist (basis i) (basis j) ≤
            dist (basis i) z + dist z (basis j) := dist_triangle _ _ _
        _ = dist z (basis i) + dist z (basis j) := by
          rw [dist_comm (basis i) z]
        _ < (1 / 3 : ℝ) + (1 / 3 : ℝ) := add_lt_add hzi' hzj'
        _ = (2 / 3 : ℝ) := by norm_num
    have hnormSq : ‖basis i - basis j‖ ^ 2 = (2 : ℝ) := by
      rw [@norm_sub_sq ℂ E]
      rw [basis.orthonormal.norm_eq_one i,
        basis.orthonormal.inner_eq_zero hij,
        basis.orthonormal.norm_eq_one j]
      norm_num
    have hnorm : (1 : ℝ) ≤ ‖basis i - basis j‖ := by
      have hnonneg : 0 ≤ ‖basis i - basis j‖ := norm_nonneg _
      nlinarith
    have hdist : (1 : ℝ) ≤ dist (basis i) (basis j) := by
      simpa only [dist_eq_norm] using hnorm
    linarith
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact (Metric.nonempty_ball).2 (by norm_num)

/-- The whole-line trace of the compact boundary square can be cycled to the
continuous-kernel pair on its finite input interval.  This is the ownership
bridge needed before evaluating the trace as an integral. -/
theorem fullBoundaryPositivePairData_trace_eq_kernelPairData
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*} [Countable iota]
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    ordinaryTraceAlong globalBasis
        (fullBoundaryPositivePairData g a c fullBasis outputBasis
          globalBasis).traceProduct =
      ordinaryTraceAlong fullBasis
        (ContinuousKernelHilbertSchmidt.pairData
          (volume : Measure (BoundaryFullInputInterval a c))
          (volume : Measure (BoundaryOutputInterval a c))
          (fullBoundaryRootKernel g a c)
          (fullBoundaryRootKernel g a c)
          fullBasis).traceProduct := by
  let data := fullBoundaryPositivePairData g a c fullBasis outputBasis
    globalBasis
  let kernelData := ContinuousKernelHilbertSchmidt.pairData
    (volume : Measure (BoundaryFullInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (fullBoundaryRootKernel g a c)
    (fullBoundaryRootKernel g a c)
    fullBasis
  have hfactor :
      data.right ∘L data.left.adjoint =
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (BoundaryFullInputInterval a c))
          (volume : Measure (BoundaryOutputInterval a c))
          (fullBoundaryRootKernel g a c)) ∘L
          (ContinuousKernelHilbertSchmidt.operator
            (volume : Measure (BoundaryFullInputInterval a c))
            (volume : Measure (BoundaryOutputInterval a c))
            (fullBoundaryRootKernel g a c)).adjoint := by
    apply ContinuousLinearMap.ext
    intro u
    change
      fullBoundaryRootFactor g a c
          ((fullBoundaryRootFactor g a c).adjoint u) =
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (BoundaryFullInputInterval a c))
          (volume : Measure (BoundaryOutputInterval a c))
          (fullBoundaryRootKernel g a c))
          ((ContinuousKernelHilbertSchmidt.operator
            (volume : Measure (BoundaryFullInputInterval a c))
            (volume : Measure (BoundaryOutputInterval a c))
            (fullBoundaryRootKernel g a c)).adjoint u)
    simp only [fullBoundaryRootFactor, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_comp]
    rw [← kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    rw [globalL2ToKernelInterval_zeroExtension]
  calc
    ordinaryTraceAlong globalBasis data.traceProduct =
        ordinaryTraceAlong outputBasis
          (data.right ∘L data.left.adjoint) :=
      data.ordinaryTraceAlong_traceProduct_eq_cyclic outputBasis
    _ = ordinaryTraceAlong outputBasis
          ((ContinuousKernelHilbertSchmidt.operator
            (volume : Measure (BoundaryFullInputInterval a c))
            (volume : Measure (BoundaryOutputInterval a c))
            (fullBoundaryRootKernel g a c)) ∘L
            (ContinuousKernelHilbertSchmidt.operator
              (volume : Measure (BoundaryFullInputInterval a c))
              (volume : Measure (BoundaryOutputInterval a c))
              (fullBoundaryRootKernel g a c)).adjoint) :=
      congrArg (ordinaryTraceAlong outputBasis) hfactor
    _ = ordinaryTraceAlong fullBasis kernelData.traceProduct :=
      (kernelData.ordinaryTraceAlong_traceProduct_eq_cyclic outputBasis).symm

/-- A diagonal section of the full boundary kernel has the expected
pointwise `L2` energy.  The displayed integral still lives on the finite
input interval; support removal and translation are separate lemmas below. -/
theorem fullBoundaryRootKernel_section_inner_eq_normSq_integral
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (t : BoundaryOutputInterval a c) :
    inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) t)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) t) =
      ∫ x in Set.Icc (a - c) (c - a),
        (Complex.normSq (g.test (x - t.1)) : ℂ) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryFullInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (fullBoundaryRootKernel g a c) t))
      (ContinuousMap.toLp 2
        (volume : Measure (BoundaryFullInputInterval a c)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (fullBoundaryRootKernel g a c) t)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x : BoundaryFullInputInterval a c,
      (fullBoundaryRootKernel g a c) (t, x) *
        star ((fullBoundaryRootKernel g a c) (t, x))
        ∂Measure.comap Subtype.val volume) = _
  calc
    (∫ x : BoundaryFullInputInterval a c,
        (fullBoundaryRootKernel g a c) (t, x) *
          star ((fullBoundaryRootKernel g a c) (t, x))
          ∂Measure.comap Subtype.val volume) =
        ∫ x : BoundaryFullInputInterval a c,
          (Complex.normSq (g.test (x.1 - t.1)) : ℂ)
            ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards with x
      change g.test (x.1 - t.1) * star (g.test (x.1 - t.1)) =
        (Complex.normSq (g.test (x.1 - t.1)) : ℂ)
      rw [Complex.normSq_eq_conj_mul_self]
      rw [starRingEnd_apply, mul_comm]
    _ = ∫ x in Set.Icc (a - c) (c - a),
        (Complex.normSq (g.test (x - t.1)) : ℂ) := by
      have hset : BoundaryFullInputInterval a c =
          Set.Icc (a - c) (c - a) := by
        ext x
        simp [BoundaryFullInputInterval, KernelInterval]
      rw [hset]
      exact integral_subtype_comap (μ := (volume : Measure ℝ))
        (s := Set.Icc (a - c) (c - a)) measurableSet_Icc
        (fun x : ℝ => (Complex.normSq (g.test (x - t.1)) : ℂ))

/-- Compact support removes the complement of the finite input interval from
the section energy. -/
theorem fullBoundaryRootKernel_section_normSq_integral_eq_whole
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (t : BoundaryOutputInterval a c) :
    (∫ x in Set.Icc (a - c) (c - a),
      (Complex.normSq (g.test (x - t.1)) : ℂ)) =
      ∫ x : ℝ, (Complex.normSq (g.test (x - t.1)) : ℂ) := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (a - c) (c - a)
  · rw [Set.indicator_of_mem hx]
  · have hzero : g.test (x - t.1) = 0 := by
      by_contra hnonzero
      exact hx (fullInput_mem_of_kernel_ne_zero g a c hsupp t hnonzero)
    simp [Set.indicator, hx, hzero]

/-- Translation invariance of Lebesgue measure removes the output coordinate
from the whole-line section energy. -/
theorem fullBoundaryRootKernel_section_whole_eq_mass
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (t : BoundaryOutputInterval a c) :
    (∫ x : ℝ, (Complex.normSq (g.test (x - t.1)) : ℂ)) =
      ∫ x : ℝ, (Complex.normSq (g.test x) : ℂ) := by
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self
      (fun x : ℝ => (Complex.normSq (g.test x) : ℂ)) (-t.1))

/-- Read the positive boundary trace as an integral of the section energies on
the reflected output interval. -/
theorem fullBoundaryPositivePairData_trace_eq_output_section_energy
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*} [Countable iota]
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    ordinaryTraceAlong globalBasis
        (fullBoundaryPositivePairData g a c fullBasis outputBasis
          globalBasis).traceProduct =
      ∫ y, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) y)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) y) := by
  rw [fullBoundaryPositivePairData_trace_eq_kernelPairData
    g a c fullBasis outputBasis globalBasis]
  apply ContinuousKernelHilbertSchmidt.pairData_trace_eq_kernel_inner
    (volume : Measure (BoundaryFullInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c))
    (fullBoundaryRootKernel g a c) (fullBoundaryRootKernel g a c) fullBasis
  · intro i
    exact ContinuousKernelHilbertSchmidt.coefficient_inner_integrable
      (volume : Measure (BoundaryFullInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (fullBoundaryRootKernel g a c) (fullBoundaryRootKernel g a c) fullBasis i
  · exact ContinuousKernelHilbertSchmidt.coefficient_inner_integral_norm_summable
      (volume : Measure (BoundaryFullInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (fullBoundaryRootKernel g a c) (fullBoundaryRootKernel g a c) fullBasis

/-- Exact finite-window energy formula.  The trace is proportional to the
reflected output-window length, with coefficient equal to the whole-line
`L2` mass of the root. -/
theorem fullBoundaryPositivePairData_trace_eq_window_length_mul_mass
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hac : a ≤ c)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {iota kappa nu : Type*} [Countable iota]
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    ordinaryTraceAlong globalBasis
        (fullBoundaryPositivePairData g a c fullBasis outputBasis
          globalBasis).traceProduct =
      ((c - a : ℝ) : ℂ) *
        (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) := by
  rw [fullBoundaryPositivePairData_trace_eq_output_section_energy
    g a c fullBasis outputBasis globalBasis]
  calc
    (∫ y, inner ℂ
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) y)
        (ContinuousKernelHilbertSchmidt.sectionToLp
          (volume : Measure (BoundaryFullInputInterval a c))
          (fullBoundaryRootKernel g a c) y)) =
        ∫ _y : BoundaryOutputInterval a c,
          (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [fullBoundaryRootKernel_section_inner_eq_normSq_integral]
      rw [fullBoundaryRootKernel_section_normSq_integral_eq_whole
        g a c hsupp y]
      exact fullBoundaryRootKernel_section_whole_eq_mass g a c y
    _ = ((c - a : ℝ) : ℂ) *
          (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) := by
      rw [integral_const]
      change ((((volume : Measure (BoundaryOutputInterval a c)) Set.univ).toReal : ℝ) : ℂ) *
        (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) = _
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring_nf

/-- The exact formula specialized to the project's canonical cutoff owner. -/
theorem cutoffPositiveBasisData_trace_eq_window_length_mul_mass
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition =
      ((cutoffUpper g n - cutoffLower g n : ℝ) : ℂ) *
        (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) := by
  letI : MeasureTheory.IsSeparable (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n))) :=
    MeasureTheory.isSeparable_of_sigmaFinite
      (volume : Measure
        (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℂ 2 (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SeparableSpace (Lp ℂ 2 (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))) := by
    infer_instance
  letI : Countable (cutoffFullBasisIndex g n) :=
    countable_hilbertBasis_index (cutoffFullBasis g n)
  calc
    ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition =
      ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector g (cutoffLower g n) (cutoffUpper g n)) :=
      congrArg (ordinaryTraceAlong globalBasis)
        (cutoffPositiveBasisData_positiveComposition_eq_detector g
          globalBasis n)
    _ = ordinaryTraceAlong globalBasis
        (fullBoundaryPositivePairData g (cutoffLower g n) (cutoffUpper g n)
          (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis).traceProduct := by
      rw [fullBoundaryPositivePairData_traceProduct_eq_detector
        g (cutoffLower g n) (cutoffUpper g n)
        (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis]
    _ = ((cutoffUpper g n - cutoffLower g n : ℝ) : ℂ) *
        (∫ x : ℝ, (Complex.normSq (g.test x) : ℂ)) :=
      fullBoundaryPositivePairData_trace_eq_window_length_mul_mass
        g (cutoffLower g n) (cutoffUpper g n)
        (cutoffLower_le_cutoffUpper g n)
        (support_subset_cutoffWindow g n)
        (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

/-- A nonzero compact-log root has strictly positive whole-line `L2` mass.
The proof uses continuity and compact support only; it does not invoke a
spectral or RH-level statement. -/
theorem integral_normSq_pos_of_test_ne_zero
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (hg : g.test ≠ 0) :
    0 < ∫ x : ℝ, Complex.normSq (g.test x) := by
  have hpoint : ∃ x : ℝ, g.test x ≠ 0 := by
    by_contra! hpoint
    apply hg
    ext x
    exact hpoint x
  obtain ⟨x, hx⟩ := hpoint
  have hcont : Continuous (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_normSq.comp g.test.continuous
  have hcompact : HasCompactSupport
      (fun y : ℝ => Complex.normSq (g.test y)) := by
    simpa only [Function.comp_apply] using
      g.compactSupport.comp_left (by simp)
  apply integral_pos_of_integrable_nonneg_nonzero
  · exact hcont
  · exact hcont.integrable_of_hasCompactSupport hcompact
  · intro y
    exact Complex.normSq_nonneg (g.test y)
  · exact (Complex.normSq_pos.mpr hx).ne'

/-- Taking real parts of the complex finite-window energy formula produces
the scalar mass-growth identity used by the obstruction below. -/
theorem cutoffPositiveBasisData_trace_re_eq_window_length_mul_mass
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    (ordinaryTraceAlong globalBasis
      (cutoffPositiveBasisData g globalBasis n).positiveComposition).re =
      (cutoffUpper g n - cutoffLower g n) *
        ∫ x : ℝ, Complex.normSq (g.test x) := by
  have htrace := congrArg Complex.re
    (cutoffPositiveBasisData_trace_eq_window_length_mul_mass g globalBasis n)
  rw [integral_complex_ofReal] at htrace
  simpa [Complex.mul_re] using htrace

/-- The canonical symmetric cutoff traces are unbounded for every nonzero
root: their exact slope is twice the strictly positive `L2` mass. -/
theorem cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (hg : g.test ≠ 0) :
    ∀ boundValue : ℝ, ∃ n,
      boundValue < (ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition).re := by
  let mass : ℝ := ∫ x : ℝ, Complex.normSq (g.test x)
  have hmass : 0 < mass := by
    dsimp [mass]
    exact integral_normSq_pos_of_test_ne_zero g hg
  have htwoMass : 0 < 2 * mass :=
    mul_pos (by norm_num) hmass
  intro boundValue
  obtain ⟨n, hn⟩ := exists_nat_gt
    (boundValue / (2 * mass) - C1SameOwnerWeil.supportRadius g - 1)
  refine ⟨n, ?_⟩
  rw [cutoffPositiveBasisData_trace_re_eq_window_length_mul_mass]
  change boundValue < (cutoffUpper g n - cutoffLower g n) * mass
  have hlinear : boundValue / (2 * mass) <
      C1SameOwnerWeil.supportRadius g + (n : ℝ) + 1 := by
    linarith
  have hmul : boundValue <
      (C1SameOwnerWeil.supportRadius g + (n : ℝ) + 1) * (2 * mass) :=
    (div_lt_iff₀ htwoMass).mp hlinear
  dsimp [cutoffUpper, cutoffLower, cutoffRadius]
  nlinarith [hmul]

/-- The explicit linear growth rules out the current summable
diagonal-majorant cutoff witness for every nonzero compact-log root. -/
theorem not_nonempty_cutoffDominatedTraceWitness_of_test_ne_zero
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (hg : g.test ≠ 0) :
    ¬ Nonempty (CutoffDominatedTraceWitness g globalBasis) :=
  not_exists_cutoffDominatedTraceWitness_of_trace_re_unbounded g globalBasis
    (cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      g globalBasis hg)

end
end C1PositiveTraceCutoffGrowth
end Dev
end Source
end ConnesWeilRH
