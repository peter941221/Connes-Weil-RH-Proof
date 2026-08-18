import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.CompactLogDetectorTraceBridge

/-!
# C1 positive-trace window producer

The compact boundary factor already has the correct analytic shape
`F : H -> G`: it is Hilbert--Schmidt on every named whole-line basis.  This
file packages the same factor on both sides of `A†B`, producing the genuine
positive operator `F†F` and its legal diagonal trace.

This is deliberately a finite-window producer only.  No theorem here says
that the window trace, after a cutoff limit, is `C1SameOwnerWeil.qw`; that
same-owner readback remains a field of `PositiveTracePairLimitFamily`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceWindowProducer

open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CompactLogDetectorTraceBridge
open C1PositiveTraceLimitBridge
open CCM25Concrete.SelectedCrossingOperatorBridge

noncomputable section

/-- The complete compact boundary factor used twice as a Hilbert--Schmidt
factor.  The compact/input/output bases are proof data for summability; the
source owner is the single `globalBasis`. -/
noncomputable def fullBoundaryPositivePairData
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))
      globalBasis :=
  { left := fullBoundaryRootFactor g a c
    right := fullBoundaryRootFactor g a c
    left_summable_normSq :=
      fullBoundaryRootFactor_summable_normSq
        g a c fullBasis outputBasis globalBasis
    right_summable_normSq :=
      fullBoundaryRootFactor_summable_normSq
        g a c fullBasis outputBasis globalBasis }

theorem fullBoundaryPositivePairData_self
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    (fullBoundaryPositivePairData g a c fullBasis outputBasis
      globalBasis).left =
      (fullBoundaryPositivePairData g a c fullBasis outputBasis
        globalBasis).right := by
  rfl

theorem fullBoundaryPositivePairData_traceProduct_eq_detector
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    (fullBoundaryPositivePairData g a c fullBasis outputBasis
      globalBasis).traceProduct =
      windowedBoundaryDetector g a c := by
  rfl

theorem fullBoundaryPositivePairData_traceProduct_isTraceClass
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    IsTraceClassAlong globalBasis
      (fullBoundaryPositivePairData g a c fullBasis outputBasis
        globalBasis).traceProduct := by
  exact BasisHilbertSchmidtPairData.traceProduct_isTraceClassAlong _

/-- The finite-window positive trace is nonnegative for the actual source
owner, not merely for an abstract operator symbol. -/
theorem fullBoundaryPositivePairData_trace_re_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (fullBoundaryPositivePairData g a c fullBasis outputBasis
        globalBasis).traceProduct).re := by
  exact positiveTracePair_re_nonnegative_of_self
    (fullBoundaryPositivePairData g a c fullBasis outputBasis globalBasis)
    (fullBoundaryPositivePairData_self g a c fullBasis outputBasis globalBasis)

theorem fullBoundaryPositivePairData_detector_trace_re_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (windowedBoundaryDetector g a c)).re := by
  rw [← fullBoundaryPositivePairData_traceProduct_eq_detector
    g a c fullBasis outputBasis globalBasis]
  exact fullBoundaryPositivePairData_trace_re_nonnegative
    g a c fullBasis outputBasis globalBasis

/- The output interval is `[-c,-a]`; it is distinct from the complete input
   interval used by `fullBoundaryRootFactor` as its domain. -/
noncomputable def fullBoundaryOutputZeroExtension (a c : ℝ) :
    Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  kernelIntervalL2ZeroExtension (-c) (-a) 0

/- The pair above is the rectangular form.  Zero-extending its target gives a
   square `H -> H` operator, so a sequence of windows can share one source
   Hilbert basis and feed the original `PositiveTraceLimitFamily` type. -/
noncomputable def fullBoundaryPositiveOperator
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  fullBoundaryOutputZeroExtension a c ∘L fullBoundaryRootFactor g a c

theorem fullBoundaryPositiveOperator_basis_normSq_summable
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    Summable (fun i =>
      ‖fullBoundaryPositiveOperator g a c (globalBasis i)‖ ^ 2) := by
  exact PositiveTrace.summable_normSq_postcomp globalBasis
    (fullBoundaryRootFactor g a c) (fullBoundaryOutputZeroExtension a c)
    (fullBoundaryRootFactor_summable_normSq
      g a c fullBasis outputBasis globalBasis)

noncomputable def fullBoundaryPositiveBasisData
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    BasisHilbertSchmidtData globalBasis where
  operator := fullBoundaryPositiveOperator g a c
  summable_normSq :=
    fullBoundaryPositiveOperator_basis_normSq_summable
      g a c fullBasis outputBasis globalBasis

theorem fullBoundaryPositiveBasisData_positiveComposition_isTraceClass
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    IsTraceClassAlong globalBasis
      (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
        globalBasis).positiveComposition := by
  exact BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong _

theorem fullBoundaryOutputZeroExtension_adjoint_comp
    (a c : ℝ) :
    (fullBoundaryOutputZeroExtension a c).adjoint ∘L
        fullBoundaryOutputZeroExtension a c =
      ContinuousLinearMap.id ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) := by
  apply ContinuousLinearMap.ext
  intro u
  unfold fullBoundaryOutputZeroExtension
  rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
  simp only [ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  simpa only [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval] using
    (globalL2ToKernelInterval_zeroExtension (-c) (-a) 0 u)

theorem fullBoundaryPositiveBasisData_positiveComposition_eq_detector
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
      globalBasis).positiveComposition =
      windowedBoundaryDetector g a c := by
  unfold fullBoundaryPositiveBasisData BasisHilbertSchmidtData.positiveComposition
  unfold fullBoundaryPositiveOperator windowedBoundaryDetector
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hzero := fullBoundaryOutputZeroExtension_adjoint_comp a c
  change (fullBoundaryRootFactor g a c).adjoint
      ((fullBoundaryOutputZeroExtension a c).adjoint
        (fullBoundaryOutputZeroExtension a c
          (fullBoundaryRootFactor g a c u))) = _
  have hzero_apply :
      (fullBoundaryOutputZeroExtension a c).adjoint
          (fullBoundaryOutputZeroExtension a c
            (fullBoundaryRootFactor g a c u)) =
        fullBoundaryRootFactor g a c u := by
    have hzero_at := congrArg
      (fun map => map (fullBoundaryRootFactor g a c u)) hzero
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hzero_at
  rw [hzero_apply]

theorem fullBoundaryPositiveBasisData_trace_re_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
        globalBasis).positiveComposition).re :=
  BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative _

theorem fullBoundaryPositiveBasisData_trace_eq_detector
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    ordinaryTraceAlong globalBasis
        (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
          globalBasis).positiveComposition =
      ordinaryTraceAlong globalBasis (windowedBoundaryDetector g a c) := by
  exact congrArg (ordinaryTraceAlong globalBasis)
    (fullBoundaryPositiveBasisData_positiveComposition_eq_detector
      g a c fullBasis outputBasis globalBasis)

/-- A concrete basis choice exists at every fixed compact window.  This closes
only the existence of the finite-window positive-trace owner; it supplies no
limit or C1 readback. -/
theorem exists_fullBoundaryPositivePairData_trace_re_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ) :
    ∃ (fullIndex : Set
        (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
      (outputIndex : Set
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
      (globalIndex : Set cc20GlobalLogCrossingL2)
      (fullBasis : HilbertBasis (↥fullIndex) ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
      (outputBasis : HilbertBasis (↥outputIndex) ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
      (globalBasis : HilbertBasis (↥globalIndex) ℂ cc20GlobalLogCrossingL2),
      0 ≤ (ordinaryTraceAlong globalBasis
        (fullBoundaryPositivePairData g a c fullBasis outputBasis
          globalBasis).traceProduct).re := by
  classical
  obtain ⟨fullIndex, fullBasis, _⟩ :=
    exists_hilbertBasis ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c)))
  obtain ⟨outputIndex, outputBasis, _⟩ :=
    exists_hilbertBasis ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))
  obtain ⟨globalIndex, globalBasis, _⟩ :=
    exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
  exact ⟨fullIndex, outputIndex, globalIndex, fullBasis, outputBasis,
    globalBasis, fullBoundaryPositivePairData_trace_re_nonnegative
      g a c fullBasis outputBasis globalBasis⟩

end
end C1PositiveTraceWindowProducer
end Dev
end Source
end ConnesWeilRH
