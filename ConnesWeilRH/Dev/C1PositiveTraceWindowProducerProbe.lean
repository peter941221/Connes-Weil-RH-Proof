import ConnesWeilRH.Dev.C1PositiveTraceWindowProducer

/-!
# Probe for the finite-window positive-trace producer

The probe checks the concrete owner, its trace-class witness, the positivity
readback, and the basis-existence closure.  It intentionally does not create
a `PositiveTracePairLimitFamily`, because the missing cutoff-limit readback is
the remaining analytic obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceWindowProducerProbe

open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceWindowProducer

noncomputable section

theorem probe_window_trace_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
      (fullBoundaryPositivePairData g a c fullBasis outputBasis
        globalBasis).traceProduct).re :=
  fullBoundaryPositivePairData_trace_re_nonnegative
    g a c fullBasis outputBasis globalBasis

theorem probe_detector_trace_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
      (windowedBoundaryDetector g a c)).re :=
  fullBoundaryPositivePairData_detector_trace_re_nonnegative
    g a c fullBasis outputBasis globalBasis

theorem probe_output_zero_extension_adjoint_comp
    (a c : ℝ) :
    (fullBoundaryOutputZeroExtension a c).adjoint ∘L
        fullBoundaryOutputZeroExtension a c =
      ContinuousLinearMap.id ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))) :=
  fullBoundaryOutputZeroExtension_adjoint_comp a c

theorem probe_square_positiveComposition_eq_detector
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
      globalBasis).positiveComposition =
      windowedBoundaryDetector g a c :=
  fullBoundaryPositiveBasisData_positiveComposition_eq_detector
    g a c fullBasis outputBasis globalBasis

theorem probe_square_trace_isTraceClass
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    IsTraceClassAlong globalBasis
      (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
        globalBasis).positiveComposition :=
  fullBoundaryPositiveBasisData_positiveComposition_isTraceClass
    g a c fullBasis outputBasis globalBasis

theorem probe_square_trace_eq_detector
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
          globalBasis).positiveComposition =
      CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector g a c) :=
  fullBoundaryPositiveBasisData_trace_eq_detector
    g a c fullBasis outputBasis globalBasis

theorem probe_square_trace_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) :
    0 ≤ (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
      (fullBoundaryPositiveBasisData g a c fullBasis outputBasis
        globalBasis).positiveComposition).re :=
  fullBoundaryPositiveBasisData_trace_re_nonnegative
    g a c fullBasis outputBasis globalBasis

#print axioms fullBoundaryPositivePairData
#print axioms fullBoundaryPositivePairData_traceProduct_isTraceClass
#print axioms fullBoundaryPositivePairData_trace_re_nonnegative
#print axioms exists_fullBoundaryPositivePairData_trace_re_nonnegative
#print axioms fullBoundaryPositiveOperator
#print axioms fullBoundaryPositiveBasisData
#print axioms fullBoundaryPositiveBasisData_positiveComposition_isTraceClass
#print axioms fullBoundaryOutputZeroExtension_adjoint_comp
#print axioms fullBoundaryPositiveBasisData_positiveComposition_eq_detector
#print axioms fullBoundaryPositiveBasisData_trace_re_nonnegative
#print axioms fullBoundaryPositiveBasisData_trace_eq_detector
#print axioms probe_window_trace_nonnegative
#print axioms probe_detector_trace_nonnegative
#print axioms probe_output_zero_extension_adjoint_comp
#print axioms probe_square_positiveComposition_eq_detector
#print axioms probe_square_trace_isTraceClass
#print axioms probe_square_trace_eq_detector
#print axioms probe_square_trace_nonnegative

end
end C1PositiveTraceWindowProducerProbe
end Dev
end Source
end ConnesWeilRH
