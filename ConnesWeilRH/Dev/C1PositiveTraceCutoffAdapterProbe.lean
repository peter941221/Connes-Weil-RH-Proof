import ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapter

/-!
# Probe for the C1 positive-trace cutoff adapter

This probe checks the fixed-carrier cutoff sequence and the explicit analytic
boundary.  It does not fabricate either cutoff contract.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffAdapterProbe

open MeasureTheory Filter
open scoped InnerProduct InnerProductSpace Topology
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter

noncomputable section

theorem probe_cutoff_contains_support
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    Function.support g.test ⊆
      Set.Icc (cutoffLower g n) (cutoffUpper g n) :=
  support_subset_cutoffWindow g n

theorem probe_cutoff_trace_nonnegative
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (cutoffPositiveBasisData g globalBasis n).positiveComposition).re :=
  cutoffPositiveBasisData_trace_re_nonnegative g globalBasis n

theorem probe_cutoff_trace_eq_detector
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition =
      ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector g (cutoffLower g n) (cutoffUpper g n)) :=
  cutoffPositiveBasisData_trace_eq_detector g globalBasis n

theorem probe_cutoff_contract_consumer
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (contracts : CutoffLimitContracts g globalBasis) :
    0 ≤ C1SameOwnerWeil.qw g :=
  qw_nonnegative_of_cutoffLimitContracts g globalBasis contracts

theorem probe_cutoff_trace_limit_from_witness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis) :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re)
      atTop
      (𝓝 (ordinaryTraceAlong globalBasis witness.limitOperator).re) :=
  cutoffPositiveBasisData_trace_re_tendsto_of_dominatedWitness
    g globalBasis witness

noncomputable def probe_cutoff_contracts_from_witness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis)
    (remainder : Nat → Real)
    (hremainder : Tendsto remainder atTop (𝓝 (0 : Real))) :
    CutoffLimitContracts g globalBasis :=
  cutoffLimitContractsOfDominatedWitness
    g globalBasis witness remainder hremainder

#print axioms cutoffRadius
#print axioms support_subset_cutoffWindow
#print axioms cutoffPositiveBasisData
#print axioms cutoffPositiveBasisData_positiveComposition_isTraceClass
#print axioms cutoffPositiveBasisData_positiveComposition_eq_detector
#print axioms cutoffPositiveBasisData_trace_re_nonnegative
#print axioms CutoffLimitContracts
#print axioms CutoffDominatedTraceWitness
#print axioms cutoffPositiveBasisData_trace_re_tendsto_of_dominatedWitness
#print axioms cutoffReadback_tendsto_qw_of_dominatedWitness
#print axioms cutoffLimitContractsOfDominatedWitness
#print axioms positiveTraceLimitFamilyOfCutoffContracts
#print axioms qw_nonnegative_of_cutoffLimitContracts
#print axioms spectral_nonnegative_of_cutoffLimitContracts
#print axioms probe_cutoff_contains_support
#print axioms probe_cutoff_trace_nonnegative
#print axioms probe_cutoff_trace_eq_detector
#print axioms probe_cutoff_contract_consumer
#print axioms probe_cutoff_trace_limit_from_witness
#print axioms probe_cutoff_contracts_from_witness

end
end C1PositiveTraceCutoffAdapterProbe
end Dev
end Source
end ConnesWeilRH
