import ConnesWeilRH.Dev.C1PositiveTraceWindowProducer
import ConnesWeilRH.Dev.C1PositiveTraceTraceContinuity

/-!
# C1 positive-trace cutoff adapter

This module turns the finite-window positive `F^* F` construction into a
genuine sequence on one fixed whole-line Hilbert carrier.  The local input and
output Hilbert bases are chosen independently at each cutoff, while the source
basis is deliberately fixed.  The two analytic facts that are still missing
are stored explicitly: the cutoff remainder tends to zero, and the corrected
trace tends to the same-owner C1 Weil square.

Nothing here identifies a finite window trace with `C1SameOwnerWeil.qw`, and
the remainder is not defined to be zero.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1PositiveTraceCutoffAdapter

open MeasureTheory Filter
open scoped InnerProduct InnerProductSpace Topology
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceLimitBridge
open C1PositiveTraceTraceContinuity
open C1PositiveTraceWindowProducer

noncomputable section

/-- A symmetric, test-owned cutoff radius.  The extra `n + 1` makes every
window strictly larger than the compact support bound and lets the window grow
without changing the source Hilbert carrier. -/
noncomputable def cutoffRadius
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) : ℝ :=
  C1SameOwnerWeil.supportRadius g + (n : ℝ) + 1

noncomputable def cutoffLower
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) : ℝ :=
  -cutoffRadius g n

noncomputable def cutoffUpper
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) : ℝ :=
  cutoffRadius g n

theorem cutoffRadius_nonnegative
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    0 ≤ cutoffRadius g n := by
  have hsupport : 0 ≤ C1SameOwnerWeil.supportRadius g :=
    C1SameOwnerWeil.supportRadius_nonnegative g
  have hn : 0 ≤ (n : ℝ) := by positivity
  dsimp [cutoffRadius]
  linarith

theorem cutoffLower_le_cutoffUpper
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    cutoffLower g n ≤ cutoffUpper g n := by
  dsimp [cutoffLower, cutoffUpper]
  linarith [cutoffRadius_nonnegative g n]

/-- Every cutoff already contains the compact support of its root test.  This
is a carrier fact, not a trace-limit assertion. -/
theorem support_subset_cutoffWindow
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    Function.support g.test ⊆ Set.Icc (cutoffLower g n) (cutoffUpper g n) := by
  intro x hx
  have hsupport := C1SameOwnerWeil.support_subset_Icc g hx
  rcases hsupport with ⟨hsupport_lower, hsupport_upper⟩
  have hradius : 0 ≤ C1SameOwnerWeil.supportRadius g :=
    C1SameOwnerWeil.supportRadius_nonnegative g
  have hn : 0 ≤ (n : ℝ) := by positivity
  dsimp [cutoffLower, cutoffUpper, cutoffRadius]
  constructor <;> linarith

theorem cutoffLower_antitone
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    Antitone (cutoffLower g) := by
  intro m n hmn
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  dsimp [cutoffLower, cutoffRadius]
  linarith

theorem cutoffUpper_monotone
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    Monotone (cutoffUpper g) := by
  intro m n hmn
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  dsimp [cutoffUpper, cutoffRadius]
  linarith

/-- The local Hilbert-basis index for the full input interval at cutoff `n`.
It is local proof data: the positive trace itself is always evaluated on the
one caller-supplied whole-line basis. -/
noncomputable def cutoffFullBasisIndex
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    Set (Lp ℂ 2 (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))) :=
  Classical.choose (exists_hilbertBasis ℂ
    (Lp ℂ 2 (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))))

noncomputable def cutoffFullBasis
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    HilbertBasis (cutoffFullBasisIndex g n) ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n)))) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ
    (Lp ℂ 2 (volume : Measure
      (BoundaryFullInputInterval (cutoffLower g n) (cutoffUpper g n))))))

noncomputable def cutoffOutputBasisIndex
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    Set (Lp ℂ 2 (volume : Measure
      (BoundaryOutputInterval (cutoffLower g n) (cutoffUpper g n)))) :=
  Classical.choose (exists_hilbertBasis ℂ
    (Lp ℂ 2 (volume : Measure
      (BoundaryOutputInterval (cutoffLower g n) (cutoffUpper g n)))))

noncomputable def cutoffOutputBasis
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    HilbertBasis (cutoffOutputBasisIndex g n) ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryOutputInterval (cutoffLower g n) (cutoffUpper g n)))) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ
    (Lp ℂ 2 (volume : Measure
      (BoundaryOutputInterval (cutoffLower g n) (cutoffUpper g n))))))

/-- The `n`th compact boundary square, represented on the fixed whole-line
carrier through the proved output zero extension. -/
noncomputable def cutoffPositiveBasisData
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    BasisHilbertSchmidtData globalBasis :=
  fullBoundaryPositiveBasisData g (cutoffLower g n) (cutoffUpper g n)
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffPositiveBasisData_positiveComposition_isTraceClass
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    IsTraceClassAlong globalBasis
      (cutoffPositiveBasisData g globalBasis n).positiveComposition := by
  exact BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong _

theorem cutoffPositiveBasisData_positiveComposition_eq_detector
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    (cutoffPositiveBasisData g globalBasis n).positiveComposition =
      windowedBoundaryDetector g (cutoffLower g n) (cutoffUpper g n) := by
  exact fullBoundaryPositiveBasisData_positiveComposition_eq_detector
    g (cutoffLower g n) (cutoffUpper g n)
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffPositiveBasisData_trace_re_nonnegative
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (cutoffPositiveBasisData g globalBasis n).positiveComposition).re := by
  exact BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative _

theorem cutoffPositiveBasisData_trace_eq_detector
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) (n : Nat) :
    ordinaryTraceAlong globalBasis
        (cutoffPositiveBasisData g globalBasis n).positiveComposition =
      ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector g (cutoffLower g n) (cutoffUpper g n)) := by
  exact congrArg (ordinaryTraceAlong globalBasis)
    (cutoffPositiveBasisData_positiveComposition_eq_detector g globalBasis n)

/- A concrete analytic witness for the diagonal Tannery step.  The limit
operator, its diagonal majorant, and the same-owner trace readback remain
caller-supplied data; this structure does not assert that any of them exist
for free. -/
structure CutoffDominatedTraceWitness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) where
  limitOperator : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2
  bound : nu → ℝ
  bound_summable : Summable bound
  diagonal_tendsto : ∀ i,
    Tendsto
      (fun n =>
        ⟪globalBasis i,
          (cutoffPositiveBasisData g globalBasis n).positiveComposition
            (globalBasis i)⟫_ℂ)
      atTop
      (𝓝 (⟪globalBasis i, limitOperator (globalBasis i)⟫_ℂ))
  diagonal_dominated : ∀ n i,
    ‖⟪globalBasis i,
      (cutoffPositiveBasisData g globalBasis n).positiveComposition
        (globalBasis i)⟫_ℂ‖ ≤ bound i
  limitTrace_re_qw :
    (ordinaryTraceAlong globalBasis limitOperator).re =
      C1SameOwnerWeil.qw g

theorem cutoffPositiveBasisData_trace_re_tendsto_of_dominatedWitness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis) :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re)
      atTop
      (𝓝 (ordinaryTraceAlong globalBasis witness.limitOperator).re) := by
  exact tendsto_ordinaryTraceAlong_re_of_dominated_diagonal
    globalBasis
    (fun n => (cutoffPositiveBasisData g globalBasis n).positiveComposition)
    witness.limitOperator witness.bound witness.bound_summable
    witness.diagonal_tendsto witness.diagonal_dominated

theorem cutoffReadback_tendsto_qw_of_dominatedWitness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis)
    (remainder : Nat → Real)
    (hremainder : Tendsto remainder atTop (𝓝 (0 : Real))) :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re -
          remainder n)
      atTop
      (𝓝 (C1SameOwnerWeil.qw g)) := by
  have htrace := cutoffPositiveBasisData_trace_re_tendsto_of_dominatedWitness
    g globalBasis witness
  have hcorrected := htrace.sub hremainder
  simpa [witness.limitTrace_re_qw] using hcorrected

/-- The two remaining analytic obligations for this concrete cutoff sequence.
The first is the genuine residual estimate `D_n -> 0`; the second is the
same-owner trace readback after that correction. -/
structure CutoffLimitContracts
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2) where
  remainder : Nat → Real
  remainder_tendsto_zero : Tendsto remainder atTop (𝓝 (0 : Real))
  readback_tendsto_qw :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffPositiveBasisData g globalBasis n).positiveComposition).re -
          remainder n)
      atTop (𝓝 (C1SameOwnerWeil.qw g))

/-- Assemble the two cutoff contracts from a dominated diagonal witness and a
separate remainder limit.  The witness still owns the limit operator,
majorant, and same-owner trace readback; this definition merely composes the
proved Tannery step with `remainder -> 0`. -/
noncomputable def cutoffLimitContractsOfDominatedWitness
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (witness : CutoffDominatedTraceWitness g globalBasis)
    (remainder : Nat → Real)
    (hremainder : Tendsto remainder atTop (𝓝 (0 : Real))) :
    CutoffLimitContracts g globalBasis where
  remainder := remainder
  remainder_tendsto_zero := hremainder
  readback_tendsto_qw :=
    cutoffReadback_tendsto_qw_of_dominatedWitness
      g globalBasis witness remainder hremainder

/-- Assemble the abstract order consumer from the actual fixed-carrier cutoff
operators, but only after the two analytic contracts have been supplied. -/
noncomputable def positiveTraceLimitFamilyOfCutoffContracts
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (contracts : CutoffLimitContracts g globalBasis) :
    PositiveTraceLimitFamily globalBasis g where
  traceData := cutoffPositiveBasisData g globalBasis
  remainder := contracts.remainder
  remainder_tendsto_zero := contracts.remainder_tendsto_zero
  readback_tendsto_qw := contracts.readback_tendsto_qw

theorem qw_nonnegative_of_cutoffLimitContracts
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (contracts : CutoffLimitContracts g globalBasis) :
    0 ≤ C1SameOwnerWeil.qw g :=
  qw_nonnegative_of_positiveTraceLimitFamily
    (positiveTraceLimitFamilyOfCutoffContracts g globalBasis contracts)

theorem spectral_nonnegative_of_cutoffLimitContracts
    {nu : Type*}
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (contracts : CutoffLimitContracts g globalBasis) :
    0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare :=
  spectral_nonnegative_of_positiveTraceLimitFamily
    (positiveTraceLimitFamilyOfCutoffContracts g globalBasis contracts)

end
end C1PositiveTraceCutoffAdapter
end Dev
end Source
end ConnesWeilRH
