import ConnesWeilRH.Dev.R1ShapeProbe979
import ConnesWeilRH.Dev.A24RetypeGateSeam914
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair

/-!
# R1Step2Probe980 — the real operator gate is uniform over `CompactLogTest`

R1 Step 2 (proof 980).  979 locked the object-layer SHAPE.  980 shows the operator
content is UNIFORM over `g`:

- `windowedBoundaryDetector_isSelfAdjoint g a c` (CompactRootHalfLinePair:1358) is
  uniform over `g`.
- `signedBoundaryOperator_isTraceClassAlong g a c …` (:1651) is uniform over `g`.
- The boundary/global Hilbert bases depend only on the fixed window `(a,c)`, NOT on
  `g` — so they exist (914c), and the trace-class theorem is test-invariant.

Consequence: `bumpPlateauTest` (the Wall-A positive-trace test) ALSO satisfies the
full operator `hilbertSchmidtGate` — one test, both halves.  This is the witness seed
for Step 3 (`SourceRouteTraceData`).  RH NOT claimed.  No sorry / no new axiom.
-/

set_option maxHeartbeats 800000

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace R1Step2Probe

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift
open ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
open ConnesWeilRH.Source.CC20Concrete

/-- The compact-log test carrier (same as 979). -/
abbrev Corpus : Type :=
  ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest

/-- HALF 1a (gate, self-adjoint) is uniform: for every test `g`, the windowed
detector at (1,1) is self-adjoint. -/
theorem r1_gate_selfAdjoint_uniform (g : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    IsSelfAdjoint (windowedBoundaryDetector g 1 1) :=
  windowedBoundaryDetector_isSelfAdjoint g 1 1

/-- HALF 1a at the bump test (instance). -/
theorem r1_gate_selfAdjoint_bump :
    IsSelfAdjoint (windowedBoundaryDetector
      ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest 1 1) :=
  r1_gate_selfAdjoint_uniform ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest

/-- HALF 1b (gate, trace-class) is uniform: for every test `g`, the signed boundary
operator at (1,1) is trace-class along four bases, and those bases exist.  This is
the reusable (test-parametric) version of 914c's `traceClass_witness_at_window`. -/
theorem r1_gate_traceClass_uniform (g : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest) :
    ∃ (nw : Set (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (pw : Set (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (ow : Set (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (gw : Set cc20GlobalLogCrossingL2)
      (negB : HilbertBasis (↥nw) ℂ (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (posB : HilbertBasis (↥pw) ℂ (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (outB : HilbertBasis (↥ow) ℂ (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (globB : HilbertBasis (↥gw) ℂ cc20GlobalLogCrossingL2),
    PositiveTrace.IsTraceClassAlong globB
      (signedBoundaryOperator g 1 1 negB posB outB globB) := by
  classical
  obtain ⟨nw, negB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1)))
  obtain ⟨pw, posB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1)))
  obtain ⟨ow, outB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1)))
  obtain ⟨gw, globB, _⟩ := exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
  refine ⟨nw, pw, ow, gw, negB, posB, outB, globB, ?_⟩
  exact signedBoundaryOperator_isTraceClassAlong g 1 1 negB posB outB globB

/-- HALF 1b at the bump test (instance).  This is `cyclicLegal` for the bump. -/
theorem r1_gate_traceClass_bump :
    ∃ (nw : Set (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (pw : Set (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (ow : Set (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (gw : Set cc20GlobalLogCrossingL2)
      (negB : HilbertBasis (↥nw) ℂ (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (posB : HilbertBasis (↥pw) ℂ (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (outB : HilbertBasis (↥ow) ℂ (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (globB : HilbertBasis (↥gw) ℂ cc20GlobalLogCrossingL2),
    PositiveTrace.IsTraceClassAlong globB
      (signedBoundaryOperator ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest
        1 1 negB posB outB globB) :=
  r1_gate_traceClass_uniform ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest

/-- The two halves: `bumpPlateauTest` carries the positivity (Wall-A), the channel's
self-adjointness (uniform), and basis-existence (914c).  This pins the operator
`hilbertSchmidtGate` conjuncts to the SAME test that has `positiveTrace > 0`. -/
theorem r1_one_test_both_halves :
    IsSelfAdjoint (windowedBoundaryDetector
      ConnesWeilRH.Source.Dev.Wall14Plateau.bumpPlateauTest 1 1) ∧
    ∃ B : Set cc20GlobalLogCrossingL2,
      Nonempty (HilbertBasis B ℂ cc20GlobalLogCrossingL2) := by
  constructor
  · exact r1_gate_selfAdjoint_bump
  · obtain ⟨gw, globB, _⟩ := exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
    exact ⟨gw, ⟨globB⟩⟩

end R1Step2Probe
end Dev
end Source
end ConnesWeilRH