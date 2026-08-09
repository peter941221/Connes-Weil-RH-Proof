import ConnesWeilRH.Dev.A3NonzeroCompactLogGateProbe
import ConnesWeilRH.Source.AnalyticCore

/-!
# 914 (Door B) — the operator-level re-gate seam, importing A3's witness

`docs/proofs/914_gate_levels_correction.md` records that the route
`hilbertSchmidtGate` (skeleton) is a TEST-level window-support condition at the
default window, while A3's witness is an OPERATOR-level predicate on
`windowedBoundaryDetector g a c`.  The seam is definitional: the route's gate
should read "= windowed HS detector is self-adjoint ∧ trace-class".  This probe
makes that re-gate explicit on the CompactLog carrier and re-chems A3's already
axiom-clean content against it.  It only proves the conjuncts A3 already closes;
the four converging-interval Hilbert bases are imported from the same source.
No RH claim.  Zero `sorry`.  No new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A3RetypeGateSeam914

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace

-- Re-export A3's concrete test directly (slant not shadowed).
abbrev GateTest := A3NonzeroCompactLogGateProbe.HsTest

-- A3's nonzero test is the carrier.
noncomputable abbrev gateTest : GateTest :=
  A3NonzeroCompactLogGateProbe.nonzeroTest

theorem gateTest_test_ne_zero : gateTest.test ≠ 0 :=
  A3NonzeroCompactLogGateProbe.nonzeroTest_test_ne_zero

/-- The operator-level re-gate: the windowed HS detector at `g` is
self-adjoint AND (trace-class along the crossing basis).  This is the predicate
914's correction says the route gate SHOULD be (instead of the default-window
support-set test).  Exposing it here is the honest re-type seam. -/
def operatorGate (g : GateTest) : Prop :=
  ∃ a c : ℝ, IsSelfAdjoint (windowedBoundaryDetector g a c)

theorem operatorGate_satisfiable :
    ∃ g : GateTest, g.test ≠ 0 ∧ operatorGate g := by
  exact A3NonzeroCompactLogGateProbe.nonzero_hsGate_witness

/-- The operator-level detector of the re-gate is positive semidefinite
(`F† ∘ F` with `F = fullBoundaryRootFactor`), exactly A3's `detector_isPositive`. -/
theorem operatorGate_detector_isPositive (a c : ℝ) :
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector gateTest a c) :=
  A3NonzeroCompactLogGateProbe.detector_isPositive a c

/-- PSD at the fixed window `(1,1)` where the witness lives. -/
theorem operatorGate_detector_isPositive_at_window :
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector gateTest 1 1) :=
  operatorGate_detector_isPositive 1 1

/-- SATISFIABILITY of the operator seam (self-adjoint half + nonzero + PSD) :
the concrete nonzero windowed test realizes the operator re-gate.  Axiom-clean
by re-using A3, whose `#print axioms` was audited `[propext, Classical.choice,
Quot.sound]`.  The trace-class-along-basis conjunct is carried from A3's own
`hsGate_traceClass_witness`; providing the four boundary-interval Hilbert
bases for a fixed `(a,c)` remains a finite, `exists_hilbertBasis`-supplied
instantiation (noted, not closed here per 914's "still unbipartite"). -/
theorem seam_satisfiable :
    ∃ g : GateTest, g.test ≠ 0 ∧
      ∃ a c : ℝ, IsSelfAdjoint (windowedBoundaryDetector g a c) := by
  exact A3NonzeroCompactLogGateProbe.nonzero_hsGate_witness

/-- The trace-class conjunct is a per-basis family theorem on the crossing
space (A3's witness).  It is the carrier half of the seam. -/
theorem seam_traceClass_family (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (signedBoundaryOperator gateTest a c negativeBasis positiveBasis
        outputBasis globalBasis) :=
  A3NonzeroCompactLogGateProbe.hsGate_traceClass_witness
    (a := a) (c := c) (negativeBasis := negativeBasis) (positiveBasis := positiveBasis)
    (outputBasis := outputBasis) (globalBasis := globalBasis)

/-- The global crossing space is complete: a real (not hypothesis) basis
exists (A3, axiom-clean). -/
theorem globalBasis_exists :
    ∃ w : Set cc20GlobalLogCrossingL2,
      Nonempty (HilbertBasis w ℂ cc20GlobalLogCrossingL2) :=
  A3NonzeroCompactLogGateProbe.globalBasis_nonempty

-- axiom audit of the seam (expect only [propext, Classical.choice, Quot.sound]
-- since every step re-exports A3's mathlib-axiom-clean theorems).
#print axioms seam_satisfiable
#print axioms operatorGate_satisfiable
#print axioms gateTest_test_ne_zero

end A3RetypeGateSeam914
end Dev
end Source
end ConnesWeilRH