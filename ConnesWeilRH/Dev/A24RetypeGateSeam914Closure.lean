import ConnesWeilRH.Dev.A24RetypeGateSeam914

/-!
# 914 (Door B, closure) — instantiate the four Hilbert bases: the operator
re-gate trace-class witness closes at the fixed window `(1,1)`

`A3RetypeGateSeam914.seam_traceClass_family` closes the trace-class conjunct at
any window given the four Hilbert bases (negative/positive/output boundary
interval `L^2` + the global crossing space).  It is parameterized over the
bases, so it does not yet assert a single *satisfiable* witness.  This module
supplies each basis from `exists_hilbertBasis` (complete complex `L^2`) and
closes `IsTraceClassAlong` at the fixed window `(1,1)`.  No new mathematics;
only the completeness witnesses.

No RH claim.  Zero `sorry`.  No new `axiom`.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A24RetypeGateSeam914Closure

open MeasureTheory
open scoped ComplexConjugate InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace

/-- The concrete nonzero windowed test (from the seam, abbreviated). -/
noncomputable abbrev gateTest : A3RetypeGateSeam914.GateTest :=
  A3RetypeGateSeam914.gateTest

theorem traceClass_witness_at_window :
    ∃ (nw : Set (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (pw : Set (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (ow : Set (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (gw : Set cc20GlobalLogCrossingL2)
      (negB : HilbertBasis (↥nw) ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1))))
      (posB : HilbertBasis (↥pw) ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1))))
      (outB : HilbertBasis (↥ow) ℂ
        (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1))))
      (globB : HilbertBasis (↥gw) ℂ cc20GlobalLogCrossingL2),
      PositiveTrace.IsTraceClassAlong globB
        (signedBoundaryOperator gateTest 1 1 negB posB outB globB) := by
  classical
  obtain ⟨_nw, _negB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval 1 1)))
  obtain ⟨_pw, _posB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval 1 1)))
  obtain ⟨_ow, _outB, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval 1 1)))
  obtain ⟨_gw, _globB, _⟩ := exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
  refine ⟨_nw, _pw, _ow, _gw, _negB, _posB, _outB, _globB, ?_⟩
  exact A3RetypeGateSeam914.seam_traceClass_family
    (a := 1) (c := 1)
    (negativeBasis := _negB) (positiveBasis := _posB)
    (outputBasis := _outB) (globalBasis := _globB)

-- axiom audit of the closure (expect only the library-level three; it is a
-- pure `exists_hilbertBasis` instantiation of the seam's axiom-clean theorem).
#print axioms traceClass_witness_at_window

end A24RetypeGateSeam914Closure
end Dev
end Source
end ConnesWeilRH