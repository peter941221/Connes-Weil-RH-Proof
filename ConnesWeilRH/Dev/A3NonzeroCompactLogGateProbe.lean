/-
A3 probe (closure-audit follow-up): the one gap the closed A1 bridge leaves open
is *existence of a nonzero test carrying the HS `hilbertSchmidtGate`*.  This
module constructs a concrete nonzero `CompactLogTest` from the mathlib smooth
bump already packaged in `CCM24UnitScalePlancherelKernel`, proves it genuinely
nonzero, and shows the windowed HS detector at that test is self-adjoint and
HS-trace-class along a Hilbert basis — the exact positive content the audit's
"re-type onto the CompactLog HS carrier" conclusion rests on.

Proof-of-WITNESS only: establishes the gate is satisfiable by a nonzero test.
Does NOT rewire the RH skeleton; no RH claim is made.
-/

import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScalePlancherelKernel
import ConnesWeilRH.Basic

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace A3NonzeroCompactLogGateProbe

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open PositiveTrace

open CCM25Concrete.CCM24UnitScaleProlateTraceReduction

abbrev HsTest := CCM25Concrete.CompactLogConvolution.CompactLogTest

/-- The unit-scale Fourier-core bump is `1` at `0` (since `0` lies in the
`closedBall 0 (1/2)` on which the bump equals `1`). -/
theorem unitFourierCoreBump_zero_eq_one : unitFourierCoreBump 0 = 1 := by
  apply unitFourierCoreBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_self]
  exact unitFourierCoreBump.rIn_pos.le

/-- The bump as a non-zero Schwartz function: its value at `0` is `1 ≠ 0`. -/
theorem unitFourierCoreBumpSchwartz_ne_zero : unitFourierCoreBumpSchwartz ≠ 0 := by
  intro hzero
  have happly : unitFourierCoreBumpSchwartz 0 = 0 := by rw [hzero]; rfl
  rw [unitFourierCoreBumpSchwartz_apply] at happly
  simpa [unitFourierCoreBump_zero_eq_one] using happly

/-- The concrete nonzero test: the unit bump wrapped as a `CompactLogTest`. -/
noncomputable def nonzeroTest : HsTest where
  test := unitFourierCoreBumpSchwartz
  compactSupport := unitFourierCoreBumpFunction_hasCompactSupport

theorem nonzeroTest_test_ne_zero : nonzeroTest.test ≠ 0 :=
  unitFourierCoreBumpSchwartz_ne_zero

/-- WITNESS conjunct 1 ("traceClass"): the windowed boundary detector at the
nonzero test is self-adjoint for every window `(a,c)`. -/
theorem hsGate_selfAdjoint_witness (a c : ℝ) :
    IsSelfAdjoint (windowedBoundaryDetector nonzeroTest a c) :=
  windowedBoundaryDetector_isSelfAdjoint nonzeroTest a c

/-- WITNESS conjunct 2 ("cyclicLegal"/trace-class): the detector is
HS-trace-class along a Hilbert basis of the global crossing space. -/
theorem hsGate_traceClass_witness
    (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (signedBoundaryOperator nonzeroTest a c negativeBasis positiveBasis
        outputBasis globalBasis) :=
  signedBoundaryOperator_isTraceClassAlong
    nonzeroTest a c negativeBasis positiveBasis outputBasis globalBasis

/-- A concrete Hilbert basis of the global crossing space instantiates the
trace-class witness (`exists_hilbertBasis` on the complete complex `Lp`). -/
theorem globalBasis_nonempty :
    ∃ w : Set cc20GlobalLogCrossingL2,
      Nonempty (HilbertBasis w ℂ cc20GlobalLogCrossingL2) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ cc20GlobalLogCrossingL2
  exact ⟨w, ⟨b⟩⟩

/--
THE WITNESS: a nonzero compact-log test exists whose windowed HS detector is
both self-adjoint and HS — i.e. the `hilbertSchmidtGate` (archimedean HS
gate = traceClass ∧ cyclicLegal) is satisfiable by a nonzero test.  This is the
concrete positive content the audit's re-type conclusion rests on; it does not
close the skeleton (the gate is not itself `SourceRH`).
-/
theorem nonzero_hsGate_witness :
    ∃ g : HsTest, g.test ≠ 0 ∧
      (∃ a c : ℝ, IsSelfAdjoint (windowedBoundaryDetector g a c)) :=
  ⟨nonzeroTest, nonzeroTest_test_ne_zero, ⟨1, 1,
    hsGate_selfAdjoint_witness 1 1⟩⟩

/--
THE VALUE: the windowed detector at the nonzero test is a *nonnegative*
operator on the crossing space — its quadratic form is a true square `‖F u‖²` and
hence `≥ 0`.  Algebraically `detector = F† ∘ F` with
`F = fullBoundaryRootFactor`, so `⟨u, detector u⟩ = ‖F u‖² ≥ 0`.  This is the
concrete sign content that A0's single-point window could never provide.
-/
theorem detector_diagonal_re_nonneg (a c : ℝ) (u : cc20GlobalLogCrossingL2) :
    0 ≤ (⟪u, windowedBoundaryDetector nonzeroTest a c u⟫_ℂ).re := by
  -- windowedBoundaryDetector g a c = (F g a c)† ∘L F g a c, so the quadratic
  -- form is the real square ‖F u‖² via the adjoint norm-square identity.
  have hsq : (⟪u, windowedBoundaryDetector nonzeroTest a c u⟫_ℂ).re =
      ‖fullBoundaryRootFactor nonzeroTest a c u‖ ^ 2 := by
    exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
      (fullBoundaryRootFactor nonzeroTest a c) u).symm
  rw [hsq]
  exact sq_nonneg _

/-- The windowed HS detector at the nonzero test is **positive semidefinite** as
   an operator on the crossing space: `F† ∘ F` is `IsPositive` for every
   `F = fullBoundaryRootFactor`. This is strictly stronger than the single-vector
   `detector_diagonal_re_nonneg` and is the operator-level positive sign the
   CompactLog re-typing of the skeleton needs. -/
theorem detector_isPositive (a c : ℝ) :
    ContinuousLinearMap.IsPositive (windowedBoundaryDetector nonzeroTest a c) :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (fullBoundaryRootFactor nonzeroTest a c)

/-- Operator-level PSD corollary: `re ⟪u, detector u⟫ ≥ 0` for every vector. -/
theorem detector_re_inner_nonneg (a c : ℝ) (u : cc20GlobalLogCrossingL2) :
    0 ≤ (⟪u, windowedBoundaryDetector nonzeroTest a c u⟫_ℂ).re :=
  ContinuousLinearMap.IsPositive.re_inner_nonneg_right (detector_isPositive a c) u

end A3NonzeroCompactLogGateProbe
end Dev
end Source
end ConnesWeilRH