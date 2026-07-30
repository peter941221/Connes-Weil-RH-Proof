/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCutoffTraceAnomaly

/-!
# Compact-support radial-cell cutoff obstruction

Compact support cuts off the scalar autocorrelation sampled by a sufficiently
large translation.  It does not make the corresponding completed crossing
operator zero.  This distinction matters for Proof 641: its finite radial
column is an operator-valued prefix, while the complete swapped cofactor is
also an operator, not merely its trace.

This module records two exact guards.

* On the actual CCM24 objects, one tail vector which is invisible to the first
  `N` radial cells but visible to the complete coupled cofactor rules out every
  bounded readout through that finite column.
* A finite matrix model has disjoint singleton input/output supports and zero
  trace, while the whole completed crossing remains nonzero and cannot factor
  through any coordinate prefix which omits its input cell.

The matrix crossing is kept whole.  It is not a norm estimate of separate
outer, reflected, second-support, or prolate branches.  The model proves that
compact support alone cannot supply an operator-level finite-cell cutoff; it
does not prove that the actual coupled CCM24 cofactor has a tail witness.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorCompactSupportCellCutoffObstruction

open scoped Matrix

open CC20Concrete
open CCM24FiniteSCutoffTraceAnomaly
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

/-! ## Actual complete-cofactor obstruction -/

/-- A single tail witness rules out every bounded factorization of the actual
complete coupled cofactor through Proof 639's first `N` radial cells.  No
physical branch of the cofactor is expanded in this statement. -/
theorem not_nonempty_finiteRadialReadoutData_of_tail_witness
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat}
    (x : sourceSoninCarrier lambda)
    (hcolumn :
      finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0)
    (hcofactor :
      suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x ≠ 0)
    (bound : Real) :
    ¬ Nonempty
      (SuffixSwappedLocalCofactorFiniteRadialReadoutData
        owner lambda p S N bound) := by
  rintro ⟨data⟩
  exact hcofactor
    (completeSwappedLocalCofactor_eq_zero_of_finiteRadialColumn_eq_zero
      data x hcolumn)

/-! ## Support-separated completed-crossing model -/

variable {X : Type*} [DecidableEq X]

/-- One complete crossing from `input` to `output`.  Its matrix support is the
single pair `(output,input)`. -/
def supportSeparatedCrossing (output input : X) : Matrix X X Complex :=
  fun i j => if i = output ∧ j = input then 1 else 0

@[simp]
theorem supportSeparatedCrossing_apply
    (output input i j : X) :
    supportSeparatedCrossing output input i j =
      if i = output ∧ j = input then 1 else 0 :=
  rfl

/-- Trace cancellation does not make the completed crossing operator zero. -/
theorem supportSeparatedCrossing_ne_zero (output input : X) :
    supportSeparatedCrossing output input ≠ 0 := by
  intro hzero
  have hentry := congrArg (fun matrix : Matrix X X Complex =>
    matrix output input) hzero
  simp [supportSeparatedCrossing] at hentry

variable [Fintype X]

/-- The crossing is exactly supported between the two singleton coordinate
windows.  This is the finite model of a root-completed translated crossing. -/
theorem singletonProjection_mul_crossing_mul_singletonProjection
    (output input : X) :
    coordinateProjection {output} * supportSeparatedCrossing output input *
        coordinateProjection {input} =
      supportSeparatedCrossing output input := by
  ext i j
  by_cases hi : i = output <;> by_cases hj : j = input <;>
    simp [coordinateProjection, supportSeparatedCrossing,
      Matrix.mul_diagonal, Matrix.diagonal_mul, hi, hj]

/-- Disjoint input and output supports kill the diagonal trace exactly. -/
theorem trace_supportSeparatedCrossing_eq_zero
    {output input : X} (hne : output ≠ input) :
    Matrix.trace (supportSeparatedCrossing output input) = 0 := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  change (if i = output ∧ i = input then 1 else 0) = 0
  split_ifs with h
  · exact (hne (h.1.symm.trans h.2)).elim
  · rfl

/-- A coordinate prefix which omits the input cell cannot own the complete
crossing through any matrix readout.  This is the finite-dimensional kernel
obstruction corresponding to Proof 641's Douglas condition. -/
theorem supportSeparatedCrossing_not_factor_through_coordinateProjection
    (output input : X) (support : Finset X) (hinput : input ∉ support) :
    ¬ (Exists fun readout : Matrix X X Complex =>
      readout * coordinateProjection support =
        supportSeparatedCrossing output input) := by
  rintro ⟨readout, hfactor⟩
  have hentry := congrArg (fun matrix : Matrix X X Complex =>
    matrix output input) hfactor
  simp [coordinateProjection, Matrix.mul_diagonal,
    supportSeparatedCrossing, hinput] at hentry

/-- Compact support can therefore give a zero scalar trace without either an
operator cutoff or a finite-prefix factorization. -/
theorem separated_singleton_support_trace_zero_but_no_operator_cutoff
    {output input : X} (hne : output ≠ input) :
    Matrix.trace (supportSeparatedCrossing output input) = 0 ∧
      supportSeparatedCrossing output input ≠ 0 :=
  ⟨trace_supportSeparatedCrossing_eq_zero hne,
    supportSeparatedCrossing_ne_zero output input⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorCompactSupportCellCutoffObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
