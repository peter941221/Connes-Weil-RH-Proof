/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary
import ConnesWeilRH.Dev.C1ProlateResponseTraceLegalityUnitScale
import ConnesWeilRH.Dev.C1ProlateRootCommutatorPerTermNuclearityGlue

/-!
# C1: discharging the S2 sandwiched nuclearity (record 1096)

Record 1095 named the canonical owed contract for S2 as per-term nuclearity of
the two WITH-C-dagger summands, and proved that S2 follows from it in one line.
This record DISCHARGES that contract down to a single primitive analytic
obligation about the prolate factor A (whose positive square is K_S):

```text
  targetProlateRemainderFactorHS : Summable fun i => ‖A e_i‖^2   (A in HS)
```

Both WITH-C-dagger summands are bounded sandwiches of K_S written as an HS-legs
trace product, so the committed `boundedSandwich_isTraceClassAlong` closes each
one from A in HS alone.  The convolution root C enters only as a bounded
dressing (never assumed Hilbert--Schmidt) - exactly the continuum-correct
posture that records 1094 and 1095 were driving at.

The remaining owed analytic core is now strictly narrower: prove A in HS on the
continuum carrier (= Tr K_S < inf, finite per family; record 1067 measured
Tr K_S growing but finite, 16 -> 34 over four octaves).

RH unclaimed; GATE 1 mainline untouched.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateRootCommutatorSandwichedNuclearityDischarge

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open C1ProlateResponseTraceLegalityUnitScale
open C1ProlateRootCommutatorPerTermNuclearityGlue

/-- THE primitive owed contract: the prolate factor A is Hilbert--Schmidt along
the global basis (= Tr K_S < inf, since K_S = A-dagger . A).  C does not appear. -/
noncomputable def targetProlateRemainderFactorHS
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily) : Prop :=
  Summable fun i =>
    ‖targetProlateRemainderFactor unitSoninScale family (globalBasis i)‖ ^ 2

/-- Pair data for K_S with both legs equal to the prolate factor A. -/
noncomputable def targetProlateRemainderHSPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hA : targetProlateRemainderFactorHS globalBasis family) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateRemainderFactor unitSoninScale family
  right := targetProlateRemainderFactor unitSoninScale family
  left_summable_normSq := hA
  right_summable_normSq := hA

/-- The pair-data trace product is exactly the prolate remainder K_S. -/
theorem targetProlateRemainderHSPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (family : FinitePrimePowerFamily)
    (hA : targetProlateRemainderFactorHS globalBasis family) :
    (targetProlateRemainderHSPairData globalBasis family hA).traceProduct =
      targetProlateRemainder unitSoninScale family := by
  unfold targetProlateRemainderHSPairData BasisHilbertSchmidtPairData.traceProduct
  exact targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family

/-- The first WITH-C-dagger summand is trace-legal from A in HS alone: it is the
bounded sandwich of K_S-as-HS-trace-product by P := C-dagger . C (left) and the
identity (right). -/
theorem targetProlateDetectorRootCommutatorLeftSummand_isTraceClassAlong
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hA : targetProlateRemainderFactorHS globalBasis family) :
    IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorLeftSummand owner family) := by
  let P : finiteSCarrier →L[ℂ] finiteSCarrier :=
    (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint ∘L
      CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  let PD := targetProlateRemainderHSPairData globalBasis family hA
  simpa only [targetProlateDetectorRootCommutatorLeftSummand, P, PD,
    targetProlateRemainderHSPairData_traceProduct_eq globalBasis family hA,
    identity, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.comp_assoc] using
    PD.boundedSandwich_isTraceClassAlong globalBasis P identity

/-- The second WITH-C-dagger summand is trace-legal from A in HS alone: it is the
bounded sandwich of K_S-as-HS-trace-product by C-dagger (left) and C (right). -/
theorem targetProlateDetectorRootCommutatorRightSummand_isTraceClassAlong
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hA : targetProlateRemainderFactorHS globalBasis family) :
    IsTraceClassAlong globalBasis
      (targetProlateDetectorRootCommutatorRightSummand owner family) := by
  let Croot := CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  let PD := targetProlateRemainderHSPairData globalBasis family hA
  have hsw : IsTraceClassAlong globalBasis
      (Croot.adjoint ∘L targetProlateRemainder unitSoninScale family ∘L Croot) := by
    rw [← targetProlateRemainderHSPairData_traceProduct_eq globalBasis family hA]
    simpa using PD.boundedSandwich_isTraceClassAlong globalBasis Croot.adjoint Croot
  simpa [targetProlateDetectorRootCommutatorRightSummand] using hsw

/-- DISCHARGE: the record-1095 sandwiched nuclearity contract follows from a
single primitive obligation, A in HS.  The convolution root C is never assumed
Hilbert--Schmidt - it enters only as bounded dressing. -/
theorem targetProlateDetectorRootCommutatorSandwichedTermNuclearity_of_FactorHS
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hA : targetProlateRemainderFactorHS globalBasis family) :
    targetProlateDetectorRootCommutatorSandwichedTermNuclearity
      globalBasis owner family := by
  constructor
  · exact targetProlateDetectorRootCommutatorLeftSummand_isTraceClassAlong
      globalBasis owner family hA
  · exact targetProlateDetectorRootCommutatorRightSummand_isTraceClassAlong
      globalBasis owner family hA

end C1ProlateRootCommutatorSandwichedNuclearityDischarge
end Source
end ConnesWeilRH
