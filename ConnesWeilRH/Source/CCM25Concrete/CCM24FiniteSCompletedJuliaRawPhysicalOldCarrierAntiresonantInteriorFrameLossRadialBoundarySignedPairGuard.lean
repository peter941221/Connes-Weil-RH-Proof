/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyPairProducer

/-!
# Signed-pair guard for the radial Cauchy producer

Proof 694 records the exact boundary between the positive Cauchy producer and
the signed radial boundary pair required by the physical owner. If

    C = radialSoninBoundaryCrossing p S

then the equal-leg producer from Proof 693 has trace product C† C, not C.
Consequently, using that producer as the signed boundary leg is equivalent to
the extra fixed-point identity C† C = C. Such an identity would also make C
self-adjoint, because C† C is self-adjoint.

The module does not claim that the fixed-point identity is false in the
abstract. It makes the missing source obligation explicit and prevents the
positive-defect witness from being silently consumed as a signed owner. The
route-level alternative remains a same-object signed scalar pairing, as
required by the compact-support cancellation guard.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundarySignedPairGuard

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialBoundaryCauchyDefect
open AntiresonantFrameLossRadialBoundaryCauchyEnergy
open AntiresonantFrameLossRadialBoundaryCauchyPairProducer
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Exact fixed-point condition -/

/-- The equal-leg Cauchy pair is a signed boundary pair exactly when its
positive Cauchy defect is the original crossing. -/
theorem radialSoninBoundaryCauchyPairData_traceProduct_eq_crossing_iff
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct =
        radialSoninBoundaryCrossing p S ↔
      radialSoninBoundaryCauchyDefect p S =
        radialSoninBoundaryCrossing p S := by
  rw [radialSoninBoundaryCauchyPairData_traceProduct_eq_defect]

/-- Any attempted signed readback from the equal-leg Cauchy pair forces the
nonlinear fixed-point identity C† C = C. -/
theorem radialSoninBoundaryCauchyPairData_fixedPoint_of_signed_readback
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2)
    (hsigned :
      (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct =
        radialSoninBoundaryCrossing p S) :
    (radialSoninBoundaryCrossing p S)† ∘L
        radialSoninBoundaryCrossing p S =
      radialSoninBoundaryCrossing p S := by
  calc
    (radialSoninBoundaryCrossing p S)† ∘L
          radialSoninBoundaryCrossing p S =
        radialSoninBoundaryCauchyDefect p S := rfl
    _ = (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct :=
      (radialSoninBoundaryCauchyPairData_traceProduct_eq_defect
        sourceBasis p S hcross).symm
    _ = radialSoninBoundaryCrossing p S := hsigned

/-- A signed readback from the equal-leg Cauchy pair necessarily makes the
bare boundary crossing self-adjoint. -/
theorem radialSoninBoundaryCauchyPairData_isSelfAdjoint_of_signed_readback
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2)
    (hsigned :
      (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct =
        radialSoninBoundaryCrossing p S) :
    IsSelfAdjoint (radialSoninBoundaryCrossing p S) := by
  have hdefect : radialSoninBoundaryCauchyDefect p S =
      radialSoninBoundaryCrossing p S := by
    calc
      radialSoninBoundaryCauchyDefect p S =
          (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct :=
        (radialSoninBoundaryCauchyPairData_traceProduct_eq_defect
          sourceBasis p S hcross).symm
      _ = radialSoninBoundaryCrossing p S := hsigned
  rw [← hdefect]
  exact
    (radialSoninBoundaryCauchyDefect_isPositive p S).isSelfAdjoint

/-! ## What the genuine source producer must still supply -/

/-- A genuine full-carrier signed boundary pair gives the positive energy
criterion, but the converse only gives the equal-leg Cauchy pair for C† C.
This theorem keeps the two readbacks visibly distinct. -/
theorem radialBoundaryEnergy_does_not_change_cauchy_readback
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct =
      radialSoninBoundaryCauchyDefect p S :=
  radialSoninBoundaryCauchyPairData_traceProduct_eq_defect
    sourceBasis p S hcross

end AntiresonantFrameLossRadialBoundarySignedPairGuard
end CCM25Concrete
end Source
end ConnesWeilRH
