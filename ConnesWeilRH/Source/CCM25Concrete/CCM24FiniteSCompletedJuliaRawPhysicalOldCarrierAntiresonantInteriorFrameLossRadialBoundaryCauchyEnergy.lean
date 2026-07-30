/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyDefect

/-!
# Cauchy-energy criterion for the radial boundary channel

Proof 692 makes the positive producer reduction exact at the named-basis
level.  For the bare radial crossing `C`, the following are equivalent:

```text
sum_i ‖C e_i‖² < ∞
    <=> IsTraceClassAlong (C† C).
```

When the condition holds, the ordinary diagonal trace of `C† C` is exactly
the squared crossing energy.  A supplied full-carrier boundary pair therefore
implies this energy condition through the Cauchy pair from Proof 691.  No
uniform-in-`S` bound or boundary-pair producer is constructed here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryCauchyEnergy

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialBoundaryCauchyDefect
open AntiresonantFrameLossRadialPhysicalOwnerCommonRootPairData
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## The positive-square criterion -/

/-- A Hilbert--Schmidt energy bound for the bare crossing gives named-basis
trace-class legality for its positive Cauchy defect. -/
theorem radialSoninBoundaryCauchyDefect_isTraceClassAlong_of_boundaryCrossing_summable
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S) := by
  let data : BasisHilbertSchmidtData sourceBasis :=
    { operator := radialSoninBoundaryCrossing p S
      summable_normSq := hcross }
  have hdata := data.positiveComposition_isTraceClassAlong
  simpa only [data, BasisHilbertSchmidtData.positiveComposition,
    radialSoninBoundaryCauchyDefect] using hdata

/-- Trace-class legality of the positive Cauchy defect forces the bare radial
crossing to have a summable squared norm on the same source basis. -/
theorem radialSoninBoundaryCrossing_summable_of_cauchyDefect_isTraceClassAlong
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hdefect : IsTraceClassAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S)) :
    Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2 := by
  apply summable_normSq_of_isTraceClassAlong_adjoint_comp_self
    sourceBasis (radialSoninBoundaryCrossing p S)
  simpa only [radialSoninBoundaryCauchyDefect] using hdefect

/-- The named-basis Hilbert--Schmidt condition and positive-defect trace
legality are equivalent for the bare radial crossing. -/
theorem radialSoninBoundaryCrossing_summable_iff_cauchyDefect_isTraceClassAlong
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) ↔
      IsTraceClassAlong sourceBasis
        (radialSoninBoundaryCauchyDefect p S) := by
  constructor
  · exact radialSoninBoundaryCauchyDefect_isTraceClassAlong_of_boundaryCrossing_summable
      sourceBasis p S
  · exact radialSoninBoundaryCrossing_summable_of_cauchyDefect_isTraceClassAlong
      sourceBasis p S

/-! ## Exact ordinary trace readout -/

/-- Under the positive-square energy premise, the ordinary defect trace is the
complexification of the crossing's squared norm sum. -/
theorem radialSoninBoundaryCauchyDefect_ordinaryTrace_eq_crossingEnergy
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis (radialSoninBoundaryCauchyDefect p S) =
      ((∑' i, ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) := by
  let data : BasisHilbertSchmidtData sourceBasis :=
    { operator := radialSoninBoundaryCrossing p S
      summable_normSq := hcross }
  have htrace := data.ordinaryTrace_positiveComposition
  simpa only [data, BasisHilbertSchmidtData.ordinaryTrace_positiveComposition,
    BasisHilbertSchmidtData.hsNormSq,
    BasisHilbertSchmidtData.positiveComposition,
    radialSoninBoundaryCauchyDefect] using htrace

/-! ## Conditional implication from the full boundary pair -/

/-- Any supplied full-carrier boundary pair forces the bare crossing to meet
the positive Cauchy-energy criterion.  The pair producer remains a premise. -/
theorem RadialSignedPhysicalOwnerPairData.boundaryCrossing_summable_of_pairData
    {p : CCM24VisiblePrime} {family : FinitePrimePowerFamily}
    {ι K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] {sourceBasis : HilbertBasis ι ℂ finiteSCarrier}
    (data : RadialSignedPhysicalOwnerPairData
      (K := K) (G := G) p family sourceBasis) :
    Summable fun i =>
      ‖radialSoninBoundaryCrossing p family.visiblePrimes
        (sourceBasis i)‖ ^ 2 := by
  exact radialSoninBoundaryCrossing_summable_of_cauchyDefect_isTraceClassAlong
    sourceBasis p family.visiblePrimes
    (by
      rw [← ConnesWeilRH.Source.CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect.RadialSignedPhysicalOwnerPairData.boundaryCauchyPair_traceProduct_eq_defect data]
      exact (ConnesWeilRH.Source.CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect.RadialSignedPhysicalOwnerPairData.boundaryCauchyPair data).traceProduct_isTraceClassAlong)

end AntiresonantFrameLossRadialBoundaryCauchyEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
