/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialReduction

/-!
# Signed radial boundary split of the frame-loss commutator

Proof 672 reduces the relative commutator to the upper radial carrier.  This
module makes the remaining source object explicit.  With `E` the genuine
radial-support projection, `P_S` the actual suffix Sonin projection, and `U_p`
the positive prime-log translation, the exact signed identity is

```text
[U_p, P_S] = [E U_p E, P_S] + (I - E) U_p P_S.
```

The first term is the compressed interior commutator.  The second is one
radial boundary crossing of the same orientation as the existing radial split.
No term is estimated or discarded here; a support estimate for arbitrary
`P_S` inputs remains a separate source obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundarySplit

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossCommutator
open AntiresonantFrameLossRadialReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## The two signed channels -/

/-- The positive translation compressed to the genuine upper radial carrier. -/
noncomputable def radialCompressedPositiveTranslation
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection unitSoninScale ∘L
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
      radialSupportProjection unitSoninScale

/-- The commutator that remains entirely inside the upper radial carrier. -/
noncomputable def radialInteriorSoninCommutator
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  cc20Commutator (radialCompressedPositiveTranslation p)
    (newSuffixRangeProjection unitSoninScale S)

/-- The single positive-translation crossing emitted from the Sonin range. -/
noncomputable def radialSoninBoundaryCrossing
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialComplement unitSoninScale ∘L
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap ∘L
      newSuffixRangeProjection unitSoninScale S

/-! ## Exact signed identity -/

/-- The actual translation/Sonin commutator is exactly the sum of its
compressed interior commutator and one radial boundary crossing. -/
theorem suffixPrimeTranslationProjectionCommutator_eq_radialInterior_add_boundary
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixPrimeTranslationProjectionCommutator p S =
      radialInteriorSoninCommutator p S +
        radialSoninBoundaryCrossing p S := by
  apply ContinuousLinearMap.ext
  intro u
  have hPE := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_radialSupportProjection
      unitSoninScale S) u
  have hEP := DFunLike.congr_fun
    (radialSupportProjection_comp_newSuffixRangeProjection
      unitSoninScale S) u
  have hPEU := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_radialSupportProjection
      unitSoninScale S)
      ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
        (radialSupportProjection unitSoninScale u))
  have hPUF := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_positiveTranslation_comp_radialComplement_eq_zero
      unitSoninScale p S) u
  simp only [ContinuousLinearMap.comp_apply] at hPE hEP hPEU
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearMap.zero_apply] at hPUF
  simp only [suffixPrimeTranslationProjectionCommutator,
    primePositiveLogTranslationOperator, radialInteriorSoninCommutator,
    radialCompressedPositiveTranslation, radialSoninBoundaryCrossing,
    cc20Commutator, radialComplement,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] at ⊢
  have hPU :
      newSuffixRangeProjection unitSoninScale S
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u) =
        newSuffixRangeProjection unitSoninScale S
          ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
            (radialSupportProjection unitSoninScale u)) := by
    exact sub_eq_zero.mp hPUF
  rw [hEP, hPEU, hPU]
  abel

end AntiresonantFrameLossRadialBoundarySplit
end CCM25Concrete
end Source
end ConnesWeilRH
