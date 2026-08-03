/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov

/-!
# One-prime difference of the normalized causal Euler inverse

The normalized inverse of one Euler factor is a probability average of causal
translations.  Its difference from the identity has a sharper exact form: it
is one translation coboundary followed by the genuine Euler inverse.  Adding
one prime to a finite family therefore preserves the complete old prefix and
inserts this one signed coboundary on the right.

This is an operator identity only.  In particular, it does not bound the
coboundary, exchange renewal and Hilbert-basis sums, or prove the
lower-factor-square decay required by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovFirstDifference

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalMarkov

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The signed one-prime increment of the normalized causal inverse.  The
translation difference removes the identity component while the inverse
remains inside the same factor. -/
noncomputable def normalizedPrimeEulerInverseTranslationCoboundary
    (p : CCM24VisiblePrime) : Op :=
  (ccm24PrimeEulerCoefficient p : ℂ) •
    (((cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap -
      ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
      (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap)

/-- The normalized inverse of one Euler factor differs from the identity by
its exact signed translation coboundary. -/
theorem normalizedPrimeEulerInverse_sub_id_eq_translationCoboundary
    (p : CCM24VisiblePrime) :
    normalizedPrimeEulerInverse p - ContinuousLinearMap.id ℂ finiteSCarrier =
      normalizedPrimeEulerInverseTranslationCoboundary p := by
  apply ContinuousLinearMap.ext
  intro u
  let v := (ccm24PrimeEulerTransportEquiv p).symm u
  have hv : ccm24PrimeEulerTransportEquiv p v = u :=
    (ccm24PrimeEulerTransportEquiv p).apply_symm_apply u
  simp only [normalizedPrimeEulerInverse,
    normalizedPrimeEulerInverseTranslationCoboundary,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  change
    ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • v - u =
      (ccm24PrimeEulerCoefficient p : ℂ) •
        (cc20GlobalLogTranslation (-Real.log p) v - v)
  rw [← hv, ccm24PrimeEulerTransportEquiv_apply]
  rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
  abel

/-- Adding one prime to the normalized causal inverse keeps the complete old
prefix and appends exactly one signed translation coboundary. -/
theorem normalizedFiniteEulerInverseList_cons_sub_eq_prefixedTranslationCoboundary
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    normalizedFiniteEulerInverseList (p :: S) -
        normalizedFiniteEulerInverseList S =
      normalizedFiniteEulerInverseList S ∘L
        normalizedPrimeEulerInverseTranslationCoboundary p := by
  rw [normalizedFiniteEulerInverseList_cons]
  apply ContinuousLinearMap.ext
  intro u
  have hprime := congrFun (congrArg DFunLike.coe
    (normalizedPrimeEulerInverse_sub_id_eq_translationCoboundary p)) u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  have hprime' : normalizedPrimeEulerInverse p u - u =
      normalizedPrimeEulerInverseTranslationCoboundary p u := by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      using hprime
  rw [← map_sub, hprime']

end CCM24FiniteSCausalMarkovFirstDifference
end CCM25Concrete
end Source
end ConnesWeilRH
