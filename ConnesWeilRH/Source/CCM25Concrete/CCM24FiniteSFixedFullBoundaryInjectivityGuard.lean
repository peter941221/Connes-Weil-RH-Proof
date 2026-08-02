/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryInjectivityBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalFamily

/-!
# Full-boundary injectivity guard

The selected owner stores support data for its root, but it does not store
root nondegeneracy or finite-window uniqueness.  This module records the
resulting degeneracy explicitly: a zero root gives a zero full boundary
factor, so the injectivity premise used by Proof 702 cannot be inferred from
the current owner fields when the source carrier is nontrivial.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedFullBoundaryInjectivityGuard

open MeasureTheory
open scoped ENNReal FourierTransform
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open SelectedCrossingOperatorBridge
open CCM24FiniteSGramResponse

theorem fullBoundaryRootFactor_eq_zero_of_test_eq_zero
    (g : CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (hzero : g.test = 0) :
    fullBoundaryRootFactor g a c = 0 := by
  have hsupp : Function.support g.test ⊆ Set.Icc a c := by
    intro x hx
    exfalso
    apply hx
    rw [hzero]
    rfl
  rw [fullBoundaryRootFactor_eq_globalConvolution g a c hsupp]
  have hinvolution : g.involution.test = 0 := by
    ext x
    rw [CompactLogConvolution.CompactLogTest.involution_apply, hzero]
    simp
  rw [hinvolution]
  apply ContinuousLinearMap.ext
  intro u
  have hfourierZero :
      FourierTransform.fourier (0 : SchwartzMap ℝ ℂ) = 0 := by
    exact map_zero _
  have hfourierLp :
      (FourierTransform.fourier (0 : SchwartzMap ℝ ℂ)).toLp ⊤ volume = 0 := by
    rw [hfourierZero]
    exact MemLp.toLp_zero _
  change globalL2ToKernelInterval (-c) (-a) 0
      (cc20GlobalLogConvolution (0 : SchwartzMap ℝ ℂ) u) = 0
  rw [cc20GlobalLogConvolution_apply, cc20FourierMultiplier_apply]
  have hmul :
      (0 : Lp ℂ ⊤ (volume : Measure ℝ)) • FourierTransform.fourier u = 0 := by
    rw [Lp.ext_iff]
    filter_upwards
      [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
        (0 : Lp ℂ ⊤ (volume : Measure ℝ)) (FourierTransform.fourier u),
       Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hmul hzero
    rw [hmul, hzero]
    simp
  rw [hfourierLp, hmul]
  simp

theorem sourceTest_ne_zero_of_finitePrimeTerm_ne_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0) :
    owner.sourceTest.test ≠ 0 := by
  intro hzero
  apply hterm
  have hsquare : owner.convolutionSquare.test = 0 := by
    ext x
    rw [SelectedWeilSquare.SelectedWeilSquareOwner.convolutionSquare_apply,
      hzero]
    simp
  rw [SelectedWeilSquare.SelectedWeilSquareOwner.finitePrimeTerm_eq,
    SelectedWeilSquare.SelectedWeilSquareOwner.primePowerValue_eq, hsquare]
  simp

theorem sourceTest_ne_zero_of_selectedVisiblePrime
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {p : CCM24VisiblePrime}
    (hp : p ∈
      CCM24FiniteSProjectionTrace.FinitePrimePowerFamily.visiblePrimes
        (CCM24FiniteSProjectionTrace.FinitePrimePowerFamily.ofSelectedOwner
          owner)) :
    owner.sourceTest.test ≠ 0 := by
  obtain ⟨m, hm⟩ :=
    CCM24FiniteSProjectionTrace.FinitePrimePowerFamily.exists_nonzero_primePower_of_mem_visiblePrimes_ofSelectedOwner
      owner hp
  exact sourceTest_ne_zero_of_finitePrimeTerm_ne_zero owner hm

theorem not_translated_fullBoundaryRootFactor_injective_of_sourceTest_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CC20Concrete.CCM24SoninScale) (a c : ℝ)
    (hzero : owner.sourceTest.test = 0)
    (hsource : ∃ y : sourceSoninCarrier lambda, y ≠ 0) :
    ¬ (∀ y : sourceSoninCarrier lambda,
      fullBoundaryRootFactor owner.sourceTest a c
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (sourceInclusion lambda y)) = 0 →
        y = 0) := by
  intro hinjective
  obtain ⟨y, hy⟩ := hsource
  apply hy
  apply hinjective y
  rw [fullBoundaryRootFactor_eq_zero_of_test_eq_zero
    owner.sourceTest a c hzero]
  rfl

end CCM24FiniteSFixedFullBoundaryInjectivityGuard
end CCM25Concrete
end Source
end ConnesWeilRH
