/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24RadialHalfLineAlignment

/-!
# C1 selected-detector semi-local Euler boundary

The selected finite-prime trace operator must arise from the actual finite-S
Euler geometry, rather than being appended as an unrelated arithmetic sum.
For one visible prime and one positive power, this file identifies the
unit-scale radial boundary crossing of the literal translation by `m * log p`
with the existing whole-line crossing used by the finite-prime trace bridge.

Consequently the existing trace readback for that crossing is also a trace
readback for a concrete Euler-boundary operator.  This is deliberately only a
one-prime / one-power brick: completing the finite-S finite-part requires the
interaction of all Euler factors with the semilocal Fourier/Sonin projection.
No residual vanishing, positivity, or RH-facing sign is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SelectedDetectorSemiLocalEulerBoundary

open CC20Concrete
open CCM25Concrete
open CCM25Concrete.SelectedCrossingOperatorBridge
open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The canonical semi-local cutoff is the unit radial scale. -/
noncomputable def unitSoninScale : CCM24SoninScale :=
  ⟨1, zero_lt_one⟩

/-- The positive logarithmic displacement attached to one prime power. -/
noncomputable def primePowerLogShift (p : CCM24VisiblePrime) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (p : ℝ)

/-- The actual radial boundary crossing caused by translating through the
unit-scale support cutoff.  This is the local term occurring in the Euler-log
expansion before its trace is taken. -/
noncomputable def radialPrimePowerBoundaryCrossing
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (m : ℕ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 -
      ccm24LogRadialSupportProjection lambda) ∘L
    (cc20GlobalLogTranslation (primePowerLogShift p m)).toContinuousLinearMap ∘L
      ccm24LogRadialSupportProjection lambda

/-- A radial boundary crossing is the translated fixed-boundary crossing.
This is the exact geometric source of the prime-power displacement; it does
not yet identify a finite-S Sonin trace. -/
theorem radialPrimePowerBoundaryCrossing_eq_translation_conjugation
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (m : ℕ) :
    radialPrimePowerBoundaryCrossing lambda p m =
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
        cc20SingleCrossingOperator (primePowerLogShift p m) ∘L
        (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap := by
  let shift := primePowerLogShift p m
  have hcomm : (cc20GlobalLogTranslation shift).toContinuousLinearMap ∘L
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap =
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
        (cc20GlobalLogTranslation shift).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro u
    exact cc20GlobalLogTranslation_commute shift (-Real.log lambda) u
  have hboundary := ccm24RadialOrientedCrossing_eq_translation_conjugation
    lambda (cc20GlobalLogTranslation shift).toContinuousLinearMap hcomm
  simpa only [radialPrimePowerBoundaryCrossing, shift,
    cc20SingleCrossingOperator, cc20NegativeHalfLineProjection] using hboundary

/-- Translation by zero is the identity as a bounded operator on the common
logarithmic carrier. -/
theorem globalLogTranslation_zero_operator :
    (cc20GlobalLogTranslation 0).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  filter_upwards [cc20GlobalLogTranslation_coeFn 0 u] with t htranslation
  simpa only [Function.comp_apply, add_zero] using htranslation

/-- At the canonical unit scale the actual Euler boundary crossing is exactly
the crossing operator already used by the finite-prime trace theorem. -/
theorem radialPrimePowerBoundaryCrossing_unitSoninScale
    (p : CCM24VisiblePrime) (m : ℕ) :
    radialPrimePowerBoundaryCrossing unitSoninScale p m =
      cc20SingleCrossingOperator (primePowerLogShift p m) := by
  rw [radialPrimePowerBoundaryCrossing_eq_translation_conjugation]
  change (cc20GlobalLogTranslation (-Real.log (1 : ℝ))).toContinuousLinearMap ∘L
      cc20SingleCrossingOperator (primePowerLogShift p m) ∘L
      (cc20GlobalLogTranslation (Real.log (1 : ℝ))).toContinuousLinearMap = _
  rw [Real.log_one, neg_zero, globalLogTranslation_zero_operator]
  simp

/-- The Euler-log weighted forward/adjoint boundary pair for one visible prime
power, defined from the semi-local radial boundary rather than directly from a
prime-term trace operator. -/
noncomputable def selectedEulerLogBoundaryPairOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (m : ℕ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (((1 / Real.sqrt ((p.1 ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) •
    (cc20GlobalConvolutionPositive owner.sourceTest.involution.test ∘L
        radialPrimePowerBoundaryCrossing unitSoninScale p m +
      (cc20GlobalConvolutionPositive owner.sourceTest.involution.test ∘L
        radialPrimePowerBoundaryCrossing unitSoninScale p m).adjoint)

/-- The boundary pair is definitionally the existing Euler-log crossing pair
after the geometric boundary identification. -/
theorem selectedEulerLogBoundaryPairOperator_eq_crossingOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (m : ℕ) :
    selectedEulerLogBoundaryPairOperator owner p m =
      eulerLogWeightedGlobalPairTraceOperator owner p.1 m := by
  rw [selectedEulerLogBoundaryPairOperator,
    radialPrimePowerBoundaryCrossing_unitSoninScale]
  rfl

/-- The one-prime Euler boundary pair is trace-class whenever the existing
compact crossing witnesses are available. -/
theorem selectedEulerLogBoundaryPairOperator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (p : CCM24VisiblePrime) {m : ℕ}
    (hp : p.1.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p.1 m) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (selectedEulerLogBoundaryPairOperator owner p m) := by
  rw [selectedEulerLogBoundaryPairOperator_eq_crossingOperator]
  exact eulerLogWeightedGlobalPairTraceOperator_isTraceClassAlong
    owner a c hp hsupp globalBasis basisData

/-- The trace of the Euler-boundary pair reads back to the corresponding
finite-prime Weil term.  The arithmetic term is therefore now attached to an
actual semi-local Euler boundary object. -/
theorem ordinaryTraceAlong_selectedEulerLogBoundaryPairOperator_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (p : CCM24VisiblePrime) {m : ℕ}
    (hp : p.1.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p.1 m) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (selectedEulerLogBoundaryPairOperator owner p m) =
      owner.finitePrimeTerm (p.1 ^ m) := by
  rw [selectedEulerLogBoundaryPairOperator_eq_crossingOperator]
  exact ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperator_eq_finitePrimeTerm_pow
    owner a c hp hm hsupp globalBasis basisData

/-! ### Finite visible Euler assemblies -/

/-- One positive power at one visible finite place.  The visible-place subtype
keeps the boundary operator tied to a concrete CCM24 finite-place list rather
than to an independently supplied natural-number prime. -/
abbrev VisiblePrimePower := CCM24VisiblePrime × ℕ

/-- A finite prime-power list owned by a concrete semi-local visible-place
list.  `visible` prevents the arithmetic trace terms from being appended from
outside the finite Euler geometry; `prime` and `exponent_ne_zero` are exactly
the hypotheses required by the existing crossing trace theorem. -/
structure VisiblePrimePowerTerms (S : List CCM24VisiblePrime) where
  terms : Finset VisiblePrimePower
  visible : ∀ pm ∈ terms, pm.1 ∈ S
  prime : ∀ pm ∈ terms, pm.1.1.Prime
  exponent_ne_zero : ∀ pm ∈ terms, pm.2 ≠ 0

/-- Forgetting the visible-place proof is injective, so finite visible
prime-power terms can be passed to the existing natural-number trace owner
without losing multiplicities or identifying distinct terms. -/
def visiblePrimePowerToNatPair : VisiblePrimePower ↪ ℕ × ℕ where
  toFun pm := (pm.1.1, pm.2)
  inj' x y h := by
    rcases x with ⟨p, m⟩
    rcases y with ⟨q, n⟩
    have hp : p.1 = q.1 := congrArg Prod.fst h
    have hm : m = n := congrArg Prod.snd h
    have hp' : p = q := Subtype.ext hp
    subst q
    subst n
    rfl

/-- The existing arithmetic trace owner sees the same finite terms after
their visible-place proofs are erased. -/
def VisiblePrimePowerTerms.natTerms {S : List CCM24VisiblePrime}
    (data : VisiblePrimePowerTerms S) : Finset (ℕ × ℕ) :=
  data.terms.map visiblePrimePowerToNatPair

/-- Every natural-number term exported from a visible Euler list remains a
prime term. -/
theorem VisiblePrimePowerTerms.natTerms_prime
    {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S) :
    ∀ pm ∈ data.natTerms, pm.1.Prime := by
  intro pm hpm
  rcases Finset.mem_map.1 hpm with ⟨visiblePm, hvisiblePm, hmap⟩
  rw [← hmap]
  exact data.prime visiblePm hvisiblePm

/-- Every exported term has a nonzero power, as required for its finite-prime
trace readback. -/
theorem VisiblePrimePowerTerms.natTerms_exponent_ne_zero
    {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S) :
    ∀ pm ∈ data.natTerms, pm.2 ≠ 0 := by
  intro pm hpm
  rcases Finset.mem_map.1 hpm with ⟨visiblePm, hvisiblePm, hmap⟩
  rw [← hmap]
  exact data.exponent_ne_zero visiblePm hvisiblePm

/-- Exported arithmetic terms genuinely come from one of the finite visible
places in `S`; this is the ownership witness that is absent from the old bare
arithmetic sum. -/
theorem VisiblePrimePowerTerms.natTerms_mem_visible
    {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S)
    {pm : ℕ × ℕ} (hpm : pm ∈ data.natTerms) :
    ∃ p : CCM24VisiblePrime, p ∈ S ∧ p.1 = pm.1 := by
  rcases Finset.mem_map.1 hpm with ⟨visiblePm, hvisiblePm, hmap⟩
  refine ⟨visiblePm.1, data.visible visiblePm hvisiblePm, ?_⟩
  exact congrArg Prod.fst hmap

/-- The finite Euler-boundary operator assembled from the literal radial
crossings at the chosen visible prime powers.  This is an operator before a
trace is taken; it intentionally makes no positivity or finite-part claim. -/
noncomputable def selectedEulerLogBoundaryPairOperatorSum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ∑ pm ∈ data.terms, selectedEulerLogBoundaryPairOperator owner pm.1 pm.2

/-- The finite visible Euler-boundary assembly is exactly the already-audited
finite crossing-operator sum after erasing only the visible-place proof. -/
theorem selectedEulerLogBoundaryPairOperatorSum_eq_crossingOperatorSum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S) :
    selectedEulerLogBoundaryPairOperatorSum owner data =
      eulerLogWeightedGlobalPairTraceOperatorSum owner data.natTerms := by
  rw [selectedEulerLogBoundaryPairOperatorSum,
    eulerLogWeightedGlobalPairTraceOperatorSum, VisiblePrimePowerTerms.natTerms,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro pm hpm
  exact selectedEulerLogBoundaryPairOperator_eq_crossingOperator owner pm.1 pm.2

/-- The finite visible Euler-boundary assembly is trace-class whenever the
existing compact crossing basis data are available term-by-term. -/
theorem selectedEulerLogBoundaryPairOperatorSum_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ data.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1.1 pm.1.2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (selectedEulerLogBoundaryPairOperatorSum owner data) := by
  rw [selectedEulerLogBoundaryPairOperatorSum]
  apply CC20Concrete.PositiveTrace.isTraceClassAlong_finset_sum globalBasis data.terms
  intro pm hpm
  exact selectedEulerLogBoundaryPairOperator_isTraceClassAlong
    owner a c pm.1 (data.prime pm hpm) hsupp globalBasis (basisData ⟨pm, hpm⟩)

/-- The trace of the finite visible Euler-boundary assembly is precisely the
finite sum of the corresponding Weil prime-power terms.  Thus the complete
finite arithmetic side is now a sum of literal semi-local boundary crossings,
not a separately appended operator. -/
theorem ordinaryTraceAlong_selectedEulerLogBoundaryPairOperatorSum_eq_finitePrimeTerm_sum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {S : List CCM24VisiblePrime} (data : VisiblePrimePowerTerms S)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ data.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1.1 pm.1.2) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (selectedEulerLogBoundaryPairOperatorSum owner data) =
      ∑ pm ∈ data.terms, owner.finitePrimeTerm (pm.1.1 ^ pm.2) := by
  rw [selectedEulerLogBoundaryPairOperatorSum]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_finset_sum globalBasis data.terms _]
  · apply Finset.sum_congr rfl
    intro pm hpm
    exact ordinaryTraceAlong_selectedEulerLogBoundaryPairOperator_eq_finitePrimeTerm_pow
      owner a c pm.1 (data.prime pm hpm) (data.exponent_ne_zero pm hpm)
        hsupp globalBasis (basisData ⟨pm, hpm⟩)
  · intro pm hpm
    exact selectedEulerLogBoundaryPairOperator_isTraceClassAlong
      owner a c pm.1 (data.prime pm hpm) hsupp globalBasis (basisData ⟨pm, hpm⟩)

end
end C1SelectedDetectorSemiLocalEulerBoundary
end Source
end ConnesWeilRH
