/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRecovery

/-!
# Route-uniform domination for the renewed antiresonant channel

Proof 627 identifies the renewed single channel equivalent to the packed
physical Bone 1 factor.  This module records the exact route-uniform analytic
statement left after that reduction:

```text
‖signedCompressedInteriorOwner_(p,S) x‖²
  ≤ C² ‖L_p† N_p† newFrame_(p,S) x‖²
```

for one finite `C`, every route-valid adjacent pair `(p,S)`, and every source
vector `x`.  The statement is equivalent, after existentially quantifying the
bound, to the route-uniform physical-factor producer.

The actual interior owner has the exact normal form

```text
A_(p,S) = T_(p,S)^dagger K_(p,S),

K_(p,S)
  = R_(p,S)^dagger B_S - B_(p::S) R_(p,S)^dagger.
```

This module also proves that the renewed domination is equivalent, up to the
fixed recovery cost `8`, to the same quotient estimate for the complete
reverse-intertwining defect `K_(p,S)`.  The signed adjacent responses remain
inside `K_(p,S)`.  Route validity only restricts the quantifier domain; it
does not imply covariance or cancellation.  No closed-range, inverse-Gram,
spectral-gap, or independent operator-norm premise is added.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance routeDominationSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The exact route-uniform analytic bottom -/

/-- One relative-energy bound for every route-valid renewed channel. -/
def SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S →
        ∀ x : sourceSoninCarrier lambda,
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
            bound ^ 2 *
              ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2

/-! ## Complete reverse-intertwining quotient -/

/-- The source-specific quotient estimate for the complete signed adjacent
boundary response.  This is stronger than a standalone operator-norm bound:
the numerator and denominator are evaluated on the same source vector. -/
def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformReverseIntertwiningDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S →
        ∀ x : sourceSoninCarrier lambda,
          ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
              owner lambda p S x‖ ^ 2 ≤
            bound ^ 2 *
              ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2

/-- The left transition is contractive, so the complete reverse-intertwining
defect dominates the interior owner pointwise without changing the bound. -/
theorem norm_signedCompressedInteriorOwner_apply_le_reverseIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖signedCompressedInteriorOwner owner lambda p S x‖ ≤
      ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S x‖ := by
  have howner := DFunLike.congr_fun
    (signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect
      owner lambda p S) x
  simp only [ContinuousLinearMap.comp_apply] at howner
  rw [howner]
  calc
    ‖((suffixEulerFrameTransition lambda p S)†)
        (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S x)‖ ≤
        ‖(suffixEulerFrameTransition lambda p S)†‖ *
          ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S x‖ :=
      ((suffixEulerFrameTransition lambda p S)†).le_opNorm _
    _ = ‖suffixEulerFrameTransition lambda p S‖ *
          ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S x‖ := by
      exact congrArg
        (fun value : ℝ => value *
          ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S x‖)
        (ContinuousLinearMap.adjoint.norm_map
          (suffixEulerFrameTransition lambda p S))
    _ ≤ 1 *
          ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S x‖ := by
      exact mul_le_mul_of_nonneg_right
        (suffixEulerFrameTransition_norm_le_one lambda p S) (norm_nonneg _)
    _ = ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S x‖ := by rw [one_mul]

/-- The paired reverse transition reconstructs the complete inner defect.
The only loss is the uniform lower bound `rho_p >= 1/8`. -/
theorem norm_reverseIntertwiningDefect_apply_le_eight_mul_interior
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S x‖ ≤
      8 * ‖signedCompressedInteriorOwner owner lambda p S x‖ := by
  let defect :=
    suffixActualBandCompleteBoundaryReverseIntertwiningDefect
      owner lambda p S
  have howner := DFunLike.congr_fun
    (signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect
      owner lambda p S) x
  have hpair := DFunLike.congr_fun
    (suffixEulerFrameReverseTransitionAdjoint_comp_transitionAdjoint_eq_scalar
      lambda p S) (defect x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    at howner hpair
  have hreconstruct :
      ((suffixEulerFrameReverseTransition lambda p S)†)
          (signedCompressedInteriorOwner owner lambda p S x) =
        (primeSchurMarkovScalar p : ℂ) • defect x := by
    rw [howner]
    exact hpair
  have hlower :
      (1 / 8 : ℝ) * ‖defect x‖ ≤
        ‖signedCompressedInteriorOwner owner lambda p S x‖ := by
    calc
      (1 / 8 : ℝ) * ‖defect x‖ ≤
          primeSchurMarkovScalar p * ‖defect x‖ :=
        mul_le_mul_of_nonneg_right
          (primeSchurMarkovScalar_ge_one_eighth p) (norm_nonneg _)
      _ = ‖(primeSchurMarkovScalar p : ℂ) • defect x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (primeSchurMarkovScalar_pos p)]
      _ = ‖((suffixEulerFrameReverseTransition lambda p S)†)
            (signedCompressedInteriorOwner owner lambda p S x)‖ := by
        rw [hreconstruct]
      _ ≤ ‖(suffixEulerFrameReverseTransition lambda p S)†‖ *
            ‖signedCompressedInteriorOwner owner lambda p S x‖ :=
        ((suffixEulerFrameReverseTransition lambda p S)†).le_opNorm _
      _ = ‖suffixEulerFrameReverseTransition lambda p S‖ *
            ‖signedCompressedInteriorOwner owner lambda p S x‖ := by
        exact congrArg
          (fun value : ℝ => value *
            ‖signedCompressedInteriorOwner owner lambda p S x‖)
          (ContinuousLinearMap.adjoint.norm_map
            (suffixEulerFrameReverseTransition lambda p S))
      _ ≤ 1 * ‖signedCompressedInteriorOwner owner lambda p S x‖ := by
        exact mul_le_mul_of_nonneg_right
          (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
          (norm_nonneg _)
      _ = ‖signedCompressedInteriorOwner owner lambda p S x‖ := by
        rw [one_mul]
  dsimp only [defect] at hlower ⊢
  nlinarith [norm_nonneg
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
      owner lambda p S x),
    norm_nonneg (signedCompressedInteriorOwner owner lambda p S x)]

/-- A quotient estimate for the complete adjacent defect proves the renewed
Bone 1 domination with the same constant. -/
theorem routeUniformRenewedAmbientDomination_of_reverseIntertwiningDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformReverseIntertwiningDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
      owner lambda bound := by
  refine ⟨hdom.1, ?_⟩
  intro p S hvalid x
  have hnorm :=
    norm_signedCompressedInteriorOwner_apply_le_reverseIntertwiningDefect
      owner lambda p S x
  have hsquare :
      ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  exact hsquare.trans (hdom.2 p S hvalid x)

/-- Conversely, the interior domination recovers the complete adjacent
defect with the fixed transition cost `8`. -/
theorem reverseIntertwiningDomination_of_routeUniformRenewedAmbientDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformReverseIntertwiningDomination
      owner lambda (8 * bound) := by
  refine ⟨mul_nonneg (by norm_num) hdom.1, ?_⟩
  intro p S hvalid x
  have hnorm :=
    norm_reverseIntertwiningDefect_apply_le_eight_mul_interior
      owner lambda p S x
  have hsquare :
      ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S x‖ ^ 2 ≤
        (8 * ‖signedCompressedInteriorOwner owner lambda p S x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _))).2 hnorm
  calc
    ‖suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S x‖ ^ 2 ≤
        (8 * ‖signedCompressedInteriorOwner owner lambda p S x‖) ^ 2 :=
      hsquare
    _ = 64 * ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 := by
      ring
    _ ≤ 64 * (bound ^ 2 *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hdom.2 p S hvalid x) (by norm_num)
    _ = (8 * bound) ^ 2 *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2 := by
      ring

/-- Existence of a finite renewed quotient is exactly existence of a finite
quotient for the complete reverse-intertwining owner.  The witnesses differ
by at most the fixed factor `8`. -/
theorem
    exists_reverseIntertwiningDomination_iff_exists_renewedAmbientDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ,
        SuffixRawOldCarrierAntiresonantInteriorRouteUniformReverseIntertwiningDomination
          owner lambda bound) ↔
      ∃ bound : ℝ,
        SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
          owner lambda bound := by
  constructor
  · rintro ⟨bound, hdom⟩
    exact ⟨bound,
      routeUniformRenewedAmbientDomination_of_reverseIntertwiningDomination
        hdom⟩
  · rintro ⟨bound, hdom⟩
    exact ⟨8 * bound,
      reverseIntertwiningDomination_of_routeUniformRenewedAmbientDomination
        hdom⟩

/-- A route-uniform single-channel factor supplies the exact relative-energy
domination with the same bound. -/
theorem routeUniformRenewedAmbientDomination_of_singleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
      owner lambda bound := by
  refine ⟨data.bound_nonneg, ?_⟩
  intro p S hvalid x
  exact
    (renewedAmbientDomination_of_readoutData
      ((data.factor p S hvalid).toRenewedAmbientReadoutData)).2 x

/-- Douglas factorization constructs a route-uniform single-channel producer
from the exact relative-energy domination, without changing the bound. -/
noncomputable def routeUniformSingleChannelFactorDataOfDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
      owner lambda bound :=
  { bound_nonneg := hdom.1
    factor := fun p S hvalid =>
      (renewedAmbientReadoutDataOfDomination
        ⟨hdom.1, hdom.2 p S hvalid⟩).toSingleChannelFactorData }

/-- At a fixed bound, the route-uniform single-channel producer is exactly
the route-uniform relative-energy domination. -/
theorem exists_routeUniformSingleChannelFactor_iff_domination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
          owner lambda bound) ↔
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound := by
  constructor
  · rintro ⟨data⟩
    exact routeUniformRenewedAmbientDomination_of_singleChannelFactorData data
  · intro hdom
    exact ⟨routeUniformSingleChannelFactorDataOfDomination hdom⟩

/-! ## Equivalence with the Proof 625 producer -/

/-- Existence of some finite route-uniform Proof 625 physical bound is
equivalent to existence of some finite bound for the renewed relative-energy
inequality.  The numerical bounds are not claimed to be identical: packing a
single channel has the proved one-way cost `17`. -/
theorem
    exists_routeUniformPhysicalFactor_iff_exists_renewedAmbientDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
          owner lambda bound)) ↔
      ∃ bound : ℝ,
        SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
          owner lambda bound := by
  constructor
  · intro hphysical
    obtain ⟨bound, hsingle⟩ :=
      (exists_routeUniformSingleChannelFactor_iff_exists_routeUniformPhysicalFactor
        owner lambda).mpr hphysical
    exact ⟨bound,
      (exists_routeUniformSingleChannelFactor_iff_domination
        owner lambda bound).mp hsingle⟩
  · rintro ⟨bound, hdom⟩
    apply
      (exists_routeUniformSingleChannelFactor_iff_exists_routeUniformPhysicalFactor
        owner lambda).mp
    exact ⟨bound,
      (exists_routeUniformSingleChannelFactor_iff_domination
        owner lambda bound).mpr hdom⟩

/-! ## Actual finite-family specialization -/

/-- The route-uniform inequality specializes to every genuine suffix of a
finite prime-power family. -/
theorem routeUniformRenewedAmbientDomination_forFamilySuffix
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound)
    (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hsuffix : p :: S <:+ family.visiblePrimes) :
    SuffixRawOldCarrierAntiresonantInteriorRenewedAmbientDomination
      owner lambda p S bound :=
  ⟨hdom.1, hdom.2 p S
    (suffixRouteValidStep_of_isSuffix_visiblePrimes family p S hsuffix)⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
