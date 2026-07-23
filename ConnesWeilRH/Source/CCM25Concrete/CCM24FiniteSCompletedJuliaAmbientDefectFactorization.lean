/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaMismatchFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSForwardRenewal

/-!
# Physical factorization of the adjacent Julia ambient defect

Proof 505 leaves the ambient part of the adjacent Schur co-defect as

```text
I - T_p T_p^dagger,
```

where `T_p=(1+a_p)^(-1)(I-a_p U_(-log p))`.  This module expands that
operator on the genuine global logarithmic carrier.  The two resonant minus
signs turn into the antiresonant positive product

```text
I - T_p T_p^dagger
  =a_p/(1+a_p)^2 (I+U_(-log p))(I+U_(log p)).
```

The identity is an exact owner refinement.  It is not a separate norm bound
for the ambient and moving-boundary channels.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaAmbientDefectFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSForwardRenewal
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open RCLike
open SelectedCrossingOperatorBridge

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The normalized one-prime ambient defect -/

/-- The adjoint of the normalized adjacent ambient Euler transport. -/
theorem normalizedPrimeEulerFrameTransport_adjoint_eq
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† =
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerCoefficient p : ℂ) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap) := by
  rw [normalizedPrimeEulerFrameTransport]
  simp only [map_smulₛₗ, starRingEnd_apply]
  have hstar :
      star ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) =
        (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ := by
    simp only [star_inv₀, star_add, star_one, Complex.star_def,
      Complex.conj_ofReal]
  rw [hstar, primeEulerTransportAdjoint_eq]

/-- The scalar coefficient in the antiresonant ambient-loss product. -/
noncomputable def primeEulerAmbientLossWeight
    (p : CCM24VisiblePrime) : ℂ :=
  (ccm24PrimeEulerCoefficient p : ℂ) *
    (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ ^ 2

/-- Exact physical normal form of the normalized one-prime ambient loss. -/
theorem normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_antiresonant
    (p : CCM24VisiblePrime) :
    rectangularAmbientCoDefect
        (normalizedPrimeEulerFrameTransport p)
        ((normalizedPrimeEulerFrameTransport p)†) =
      primeEulerAmbientLossWeight p •
        ((ContinuousLinearMap.id ℂ finiteSCarrier +
            (cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap) ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier +
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap)) := by
  have hdenReal :
      (1 + ccm24PrimeEulerCoefficient p : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (ccm24PrimeEulerCoefficient_nonneg p))
  have hdenComplex :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast hdenReal
  have hdenSqComplex :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ) * 2 +
        (ccm24PrimeEulerCoefficient p : ℂ) ^ 2) ≠ 0 := by
    have hsquare :
        1 + (ccm24PrimeEulerCoefficient p : ℂ) * 2 +
            (ccm24PrimeEulerCoefficient p : ℂ) ^ 2 =
          (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ^ 2 := by
      ring
    rw [hsquare]
    exact pow_ne_zero 2 hdenComplex
  rw [normalizedPrimeEulerFrameTransport_adjoint_eq,
    normalizedPrimeEulerFrameTransport,
    CCM24FiniteSJuliaSchur.primeEulerTransport_eq_id_sub_translation]
  apply ContinuousLinearMap.ext
  intro x
  simp only [rectangularAmbientCoDefect,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_add, map_smul]
  have hcancel :
      (cc20GlobalLogTranslation
          (-Real.log p)).toContinuousLinearMap
          ((cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap x) = x := by
    change cc20GlobalLogTranslation (-Real.log p)
        (cc20GlobalLogTranslation (Real.log p) x) = x
    simpa only [neg_neg] using
      cc20GlobalLogTranslation_neg_apply (-Real.log p) x
  rw [hcancel]
  simp only [primeEulerAmbientLossWeight]
  match_scalars
  all_goals field_simp [hdenComplex, hdenSqComplex]
  ring

/-! ## A genuine square root of the ambient loss -/

/-- The real square-root scale in the one-prime ambient loss column. -/
noncomputable def primeEulerAmbientLossScale
    (p : CCM24VisiblePrime) : ℝ :=
  Real.sqrt (ccm24PrimeEulerCoefficient p) /
    (1 + ccm24PrimeEulerCoefficient p)

/-- The complex ambient weight is the square of its real scale. -/
theorem primeEulerAmbientLossScale_sq_eq_weight
    (p : CCM24VisiblePrime) :
    (primeEulerAmbientLossScale p : ℂ) ^ 2 =
      primeEulerAmbientLossWeight p := by
  have hcoeff := ccm24PrimeEulerCoefficient_nonneg p
  have hdenReal :
      (1 + ccm24PrimeEulerCoefficient p : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hcoeff)
  have hdenComplex :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast hdenReal
  have hsqrtComplex :
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ^ 2 =
        (ccm24PrimeEulerCoefficient p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcoeff
  rw [primeEulerAmbientLossScale, primeEulerAmbientLossWeight]
  push_cast
  rw [div_pow, hsqrtComplex]
  field_simp [hdenComplex]

/-- The antiresonant square-root row on the genuine ambient carrier. -/
noncomputable def primeEulerAmbientLossFactor
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (primeEulerAmbientLossScale p : ℂ) •
    (ContinuousLinearMap.id ℂ finiteSCarrier +
      (cc20GlobalLogTranslation
        (-Real.log p)).toContinuousLinearMap)

/-- The factor adjoint reverses the physical translation. -/
theorem primeEulerAmbientLossFactor_adjoint_eq
    (p : CCM24VisiblePrime) :
    (primeEulerAmbientLossFactor p)† =
      (primeEulerAmbientLossScale p : ℂ) •
        (ContinuousLinearMap.id ℂ finiteSCarrier +
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap) := by
  rw [primeEulerAmbientLossFactor]
  simp only [map_smulₛₗ, starRingEnd_apply, map_add,
    ContinuousLinearMap.adjoint_id]
  have hstar :
      star (primeEulerAmbientLossScale p : ℂ) =
        (primeEulerAmbientLossScale p : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hstar, cc20GlobalLogTranslation_neg_adjoint]

/-- The antiresonant product is the Gram operator of the explicit loss
factor. -/
theorem primeEulerAmbientLossFactor_comp_adjoint
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossFactor p ∘L
        (primeEulerAmbientLossFactor p)† =
      primeEulerAmbientLossWeight p •
        ((ContinuousLinearMap.id ℂ finiteSCarrier +
            (cc20GlobalLogTranslation
              (-Real.log p)).toContinuousLinearMap) ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier +
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap)) := by
  rw [primeEulerAmbientLossFactor_adjoint_eq,
    primeEulerAmbientLossFactor]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [show
    (primeEulerAmbientLossScale p : ℂ) *
        (primeEulerAmbientLossScale p : ℂ) =
      primeEulerAmbientLossWeight p by
        simpa only [pow_two] using
          primeEulerAmbientLossScale_sq_eq_weight p]

/-- The normalized Euler ambient co-defect is exactly the Gram operator of
the antiresonant loss factor. -/
theorem normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_factor
    (p : CCM24VisiblePrime) :
    rectangularAmbientCoDefect
        (normalizedPrimeEulerFrameTransport p)
        ((normalizedPrimeEulerFrameTransport p)†) =
      primeEulerAmbientLossFactor p ∘L
        (primeEulerAmbientLossFactor p)† := by
  rw [normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_antiresonant,
    primeEulerAmbientLossFactor_comp_adjoint]

/-! ## The actual two-channel adjacent co-defect owner -/

/-- The ambient-loss column pulled back through the actual old suffix frame.
Its target remains the genuine global logarithmic carrier. -/
noncomputable def suffixEulerFrameAmbientLossColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (primeEulerAmbientLossFactor p)† ∘L
    (suffixEulerFrameSchurStep lambda p S).oldFrame

/-- The pulled-back ambient column has exactly the ambient summand in the
Proof 505 Schur co-defect ledger. -/
theorem suffixEulerFrameAmbientLossColumn_adjoint_comp_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameAmbientLossColumn lambda p S)† ∘L
        suffixEulerFrameAmbientLossColumn lambda p S =
      ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        rectangularAmbientCoDefect
          (suffixEulerFrameSchurStep lambda p S).transport
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transport) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  rw [suffixEulerFrameAmbientLossColumn,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change
    ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        (primeEulerAmbientLossFactor p ∘L
          (primeEulerAmbientLossFactor p)†) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame =
      ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        rectangularAmbientCoDefect
          (normalizedPrimeEulerFrameTransport p)
          ((normalizedPrimeEulerFrameTransport p)†) ∘L
        (suffixEulerFrameSchurStep lambda p S).oldFrame
  rw [← normalizedPrimeEulerFrameTransport_ambientCoDefect_eq_factor]

/-- Orthogonal target carrying the ambient antiresonant loss and the moving
suffix-boundary loss without mixing their coordinates. -/
noncomputable abbrev suffixEulerFrameAmbientBoundaryCarrier :=
  WithLp 2 (finiteSCarrier × finiteSCarrier)

/-- The actual two-channel analysis column for one adjacent Julia step. -/
noncomputable def suffixEulerFrameAmbientBoundaryAnalysis
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ]
      suffixEulerFrameAmbientBoundaryCarrier :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ
      finiteSCarrier finiteSCarrier).symm.toContinuousLinearMap ∘L
    (suffixEulerFrameAmbientLossColumn lambda p S).prod
      (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).boundary)

@[simp]
theorem suffixEulerFrameAmbientBoundaryAnalysis_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryAnalysis lambda p S x =
      WithLp.toLp 2
        (suffixEulerFrameAmbientLossColumn lambda p S x,
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).boundary) x) := by
  rfl

/-- The two physical loss channels have exactly the Gram operator of the
actual adjacent left Julia co-defect. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_adjoint_comp_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameAmbientBoundaryAnalysis lambda p S)† ∘L
        suffixEulerFrameAmbientBoundaryAnalysis lambda p S =
      ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
  rw [suffixEulerFrameLeftCoDefect_adjoint_comp_self_eq_ambient_add_boundary,
    ← suffixEulerFrameAmbientLossColumn_adjoint_comp_self]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  let column := suffixEulerFrameAmbientLossColumn lambda p S
  let boundary := (suffixEulerFrameSchurStep lambda p S).boundary
  have hcolumn :
      ⟪column y, column x⟫_ℂ =
        ⟪y, (ContinuousLinearMap.adjoint column) (column x)⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_right column y (column x)).symm
  have hboundary :
      ⟪(ContinuousLinearMap.adjoint boundary) y,
          (ContinuousLinearMap.adjoint boundary) x⟫_ℂ =
        ⟪y, boundary ((ContinuousLinearMap.adjoint boundary) x)⟫_ℂ := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (ContinuousLinearMap.adjoint_inner_right
        (ContinuousLinearMap.adjoint boundary) y
        ((ContinuousLinearMap.adjoint boundary) x)).symm
  calc
    ⟪y, ((suffixEulerFrameAmbientBoundaryAnalysis lambda p S)† ∘L
          suffixEulerFrameAmbientBoundaryAnalysis lambda p S) x⟫_ℂ =
        ⟪suffixEulerFrameAmbientBoundaryAnalysis lambda p S y,
          suffixEulerFrameAmbientBoundaryAnalysis lambda p S x⟫_ℂ := by
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪column y, column x⟫_ℂ +
        ⟪(ContinuousLinearMap.adjoint boundary) y,
          (ContinuousLinearMap.adjoint boundary) x⟫_ℂ := by
      simp only [column, boundary,
        suffixEulerFrameAmbientBoundaryAnalysis_apply,
        WithLp.prod_inner_apply]
    _ = ⟪y, ((ContinuousLinearMap.adjoint column ∘L column) +
          (boundary ∘L ContinuousLinearMap.adjoint boundary)) x⟫_ℂ := by
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, inner_add_right,
        hcolumn, hboundary]

/-- The packed physical two-channel energy equals the actual Julia
co-defect energy pointwise. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 =
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
  calc
    ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 =
        re ⟪((suffixEulerFrameAmbientBoundaryAnalysis lambda p S)† ∘L
          suffixEulerFrameAmbientBoundaryAnalysis lambda p S) x, x⟫_ℂ := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = re ⟪(ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect) x, x⟫_ℂ := by
      rw [suffixEulerFrameAmbientBoundaryAnalysis_adjoint_comp_self]
    _ = ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]

/-- The packed energy is literally the sum of the two physical channel
energies. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ ^ 2 =
      ‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
        ‖(ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2 := by
  rw [suffixEulerFrameAmbientBoundaryAnalysis_apply,
    WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
        ‖(ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2 = _
  rfl

/-- Explicit two-channel energy formula for the actual adjacent Julia
co-defect.  The sum must remain intact in later estimates. -/
theorem suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ ^ 2 =
      ‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
        ‖(ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2 := by
  rw [← suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect,
    suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels]

/-- Vanishing of the physical ambient-plus-boundary column is exactly
vanishing of the actual adjacent Julia co-defect. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0 ↔
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0 := by
  have hnorm :
      ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ =
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
      lambda p S x
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [← hnorm, hx, norm_zero]
  · intro hx
    apply norm_eq_zero.mp
    rw [hnorm, hx, norm_zero]

/-- The actual Julia zero modes are exactly the simultaneous zero modes of
the ambient antiresonant loss and the moving-boundary adjoint. -/
theorem suffixEulerFrameLeftCoDefect_eq_zero_iff_channels_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0 ↔
      suffixEulerFrameAmbientLossColumn lambda p S x = 0 ∧
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x = 0 := by
  constructor
  · intro hx
    have hsum := suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary
      lambda p S x
    rw [hx, norm_zero] at hsum
    norm_num at hsum
    have hfirst :
        ‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).boundary) x‖]
    have hsecond :
        ‖(ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖suffixEulerFrameAmbientLossColumn lambda p S x‖]
    constructor
    · apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        (suffixEulerFrameAmbientLossColumn lambda p S x)]
    · apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        ((ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).boundary) x)]
  · rintro ⟨hfirst, hsecond⟩
    have hsum := suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary
      lambda p S x
    rw [hfirst, hsecond, norm_zero] at hsum
    norm_num at hsum
    exact hsum

/-! ## The physical form of the remaining Douglas gate -/

/-- Proof 505's Douglas estimate written on the actual ambient and boundary
channels.  The channels are summed before the inequality; this definition
does not license separate bounds. -/
def SuffixMismatchAmbientBoundaryDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ x : sourceSoninCarrier lambda,
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ^ 2 ≤
        bound ^ 2 *
          (‖suffixEulerFrameAmbientLossColumn lambda p S x‖ ^ 2 +
            ‖(ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).boundary) x‖ ^ 2)

/-- The explicit physical two-channel condition is exactly Proof 505's
abstract left-co-defect Douglas condition. -/
theorem suffixMismatchAmbientBoundaryDomination_iff_douglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixMismatchAmbientBoundaryDomination owner lambda p S bound ↔
      SuffixMismatchAdjointDouglasDomination owner lambda p S bound := by
  constructor
  · rintro ⟨hbound, hphysical⟩
    refine ⟨hbound, ?_⟩
    intro x
    rw [suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary]
    exact hphysical x
  · rintro ⟨hbound, hdouglas⟩
    refine ⟨hbound, ?_⟩
    intro x
    rw [← suffixEulerFrameLeftCoDefect_normSq_eq_ambient_add_boundary]
    exact hdouglas x

/-- A physical two-channel domination produces the same correctly oriented
co-defect factor as Proof 505's Douglas constructor. -/
noncomputable def suffixMismatchCoDefectFactorDataOfAmbientBoundaryDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ)
    (hdom : SuffixMismatchAmbientBoundaryDomination
      owner lambda p S bound) :
    SuffixMismatchCoDefectFactorData owner lambda p S bound :=
  suffixMismatchCoDefectFactorDataOfDomination owner lambda p S bound
    ((suffixMismatchAmbientBoundaryDomination_iff_douglas
      owner lambda p S bound).mp hdom)

/-- Proof 505's mismatch-kernel reduction can be read directly from the
explicit ambient-plus-boundary zero mode. -/
theorem suffixMismatchIntertwining_adjoint_on_ambientBoundaryKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x =
      -((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x := by
  apply suffixMismatchIntertwining_adjoint_on_leftCoDefectKernel
  exact
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mp hx

end CCM24FiniteSCompletedJuliaAmbientDefectFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
