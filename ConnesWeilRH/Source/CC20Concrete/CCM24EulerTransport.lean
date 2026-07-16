/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Concrete finite Euler transport on the global logarithmic carrier

In the physical logarithmic coordinate `rho = exp t`, a finite-place CCM24
transport factor is `I - p^(-1/2) U_(-log p)`. Here `U_b` is the translation
isometry on the global `L2` carrier. Since `p^(-1/2) < 1`, every factor is a
unit in the Banach algebra of bounded endomorphisms and therefore determines
a genuine continuous linear equivalence.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

/-- A visible finite place. The analytic construction only needs `p > 1`;
primality remains part of the arithmetic owner that supplies the list. -/
abbrev CCM24VisiblePrime := {p : ℕ // 1 < p}

/-- The critical-line Euler contraction coefficient `p^(-1/2)`. -/
noncomputable def ccm24PrimeEulerCoefficient (p : CCM24VisiblePrime) : ℝ :=
  1 / Real.sqrt p

theorem ccm24PrimeEulerCoefficient_nonneg (p : CCM24VisiblePrime) :
    0 ≤ ccm24PrimeEulerCoefficient p := by
  exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem ccm24PrimeEulerCoefficient_lt_one (p : CCM24VisiblePrime) :
    ccm24PrimeEulerCoefficient p < 1 := by
  have hp : (1 : ℝ) < p := by
    exact_mod_cast p.property
  have hsqrt : 1 < Real.sqrt p := by
    exact (Real.lt_sqrt (by norm_num)).2 (by simpa using hp)
  exact (div_lt_one (lt_trans zero_lt_one hsqrt)).2 hsqrt

/-- The strict contraction `p^(-1/2) U_(-log p)` on the global log carrier. -/
noncomputable def ccm24PrimeEulerContraction (p : CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (ccm24PrimeEulerCoefficient p : ℂ) •
    (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap

theorem norm_ccm24PrimeEulerContraction_lt_one (p : CCM24VisiblePrime) :
    ‖ccm24PrimeEulerContraction p‖ < 1 := by
  rw [ccm24PrimeEulerContraction, norm_smul]
  calc
    ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ *
          ‖(cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap‖ ≤
        ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (cc20GlobalLogTranslation (-Real.log p)).norm_toContinuousLinearMap_le
        (norm_nonneg _)
    _ = ccm24PrimeEulerCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
    _ < 1 := ccm24PrimeEulerCoefficient_lt_one p

/-- The Banach-algebra unit with value `I - p^(-1/2) U_(-log p)`. -/
noncomputable def ccm24PrimeEulerUnit (p : CCM24VisiblePrime) :
    (cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2)ˣ :=
  Units.oneSub (ccm24PrimeEulerContraction p)
    (norm_ccm24PrimeEulerContraction_lt_one p)

/-- One concrete finite-place CCM24 transport factor. -/
noncomputable def ccm24PrimeEulerTransportEquiv (p : CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 ≃L[ℂ] cc20GlobalLogCrossingL2 :=
  ContinuousLinearEquiv.unitsEquiv ℂ cc20GlobalLogCrossingL2
    (ccm24PrimeEulerUnit p)

theorem ccm24PrimeEulerTransportEquiv_apply
    (p : CCM24VisiblePrime) (u : cc20GlobalLogCrossingL2) :
    ccm24PrimeEulerTransportEquiv p u =
      u - (ccm24PrimeEulerCoefficient p : ℂ) •
        cc20GlobalLogTranslation (-Real.log p) u := by
  change ((1 - ccm24PrimeEulerContraction p) :
      cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2) u = _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ccm24PrimeEulerContraction, ContinuousLinearMap.smul_apply]
  rfl

/-- In the physical logarithmic coordinate, the Euler factor is exactly the
source formula `g(lambda) - p^(-1/2) g(lambda / p)`, with `lambda = exp t`. -/
theorem ccm24PrimeEulerTransportEquiv_coeFn
    (p : CCM24VisiblePrime) (u : cc20GlobalLogCrossingL2) :
    (ccm24PrimeEulerTransportEquiv p u : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
      fun t => u t - (ccm24PrimeEulerCoefficient p : ℂ) *
        u (t - Real.log p) := by
  rw [ccm24PrimeEulerTransportEquiv_apply]
  filter_upwards
    [Lp.coeFn_sub u
      ((ccm24PrimeEulerCoefficient p : ℂ) •
        cc20GlobalLogTranslation (-Real.log p) u),
      Lp.coeFn_smul (ccm24PrimeEulerCoefficient p : ℂ)
        (cc20GlobalLogTranslation (-Real.log p) u),
      cc20GlobalLogTranslation_coeFn (-Real.log p) u] with t hsub hsmul htrans
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [htrans]
  congr 2

/-- The exact Neumann-series inverse operator of one Euler factor. -/
noncomputable def ccm24PrimeEulerInverseOperator (p : CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ∑' n : ℕ, ccm24PrimeEulerContraction p ^ n

theorem ccm24PrimeEulerTransportEquiv_symm_toContinuousLinearMap
    (p : CCM24VisiblePrime) :
    (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap =
      ccm24PrimeEulerInverseOperator p := by
  rfl

theorem ccm24PrimeEulerInverse_mul_factor (p : CCM24VisiblePrime) :
    ccm24PrimeEulerInverseOperator p *
        (1 - ccm24PrimeEulerContraction p) = 1 := by
  exact geom_series_mul_neg (ccm24PrimeEulerContraction p)
    (norm_ccm24PrimeEulerContraction_lt_one p)

/-- Euler contractions at two visible finite places commute because their
translation operators belong to the same additive representation. -/
theorem ccm24PrimeEulerContraction_commute
    (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerContraction p)
      (ccm24PrimeEulerContraction q) := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ccm24PrimeEulerContraction, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  have htranslation :
      (cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap
          ((cc20GlobalLogTranslation (-Real.log q)).toContinuousLinearMap u) =
        (cc20GlobalLogTranslation (-Real.log q)).toContinuousLinearMap
          ((cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap u) :=
    cc20GlobalLogTranslation_commute (-Real.log p) (-Real.log q) u
  have hcoefficient :
      (ccm24PrimeEulerCoefficient q : ℂ) *
          (ccm24PrimeEulerCoefficient p : ℂ) =
        (ccm24PrimeEulerCoefficient p : ℂ) *
          (ccm24PrimeEulerCoefficient q : ℂ) := mul_comm _ _
  rw [htranslation, hcoefficient]

/-- The underlying operators `I - p^(-1/2) U_(-log p)` commute. -/
theorem ccm24PrimeEulerFactor_commute
    (p q : CCM24VisiblePrime) :
    Commute (1 - ccm24PrimeEulerContraction p)
      (1 - ccm24PrimeEulerContraction q) :=
  (Commute.one_left _).sub_left
    ((Commute.one_right _).sub_right
      (ccm24PrimeEulerContraction_commute p q))

/-- The corresponding Banach-algebra units commute as units, including their
inverse data. -/
theorem ccm24PrimeEulerUnit_commute
    (p q : CCM24VisiblePrime) :
    Commute (ccm24PrimeEulerUnit p) (ccm24PrimeEulerUnit q) := by
  apply Commute.units_of_val
  change Commute (1 - ccm24PrimeEulerContraction p)
    (1 - ccm24PrimeEulerContraction q)
  exact ccm24PrimeEulerFactor_commute p q

/-- The ordered product of the concrete finite-place Euler units. Lists avoid
assuming commutativity before the translation-commutation theorem is proved. -/
noncomputable def ccm24FiniteEulerUnit (S : List CCM24VisiblePrime) :
    (cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2)ˣ :=
  (S.map ccm24PrimeEulerUnit).prod

theorem ccm24PrimeEulerUnit_list_pairwise
    (S : List CCM24VisiblePrime) :
    (S.map ccm24PrimeEulerUnit).Pairwise Commute := by
  induction S with
  | nil => simp
  | cons p S ih =>
      simp only [List.map_cons, List.pairwise_cons, List.mem_map]
      constructor
      · rintro _ ⟨q, _, rfl⟩
        exact ccm24PrimeEulerUnit_commute p q
      · exact ih

/-- The finite Euler unit depends only on the multiset of visible places, not
on the chosen list order. -/
theorem ccm24FiniteEulerUnit_eq_of_perm
    {S T : List CCM24VisiblePrime} (h : S.Perm T) :
    ccm24FiniteEulerUnit S = ccm24FiniteEulerUnit T := by
  exact (h.map ccm24PrimeEulerUnit).prod_eq'
    (ccm24PrimeEulerUnit_list_pairwise S)

/-- The ambient bounded invertible CCM24 finite Euler transport on the common
global logarithmic `L2` carrier. -/
noncomputable def ccm24FiniteEulerTransportEquiv (S : List CCM24VisiblePrime) :
    cc20GlobalLogCrossingL2 ≃L[ℂ] cc20GlobalLogCrossingL2 :=
  ContinuousLinearEquiv.unitsEquiv ℂ cc20GlobalLogCrossingL2
    (ccm24FiniteEulerUnit S)

@[simp]
theorem ccm24FiniteEulerTransportEquiv_nil :
    ccm24FiniteEulerTransportEquiv [] =
      ContinuousLinearEquiv.refl ℂ cc20GlobalLogCrossingL2 := by
  rfl

theorem ccm24FiniteEulerTransportEquiv_cons_apply
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (u : cc20GlobalLogCrossingL2) :
    ccm24FiniteEulerTransportEquiv (p :: S) u =
      ccm24PrimeEulerTransportEquiv p
        (ccm24FiniteEulerTransportEquiv S u) := by
  rfl

/-- Reordering the visible finite places does not change the concrete ambient
CCM24 transport equivalence. -/
theorem ccm24FiniteEulerTransportEquiv_eq_of_perm
    {S T : List CCM24VisiblePrime} (h : S.Perm T) :
    ccm24FiniteEulerTransportEquiv S =
      ccm24FiniteEulerTransportEquiv T := by
  rw [ccm24FiniteEulerTransportEquiv, ccm24FiniteEulerTransportEquiv,
    ccm24FiniteEulerUnit_eq_of_perm h]

end CC20Concrete
end Source
end ConnesWeilRH
