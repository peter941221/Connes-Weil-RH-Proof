/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassWindowObjects
import ConnesWeilRH.Dev.C1HboxRationalData

/-!
# Record 1125: the class-window Gram owner

This module names the real Gram matrix carried by the class-window objects of
record 1124.  Its entries are ordinary integrals of the real window cores,
matching the `G_TAB` owner used by the 1112 pipeline.  The module proves the
support, integrability, symmetry, and finite quadratic-form identities needed
by later true-data consumers.

The narrow entrywise `Hbox-G` inequalities remain explicit hypotheses here;
no floating-point or quadrature output is treated as a theorem.  RH is NOT
claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramOwner

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open C1ClassWindowObjects
open C1HboxRationalData
open Matrix
open Polynomial
open scoped BigOperators ContDiff Topology Filter

noncomputable section

/-! ## The real class-window core -/

/-- The real class-window core is smooth at every class scale. -/
theorem classWindowFun_contDiff (a : ℝ) (ha : 0 < a) (i : ℕ) :
    ContDiff ℝ ∞ (classWindowFun a i) := by
  have hdiv : ContDiff ℝ ∞ (fun u : ℝ => u / a) := by
    fun_prop
  have hpoly : ContDiff ℝ ∞
      (fun u : ℝ => eval (u / a) (legendrePoly i)) :=
    (contDiff_legendreEval (legendrePoly i)).comp hdiv
  have hbump : ContDiff ℝ ∞
      (fun u : ℝ => classBump (u / a)) :=
    classBump_contDiff.comp hdiv
  exact hpoly.mul hbump

/-- The real core has the same closed support interval as its complexified
packaging. -/
theorem classWindowFun_support_subset_Icc (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Function.support (classWindowFun a i) ⊆ Icc (-a) a := by
  intro u hu
  rw [Function.mem_support] at hu
  exact support_subset_Icc a ha i (by
    rw [Function.mem_support]
    intro hzero
    apply hu
    simpa using hzero)

/-- Compact support of the real class-window core. -/
theorem classWindowFun_hasCompactSupport (a : ℝ) (ha : 0 < a) (i : ℕ) :
    HasCompactSupport (classWindowFun a i) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (classWindowFun_support_subset_Icc a ha i)

/-- Every pairwise product of class-window cores is integrable. -/
theorem classWindowProduct_integrable (a : ℝ) (ha : 0 < a) (i j : ℕ) :
    Integrable (fun x : ℝ => classWindowFun a i x * classWindowFun a j x) := by
  have hcont : Continuous
      (fun x : ℝ => classWindowFun a i x * classWindowFun a j x) :=
    (classWindowFun_contDiff a ha i).continuous.mul
      (classWindowFun_contDiff a ha j).continuous
  have hcompact : HasCompactSupport
      (fun x : ℝ => classWindowFun a i x * classWindowFun a j x) :=
    HasCompactSupport.mul_right (classWindowFun_hasCompactSupport a ha i)
  exact hcont.integrable_of_hasCompactSupport hcompact

/-! ## The same-owner Gram definitions -/

/-- The real Gram entry of two class-window cores. -/
noncomputable def classGramEntry (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) : ℝ :=
  let _ha := ha
  ∫ x : ℝ, classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x

/-- The `(a,8)` class-window Gram matrix. -/
noncomputable def classGramMatrix (a : ℝ) (ha : 0 < a) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => classGramEntry a ha i j

@[simp] theorem classGramMatrix_apply (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) :
    classGramMatrix a ha i j = classGramEntry a ha i j :=
  rfl

/-- The 1124 compact-log test evaluates to its defining real core. -/
@[simp] theorem classWindowTest_apply (a : ℝ) (ha : 0 < a)
    (i : ℕ) (x : ℝ) :
    (classWindowTest a ha i).test x = (classWindowFun a i x : ℂ) := by
  rfl

/-- The family notation preserves the 1124 support certificate. -/
theorem classTestFamily_support (a : ℝ) (ha : 0 < a) (i : Fin 8) :
    Function.support (classTestFamily a ha i).test ⊆ Ioo (-a) a := by
  simpa [classTestFamily] using classWindowTest_support a ha (i : ℕ)

/-- The complex product integral of the packaged tests is the complex cast of
the real Gram entry. -/
theorem classGramEntry_complex_integral (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) :
    (∫ x : ℝ, (classTestFamily a ha i).test x *
      (classTestFamily a ha j).test x) =
        (classGramEntry a ha i j : ℂ) := by
  change (∫ x : ℝ,
      (classWindowFun a (i : ℕ) x : ℂ) *
        (classWindowFun a (j : ℕ) x : ℂ)) =
    (classGramEntry a ha i j : ℂ)
  simp_rw [← Complex.ofReal_mul]
  exact ContinuousLinearMap.integral_comp_comm (L := Complex.ofRealCLM)
    (Integrable.ofReal (classWindowProduct_integrable a ha i j))

/-- The class Gram matrix is symmetric. -/
theorem classGramMatrix_transpose (a : ℝ) (ha : 0 < a) :
    (classGramMatrix a ha)ᵀ = classGramMatrix a ha := by
  ext i j
  unfold classGramMatrix classGramEntry
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-! ## Quadratic-form readback -/

private theorem classGram_double_sum_integral (a : ℝ) (ha : 0 < a)
    (c : Fin 8 → ℝ) :
    (∑ i : Fin 8, ∑ j : Fin 8,
        c i * c j * classGramEntry a ha i j) =
      ∫ x : ℝ, ∑ i : Fin 8, ∑ j : Fin 8,
        c i * c j * (classWindowFun a (i : ℕ) x *
          classWindowFun a (j : ℕ) x) := by
  calc
    (∑ i : Fin 8, ∑ j : Fin 8,
        c i * c j * classGramEntry a ha i j) =
        ∑ i : Fin 8, ∑ j : Fin 8,
          ∫ x : ℝ, c i * c j *
            (classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [classGramEntry]
      rw [← MeasureTheory.integral_const_mul]
    _ = ∫ x : ℝ, ∑ i : Fin 8, ∑ j : Fin 8,
        c i * c j * (classWindowFun a (i : ℕ) x *
          classWindowFun a (j : ℕ) x) := by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [MeasureTheory.integral_finsetSum]
        intro j hj
        exact (classWindowProduct_integrable a ha i j).const_mul' (c i * c j)
      · intro i hi
        refine integrable_finsetSum (Finset.univ : Finset (Fin 8)) ?_
        intro j hj
        exact (classWindowProduct_integrable a ha i j).const_mul' (c i * c j)

/-- The Gram quadratic form is the integral of the square of the finite
linear combination of class-window cores. -/
theorem classGramMatrix_quadratic_eq_integral_square
    (a : ℝ) (ha : 0 < a) (c : Fin 8 → ℝ) :
    c ⬝ᵥ (classGramMatrix a ha *ᵥ c) =
      ∫ x : ℝ, (∑ i : Fin 8,
        c i * classWindowFun a (i : ℕ) x) ^ 2 := by
  calc
    c ⬝ᵥ (classGramMatrix a ha *ᵥ c) =
        ∑ i : Fin 8, ∑ j : Fin 8,
          c i * c j * classGramEntry a ha i j := by
      simp only [dotProduct, Matrix.mulVec, classGramMatrix, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∫ x : ℝ, ∑ i : Fin 8, ∑ j : Fin 8,
        c i * c j * (classWindowFun a (i : ℕ) x *
          classWindowFun a (j : ℕ) x) :=
      classGram_double_sum_integral a ha c
    _ = ∫ x : ℝ, (∑ i : Fin 8,
        c i * classWindowFun a (i : ℕ) x) ^ 2 := by
      congr 1
      funext x
      simp only [pow_two]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

/-- The class Gram quadratic form is nonnegative. -/
theorem classGramMatrix_quadratic_nonneg (a : ℝ) (ha : 0 < a)
    (c : Fin 8 → ℝ) :
    0 ≤ c ⬝ᵥ (classGramMatrix a ha *ᵥ c) := by
  rw [classGramMatrix_quadratic_eq_integral_square a ha c]
  exact integral_nonneg fun x => sq_nonneg _

/-! ## Hbox-G consumer socket -/

/-- Explicit Gram and M entrywise bounds assemble into the exact Hbox
proposition consumed by the existing true-data T-box chain. -/
theorem hbox_of_classGramBounds
    (a : ℝ) (ha : 0 < a)
    (GLo GHi MLo MHi : Matrix (Fin 8) (Fin 8) ℝ)
    (M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, GLo i j ≤ classGramMatrix a ha i j ∧
      classGramMatrix a ha i j ≤ GHi i j)
    (hM : ∀ i j, MLo i j ≤ M_true i j ∧ M_true i j ≤ MHi i j) :
    Hbox GLo GHi MLo MHi (classGramMatrix a ha) M_true :=
  ⟨hG, hM⟩

end
end C1ClassGramOwner
end Source
end ConnesWeilRH
