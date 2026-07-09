/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20ConcreteTestSpace
import ConnesWeilRH.Source.CC20YoshidaCriterion

/-!
# Concrete Mellin evaluation map for the Yoshida nodes

This module fixes the finite evaluation map that 05C2D must make surjective.
It does not construct a test and does not assume detector existence.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaInterpolationNode

open MeasureTheory Asymptotics Filter Set
open scoped Topology

noncomputable def concreteMellinEvaluationMap
    (rho : ℂ) (g : normalizedCC20ConcreteTestAlgebra.Test) :
    CC20YoshidaInterpolationNode → ℂ :=
  fun n => normalizedCC20ConcreteEvaluationData.mellinAt g (nodeValue rho n)

def ConcreteMellinRealizesDesired
    (rho : ℂ) (g : normalizedCC20ConcreteTestAlgebra.Test) : Prop :=
  ∀ n : CC20YoshidaInterpolationNode,
    concreteMellinEvaluationMap rho g n = desiredMellinValue n

noncomputable def finiteLinearCombination
    (coeff : CC20YoshidaInterpolationNode → ℂ)
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20ConcreteTestAlgebra.Test :=
  normalizedCC20ConcreteTestAlgebra.legacy.decode
    (∑ j,
      coeff j • normalizedCC20ConcreteTestAlgebra.legacy.encode (basisTest j))

@[simp] theorem concreteMellinEvaluationMap_eq_mellin
    (rho : ℂ) (g : normalizedCC20ConcreteTestAlgebra.Test)
    (n : CC20YoshidaInterpolationNode) :
    concreteMellinEvaluationMap rho g n =
      mellin
        (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
        (nodeValue rho n) := by
  simp [concreteMellinEvaluationMap]

theorem concreteMellinRealizesDesired_eval_zero
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20ConcreteEvaluationData.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.zero) = 0 := by
  simpa [ConcreteMellinRealizesDesired, concreteMellinEvaluationMap,
    nodeValue, desiredMellinValue] using h zero

theorem concreteMellinRealizesDesired_eval_half
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20ConcreteEvaluationData.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.half) = 0 := by
  simpa [ConcreteMellinRealizesDesired, concreteMellinEvaluationMap,
    nodeValue, desiredMellinValue] using h half

theorem concreteMellinRealizesDesired_eval_one
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20ConcreteEvaluationData.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.one) = 0 := by
  simpa [ConcreteMellinRealizesDesired, concreteMellinEvaluationMap,
    nodeValue, desiredMellinValue] using h one

theorem concreteMellinRealizesDesired_eval_rho
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20ConcreteEvaluationData.mellinAt g rho = 1 := by
  simpa [ConcreteMellinRealizesDesired, concreteMellinEvaluationMap,
    nodeValue, desiredMellinValue] using h .rho

theorem concreteMellinRealizesDesired_detects_rho
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20ConcreteEvaluationData.mellinAt g rho ≠ 0 := by
  rw [concreteMellinRealizesDesired_eval_rho h]
  norm_num

theorem concreteMellinRealizesDesired_vanishesOn_cc20Triple
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g := by
  intro p _hp
  cases p with
  | zero =>
      simpa [normalizedCC20TestSpace_mellinAt_eq] using
        concreteMellinRealizesDesired_eval_zero h
  | half =>
      simpa [normalizedCC20TestSpace_mellinAt_eq] using
        concreteMellinRealizesDesired_eval_half h
  | one =>
      simpa [normalizedCC20TestSpace_mellinAt_eq] using
        concreteMellinRealizesDesired_eval_one h

theorem concreteMellinRealizesDesired_normalized_detects_rho
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteMellinRealizesDesired rho g) :
    normalizedCC20TestSpace.mellinAt g rho ≠ 0 := by
  simpa [normalizedCC20TestSpace_mellinAt_eq] using
    concreteMellinRealizesDesired_detects_rho h

theorem testFunction_eventuallyEq_zero_atTop_of_support_subset_Icc
    (f : TestFunction) {a b : ℝ}
    (hsupp : Function.support (fun x : ℝ => f x) ⊆ Set.Icc a b) :
    (fun x : ℝ => f x) =ᶠ[atTop] (fun _x : ℝ => 0) := by
  filter_upwards [eventually_gt_atTop b] with x hx
  by_contra hfx
  have hxmem : x ∈ Function.support (fun x : ℝ => f x) := by
    exact Function.mem_support.mpr hfx
  have hxb : x ≤ b := (hsupp hxmem).2
  linarith

theorem testFunction_eventuallyEq_zero_nhdsGT_zero_of_support_subset_Icc
    (f : TestFunction) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support (fun x : ℝ => f x) ⊆ Set.Icc a b) :
    (fun x : ℝ => f x) =ᶠ[𝓝[>] (0 : ℝ)] (fun _x : ℝ => 0) := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds (show (0 : ℝ) < a by exact ha))] with x hx
  by_contra hfx
  have hxmem : x ∈ Function.support (fun x : ℝ => f x) := by
    exact Function.mem_support.mpr hfx
  have hxa : a ≤ x := (hsupp hxmem).1
  have hxlt : x < a := hx
  linarith

theorem testFunction_mellinConvergent_of_support_subset_Icc
    (f : TestFunction) (s : ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support (fun x : ℝ => f x) ⊆ Set.Icc a b) :
    MellinConvergent (fun x : ℝ => f x) s := by
  refine mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    ?hlocal ?htop ?hsTop ?hbot ?hsBot
  · exact
      (SchwartzMap.continuous f).locallyIntegrable.locallyIntegrableOn
        (Set.Ioi 0)
  · exact
      (isBigO_zero (fun x : ℝ => x ^ (-(s.re + 1))) atTop).congr'
        (testFunction_eventuallyEq_zero_atTop_of_support_subset_Icc
          f hsupp).symm
        EventuallyEq.rfl
  · linarith
  · exact
      (isBigO_zero (fun x : ℝ => x ^ (-(s.re - 1)))
        (𝓝[>] (0 : ℝ))).congr'
        (testFunction_eventuallyEq_zero_nhdsGT_zero_of_support_subset_Icc
          f ha hsupp).symm
        EventuallyEq.rfl
  · linarith

theorem exists_testFunction_supported_Icc_eq_one
    {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    ∃ g : TestFunction,
      Function.support (fun t : ℝ => g t) ⊆ Set.Icc a b ∧
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      g x = 1 := by
  obtain ⟨u, htsupp, hcompact, hsmooth, _hrange, hux⟩ :=
    exists_contDiff_tsupport_subset (s := Set.Ioo a b) (x := x) (n := ⊤)
      (Ioo_mem_nhds hax hxb)
  let v : ℝ → ℂ := Complex.ofRealCLM ∘ u
  have hvcompact : HasCompactSupport v := hcompact.comp_left (by simp)
  let hvsmooth := Complex.ofRealCLM.contDiff.comp hsmooth
  let g : TestFunction := hvcompact.toSchwartzMap hvsmooth
  refine ⟨g, ?_, ?_, ?_⟩
  · intro y hy
    have hyts : y ∈ tsupport v := subset_tsupport v hy
    have hytsu : y ∈ tsupport u := tsupport_comp_subset (by simp) u hyts
    have hyIoo : y ∈ Set.Ioo a b := htsupp hytsu
    exact ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
  · rw [normalizedCC20TestSpace_compactSupportSmooth_eq]
    simpa [g, v] using hvcompact
  · simp [g, v, hux]

theorem exists_yoshida_indexed_testFunction_basis_supported_Icc
    (center lower upper : CC20YoshidaInterpolationNode → ℝ)
    (hlower : ∀ j, lower j < center j)
    (hupper : ∀ j, center j < upper j) :
    ∃ basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test,
      (∀ j,
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (basisTest j) x) ⊆ Set.Icc (lower j) (upper j)) ∧
      (∀ j,
        normalizedCC20TestSpace.compactSupportSmooth (basisTest j)) ∧
      (∀ j,
        normalizedCC20ConcreteTestAlgebra.legacy.encode
          (basisTest j) (center j) = 1) := by
  classical
  choose basisTest hsupport hcompact hvalue using
    fun j => exists_testFunction_supported_Icc_eq_one
      (hax := hlower j) (hxb := hupper j)
  exact ⟨basisTest, hsupport, hcompact, hvalue⟩

theorem finiteLinearCombination_compactSupportSmooth
    (coeff : CC20YoshidaInterpolationNode → ℂ)
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j)) :
    normalizedCC20TestSpace.compactSupportSmooth
      (finiteLinearCombination coeff basisTest) := by
  rw [normalizedCC20TestSpace_compactSupportSmooth_eq]
  unfold finiteLinearCombination
  simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
  exact
    (HasCompactSupport.finset_sum
      (s := (Finset.univ : Finset CC20YoshidaInterpolationNode))
      (f := fun j : CC20YoshidaInterpolationNode =>
        fun x : ℝ =>
          (coeff j •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (basisTest j)) x)
      (fun j _hj => by
        have hj := hcompact j
        rw [normalizedCC20TestSpace_compactSupportSmooth_eq] at hj
        simpa [SchwartzMap.smul_apply] using
          (HasCompactSupport.smul_left
            (f := fun _x : ℝ => coeff j)
            (f' := fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode
                (basisTest j) x)
            hj)))

theorem concreteMellinEvaluationMap_finiteLinearCombination
    (rho : ℂ)
    (coeff : CC20YoshidaInterpolationNode → ℂ)
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (i : CC20YoshidaInterpolationNode)
    (hconv : ∀ j,
      MellinConvergent
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x)
        (nodeValue rho i)) :
    concreteMellinEvaluationMap rho
        (finiteLinearCombination coeff basisTest) i =
      Matrix.mulVec
        (Matrix.of fun i j =>
          concreteMellinEvaluationMap rho (basisTest j) i)
        coeff i := by
  have hmellin :
      mellin
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (finiteLinearCombination coeff basisTest) x)
          (nodeValue rho i) =
        ∑ j : CC20YoshidaInterpolationNode,
          coeff j *
            mellin
              (fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode
                  (basisTest j) x)
              (nodeValue rho i) := by
    unfold finiteLinearCombination
    rw [mellin]
    calc
      (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (nodeValue rho i - 1) •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (normalizedCC20ConcreteTestAlgebra.legacy.decode
                (∑ j : CC20YoshidaInterpolationNode,
                  coeff j •
                    normalizedCC20ConcreteTestAlgebra.legacy.encode
                      (basisTest j))) t) =
          ∫ t : ℝ in Set.Ioi 0,
            ∑ j : CC20YoshidaInterpolationNode,
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((coeff j •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j)) t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t _ht
            simp [SchwartzMap.sum_apply, Finset.mul_sum]
      _ =
          ∑ j : CC20YoshidaInterpolationNode,
            ∫ t : ℝ in Set.Ioi 0,
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((coeff j •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j)) t) := by
            rw [integral_finsetSum]
            intro j _hj
            exact hconv j |>.const_smul (coeff j)
      _ =
          ∑ j : CC20YoshidaInterpolationNode,
            coeff j *
              mellin
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j) x)
                (nodeValue rho i) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simpa [mellin, SchwartzMap.smul_apply, smul_eq_mul] using
              (mellin_const_smul
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j) x)
                (nodeValue rho i)
                (coeff j))
  rw [concreteMellinEvaluationMap_eq_mellin, hmellin]
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Matrix.of_apply, concreteMellinEvaluationMap_eq_mellin]
  ring

theorem concreteMellinRealizesDesired_of_basis_matrix_det_ne_zero
    {rho : ℂ}
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hconv : ∀ i j,
      MellinConvergent
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x)
        (nodeValue rho i))
    (hdet :
      (Matrix.of fun i j =>
        concreteMellinEvaluationMap rho (basisTest j) i).det ≠ 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteMellinRealizesDesired rho g := by
  let M : Matrix
      CC20YoshidaInterpolationNode
      CC20YoshidaInterpolationNode ℂ :=
    Matrix.of fun i j =>
      concreteMellinEvaluationMap rho (basisTest j) i
  let coeff : CC20YoshidaInterpolationNode → ℂ :=
    Matrix.mulVec M⁻¹ desiredMellinValue
  refine ⟨finiteLinearCombination coeff basisTest, ?_, ?_⟩
  · exact finiteLinearCombination_compactSupportSmooth coeff basisTest hcompact
  · intro i
    have hunit : IsUnit M.det := by
      exact isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
    rw [concreteMellinEvaluationMap_finiteLinearCombination
      rho coeff basisTest i (hconv i)]
    change Matrix.mulVec M (Matrix.mulVec M⁻¹ desiredMellinValue) i =
      desiredMellinValue i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]

theorem concreteMellinRealizesDesired_of_positive_interval_supported_basis
    {rho : ℂ}
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (lower upper : CC20YoshidaInterpolationNode → ℝ)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hlower : ∀ j, 0 < lower j)
    (hsupp : ∀ j,
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x) ⊆ Set.Icc (lower j) (upper j))
    (hdet :
      (Matrix.of fun i j =>
        concreteMellinEvaluationMap rho (basisTest j) i).det ≠ 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteMellinRealizesDesired rho g := by
  exact concreteMellinRealizesDesired_of_basis_matrix_det_ne_zero
    basisTest hcompact
    (fun i j =>
      testFunction_mellinConvergent_of_support_subset_Icc
        (normalizedCC20ConcreteTestAlgebra.legacy.encode (basisTest j))
        (nodeValue rho i) (hlower j) (hsupp j))
    hdet

theorem concreteMellinRealizesDesired_of_kronecker_mellin_basis
    {rho : ℂ}
    (basisTest :
      CC20YoshidaInterpolationNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (lower upper : CC20YoshidaInterpolationNode → ℝ)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hlower : ∀ j, 0 < lower j)
    (hsupp : ∀ j,
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x) ⊆ Set.Icc (lower j) (upper j))
    (hkronecker : ∀ i j,
      concreteMellinEvaluationMap rho (basisTest j) i =
        if i = j then 1 else 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteMellinRealizesDesired rho g := by
  refine concreteMellinRealizesDesired_of_positive_interval_supported_basis
    basisTest lower upper hcompact hlower hsupp ?_
  have hmatrix :
      (Matrix.of fun i j =>
        concreteMellinEvaluationMap rho (basisTest j) i) =
        (1 : Matrix
          CC20YoshidaInterpolationNode CC20YoshidaInterpolationNode ℂ) := by
    ext i j
    rw [Matrix.of_apply, hkronecker, Matrix.one_apply]
  rw [hmatrix]
  simp

theorem concreteMellinRealizesDesired_of_positive_interval_mellin_surjective
    {rho : ℂ}
    (hsurj : ∀ y : CC20YoshidaInterpolationNode → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        (∀ i : CC20YoshidaInterpolationNode,
          concreteMellinEvaluationMap rho g i = y i)) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteMellinRealizesDesired rho g := by
  classical
  choose basisTest lower upper hlower hcompact hsupp hvalue using
    fun j : CC20YoshidaInterpolationNode =>
      hsurj (fun i => if i = j then 1 else 0)
  exact concreteMellinRealizesDesired_of_kronecker_mellin_basis
    basisTest lower upper hcompact hlower hsupp
    (fun i j => hvalue j i)

end CC20YoshidaInterpolationNode
end Source
end ConnesWeilRH
