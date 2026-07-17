/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete.ContinuousKernelCompact
import ConnesWeilRH.Source.CC20Concrete.CompactConvolutionSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScalePlancherelKernel
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Unit-scale strict prolate angle

This module closes the strict-angle premise in the fixed-source prolate trace
reduction.  It first proves compact physical/Fourier support uniqueness for
the genuine additive-even Plancherel transform.  Compactness, self-adjointness,
and the absence of `+1` and `-1` fixed vectors then give a strict norm bound
for the literal finite Fourier compression.

The bound is transported to common-log coordinates and then to the actual
two-projection prolate factor.  The last transfer uses the leakage block
`L = (I-P) H (P-R)`, its Gram operator `I-C^2`, and the inverse of that Gram
operator.  No prolate eigenvalue, angle gap, or support-uniqueness conclusion
is stored as a premise.
-/

namespace ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction

open MeasureTheory
open Complex Module
open scoped ComplexConjugate FourierTransform
open CC20Concrete
open CC20Concrete.ProlateTraceReduction
open CC20Concrete.PositiveTrace
open CC20Concrete.ContinuousKernelHilbertSchmidt
open CC20Concrete.CompactConvolutionSupport
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24UnitScaleProlateAlignment
open CCM24SourceProlateTrace
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge

local notation "Jadd" => KernelInterval (-1) 1 0
local notation "Hadd" => ccm24EvenAdditiveL2
local notation "H" => finiteSCarrier
local notation "Hinf" => ccm24ArchimedeanHardyTitchmarsh
local notation "Hop" => archimedeanHardyTitchmarshOperator

noncomputable local instance : CompleteSpace Hadd :=
  ccm24EvenAdditiveClosedSubspace.isClosed.completeSpace_coe

theorem unitAdditiveIntervalFourierOperator_isCompactOperator :
    IsCompactOperator unitAdditiveIntervalFourierOperator := by
  exact operator_isCompactOperator
    (volume : Measure Jadd) (volume : Measure Jadd)
    unitAdditiveFourierKernel

theorem unitAdditiveFiniteWindowFourierFactor_isCompactOperator :
    IsCompactOperator unitAdditiveFiniteWindowFourierFactor := by
  have hinterval := unitAdditiveIntervalFourierOperator_isCompactOperator
  have hrestricted := hinterval.comp_clm
    (globalL2ToKernelInterval (-1) 1 0)
  exact hrestricted.clm_comp (kernelIntervalL2ZeroExtension (-1) 1 0)

theorem unitEvenAdditiveFiniteWindowFourierFactor_isCompactOperator :
    IsCompactOperator unitEvenAdditiveFiniteWindowFourierFactor := by
  have hglobal := unitAdditiveFiniteWindowFourierFactor_isCompactOperator
  have hrestricted := hglobal.comp_clm
    ccm24EvenAdditiveClosedSubspace.subtypeL
  exact hrestricted.clm_comp ccm24EvenSymmetrizationToEven

theorem unitEvenAdditiveFourierCompression_isCompactOperator :
    IsCompactOperator unitEvenAdditiveFourierCompression := by
  rw [unitEvenAdditiveFourierCompression_eq_finiteWindowFactor]
  exact unitEvenAdditiveFiniteWindowFourierFactor_isCompactOperator

theorem unitLiteralEvenAdditiveInteriorProjection_inner_symmetry
    (u v : Hadd) :
    inner ℂ (unitLiteralEvenAdditiveInteriorProjection u) v =
      inner ℂ u (unitLiteralEvenAdditiveInteriorProjection v) := by
  change inner ℂ
      (kernelIntervalProjection (-1) 1 0
        (u : cc20GlobalLogCrossingL2))
      (v : cc20GlobalLogCrossingL2) =
    inner ℂ (u : cc20GlobalLogCrossingL2)
      (kernelIntervalProjection (-1) 1 0
        (v : cc20GlobalLogCrossingL2))
  exact (kernelIntervalProjection_isSelfAdjoint (-1) 1).isSymmetric u v

theorem ccm24EvenAdditiveFourier_inner_symmetry
    (u v : Hadd) :
    inner ℂ (ccm24EvenAdditiveFourier u) v =
      inner ℂ u (ccm24EvenAdditiveFourier v) := by
  have hinvolutive (w : Hadd) :
      ccm24EvenAdditiveFourier (ccm24EvenAdditiveFourier w) = w := by
    change ccm24EvenAdditiveFourierLinearIsometry
      (ccm24EvenAdditiveFourierLinearIsometry w) = w
    exact ccm24EvenAdditiveFourierLinearIsometry_involutive w
  calc
    inner ℂ (ccm24EvenAdditiveFourier u) v =
        inner ℂ (ccm24EvenAdditiveFourier u)
          (ccm24EvenAdditiveFourier (ccm24EvenAdditiveFourier v)) := by
      rw [hinvolutive]
    _ = inner ℂ u (ccm24EvenAdditiveFourier v) :=
      ccm24EvenAdditiveFourier.inner_map_map u
        (ccm24EvenAdditiveFourier v)

theorem unitEvenAdditiveFourierCompression_inner_symmetry
    (u v : Hadd) :
    inner ℂ (unitEvenAdditiveFourierCompression u) v =
      inner ℂ u (unitEvenAdditiveFourierCompression v) := by
  rw [unitEvenAdditiveFourierCompression_eq_literalProjection]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    inner ℂ
        (unitLiteralEvenAdditiveInteriorProjection
          (ccm24EvenAdditiveFourier
            (unitLiteralEvenAdditiveInteriorProjection u))) v =
        inner ℂ
          (ccm24EvenAdditiveFourier
            (unitLiteralEvenAdditiveInteriorProjection u))
          (unitLiteralEvenAdditiveInteriorProjection v) :=
      unitLiteralEvenAdditiveInteriorProjection_inner_symmetry _ _
    _ = inner ℂ (unitLiteralEvenAdditiveInteriorProjection u)
          (ccm24EvenAdditiveFourier
            (unitLiteralEvenAdditiveInteriorProjection v)) :=
      ccm24EvenAdditiveFourier_inner_symmetry _ _
    _ = inner ℂ u
          (unitLiteralEvenAdditiveInteriorProjection
            (ccm24EvenAdditiveFourier
              (unitLiteralEvenAdditiveInteriorProjection v))) :=
      unitLiteralEvenAdditiveInteriorProjection_inner_symmetry _ _

theorem unitEvenAdditiveFourierCompression_isSelfAdjoint :
    IsSelfAdjoint unitEvenAdditiveFourierCompression := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  exact unitEvenAdditiveFourierCompression_inner_symmetry

theorem unitLiteralEvenAdditiveInteriorProjection_idempotent
    (u : Hadd) :
    unitLiteralEvenAdditiveInteriorProjection
        (unitLiteralEvenAdditiveInteriorProjection u) =
      unitLiteralEvenAdditiveInteriorProjection u := by
  apply Subtype.ext
  change kernelIntervalProjection (-1) 1 0
      (kernelIntervalProjection (-1) 1 0
        (u : cc20GlobalLogCrossingL2)) =
    kernelIntervalProjection (-1) 1 0
      (u : cc20GlobalLogCrossingL2)
  rw [unitKernelIntervalProjection_apply,
    unitKernelIntervalProjection_apply,
    globalL2ToKernelInterval_zeroExtension]

theorem unitLiteralEvenAdditiveInteriorProjection_isStarProjection :
    IsStarProjection unitLiteralEvenAdditiveInteriorProjection := by
  constructor
  · apply ContinuousLinearMap.ext
    exact unitLiteralEvenAdditiveInteriorProjection_idempotent
  · exact (LinearMap.IsSymmetric.isSelfAdjoint
      unitLiteralEvenAdditiveInteriorProjection_inner_symmetry)

theorem norm_unitLiteralEvenAdditiveInteriorProjection_le_one :
    ‖unitLiteralEvenAdditiveInteriorProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  let P := unitLiteralEvenAdditiveInteriorProjection
  have hinner : inner ℂ u (P u) = inner ℂ (P u) (P u) := by
    have hsym := unitLiteralEvenAdditiveInteriorProjection_inner_symmetry
      u (P u)
    rw [unitLiteralEvenAdditiveInteriorProjection_idempotent] at hsym
    exact hsym.symm
  have hsub := norm_sub_sq (𝕜 := ℂ) u (P u)
  rw [hinner, ← norm_sq_eq_re_inner] at hsub
  have hsquare : ‖P u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [sq_nonneg ‖u - P u‖]
  simpa [P] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

theorem norm_ccm24EvenAdditiveFourier_clm_le_one :
    ‖ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  exact ccm24EvenAdditiveFourier.norm_map u |>.le

theorem norm_unitEvenAdditiveFourierCompression_le_one :
    ‖unitEvenAdditiveFourierCompression‖ ≤ 1 := by
  rw [unitEvenAdditiveFourierCompression_eq_literalProjection]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [ContinuousLinearMap.comp_apply, one_mul]
  let P := unitLiteralEvenAdditiveInteriorProjection
  let F := ccm24EvenAdditiveFourier.toContinuousLinearEquiv.toContinuousLinearMap
  have hP : ‖P‖ ≤ 1 := norm_unitLiteralEvenAdditiveInteriorProjection_le_one
  have hF : ‖F‖ ≤ 1 := norm_ccm24EvenAdditiveFourier_clm_le_one
  calc
    ‖P (F (P u))‖ ≤ ‖P‖ * ‖F (P u)‖ := P.le_opNorm _
    _ ≤ 1 * ‖F (P u)‖ := by gcongr
    _ = ‖F (P u)‖ := one_mul _
    _ ≤ ‖F‖ * ‖P u‖ := F.le_opNorm _
    _ ≤ 1 * ‖P u‖ := by gcongr
    _ = ‖P u‖ := one_mul _
    _ ≤ ‖P‖ * ‖u‖ := P.le_opNorm _
    _ ≤ 1 * ‖u‖ := by gcongr
    _ = ‖u‖ := one_mul _

theorem unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq
    (u : Hadd)
    (hnorm : ‖unitLiteralEvenAdditiveInteriorProjection u‖ = ‖u‖) :
    unitLiteralEvenAdditiveInteriorProjection u = u := by
  let P := unitLiteralEvenAdditiveInteriorProjection
  have hinner : inner ℂ u (P u) = inner ℂ (P u) (P u) := by
    have hsym := unitLiteralEvenAdditiveInteriorProjection_inner_symmetry
      u (P u)
    rw [unitLiteralEvenAdditiveInteriorProjection_idempotent] at hsym
    exact hsym.symm
  have hsub := norm_sub_sq (𝕜 := ℂ) u (P u)
  rw [hinner, ← norm_sq_eq_re_inner] at hsub
  have hzero : ‖u - P u‖ ^ 2 = 0 := by
    rw [hsub, hnorm]
    ring
  have hnormZero : ‖u - P u‖ = 0 := (sq_eq_zero_iff).mp hzero
  have : u - P u = 0 := norm_eq_zero.mp hnormZero
  exact (sub_eq_zero.mp this).symm

theorem unitEvenAdditiveFourierCompression_fixed_supports
    (u : Hadd) (hu : unitEvenAdditiveFourierCompression u = u) :
    unitLiteralEvenAdditiveInteriorProjection u = u ∧
      unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u := by
  rw [unitEvenAdditiveFourierCompression_eq_literalProjection] at hu
  simp only [ContinuousLinearMap.comp_apply] at hu
  have hphysical : unitLiteralEvenAdditiveInteriorProjection u = u := by
    rw [← hu]
    exact unitLiteralEvenAdditiveInteriorProjection_idempotent _
  rw [hphysical] at hu
  have hnorm : ‖unitLiteralEvenAdditiveInteriorProjection
      (ccm24EvenAdditiveFourier u)‖ = ‖ccm24EvenAdditiveFourier u‖ := by
    calc
      ‖unitLiteralEvenAdditiveInteriorProjection
          (ccm24EvenAdditiveFourier u)‖ = ‖u‖ := congrArg norm hu
      _ = ‖ccm24EvenAdditiveFourier u‖ :=
        (ccm24EvenAdditiveFourier.norm_map u).symm
  exact ⟨hphysical,
    unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq _ hnorm⟩

theorem unitEvenAdditiveFourierCompression_negFixed_supports
    (u : Hadd) (hu : unitEvenAdditiveFourierCompression u = -u) :
    unitLiteralEvenAdditiveInteriorProjection u = u ∧
      unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u := by
  rw [unitEvenAdditiveFourierCompression_eq_literalProjection] at hu
  simp only [ContinuousLinearMap.comp_apply] at hu
  have hphysical : unitLiteralEvenAdditiveInteriorProjection u = u := by
    have hprojected := congrArg unitLiteralEvenAdditiveInteriorProjection hu
    rw [unitLiteralEvenAdditiveInteriorProjection_idempotent, map_neg] at hprojected
    exact neg_injective (hprojected.symm.trans hu)
  rw [hphysical] at hu
  have hnorm : ‖unitLiteralEvenAdditiveInteriorProjection
      (ccm24EvenAdditiveFourier u)‖ = ‖ccm24EvenAdditiveFourier u‖ := by
    calc
      ‖unitLiteralEvenAdditiveInteriorProjection
          (ccm24EvenAdditiveFourier u)‖ = ‖-u‖ := congrArg norm hu
      _ = ‖u‖ := norm_neg u
      _ = ‖ccm24EvenAdditiveFourier u‖ :=
        (ccm24EvenAdditiveFourier.norm_map u).symm
  exact ⟨hphysical,
    unitLiteralEvenAdditiveInteriorProjection_eq_of_norm_eq _ hnorm⟩

theorem norm_lt_one_of_compact_selfAdjoint_of_no_fixed_vectors_of_nontrivial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E]
    (T : E →L[ℂ] E)
    (hcompact : IsCompactOperator T)
    (hself : IsSelfAdjoint T)
    (hnorm : ‖T‖ ≤ 1)
    (hfixed : ∀ x, T x = x → x = 0)
    (hnegFixed : ∀ x, T x = -x → x = 0) :
    ‖T‖ < 1 := by
  by_contra hnot
  have hone : (1 : ℝ) ≤ ‖T‖ := le_of_not_gt hnot
  have hnormEq : ‖T‖ = 1 := le_antisymm hnorm hone
  have hspectrum : (spectrum ℂ T).Nonempty := spectrum.nonempty T
  obtain ⟨mu, hmuSpectrum, hmuRadius⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hspectrum
  have hmuNormNN : ‖mu‖₊ = ‖T‖₊ := by
    apply ENNReal.coe_injective
    rw [hmuRadius]
    exact T.spectralRadius_eq_nnnorm hself
  have hmuNorm : ‖mu‖ = 1 := by
    have hreal := congrArg (fun r : NNReal => (r : ℝ)) hmuNormNN
    simpa [hnormEq] using hreal
  have hmuNe : mu ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hmuNorm
    norm_num at hmuNorm
  have hmuEigen : Module.End.HasEigenvalue (T : Module.End ℂ E) mu :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hmuNe).2 hmuSpectrum
  have hmuConj : conj mu = mu :=
    hself.isSymmetric.conj_eigenvalue_eq_self hmuEigen
  have hmuIm : mu.im = 0 := by
    have him := congrArg Complex.im hmuConj
    simp only [Complex.conj_im] at him
    linarith
  have hmuReal : mu = (mu.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hmuIm]
  have hrealNorm : ‖(mu.re : ℂ)‖ = 1 := by
    rw [← hmuReal]
    exact hmuNorm
  have habs : |mu.re| = |(1 : ℝ)| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_one] using hrealNorm
  have hsquares : mu.re ^ 2 = (1 : ℝ) ^ 2 := by
    exact (sq_eq_sq_iff_abs_eq_abs mu.re 1).mpr habs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hpos | hneg
  · have hmueq : mu = 1 := by
      rw [hmuReal]
      exact_mod_cast hpos
    obtain ⟨x, hx, hxne⟩ := hmuEigen.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff, hmueq, one_smul] at hx
    exact hxne (hfixed x hx)
  · have hmueq : mu = -1 := by
      rw [hmuReal]
      exact_mod_cast hneg
    obtain ⟨x, hx, hxne⟩ := hmuEigen.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff, hmueq, neg_smul, one_smul] at hx
    exact hxne (hnegFixed x hx)

theorem norm_lt_one_of_compact_selfAdjoint_of_no_fixed_vectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (T : E →L[ℂ] E)
    (hcompact : IsCompactOperator T)
    (hself : IsSelfAdjoint T)
    (hnorm : ‖T‖ ≤ 1)
    (hfixed : ∀ x, T x = x → x = 0)
    (hnegFixed : ∀ x, T x = -x → x = 0) :
    ‖T‖ < 1 := by
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
      have hzero : T = 0 := by
        apply ContinuousLinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      simp [hzero]
  | inr hnontrivial =>
      letI := hnontrivial
      exact norm_lt_one_of_compact_selfAdjoint_of_no_fixed_vectors_of_nontrivial
        T hcompact hself hnorm hfixed hnegFixed

theorem norm_unitEvenAdditiveFourierCompression_lt_one_of_support_uniqueness
    (hunique : ∀ u : Hadd,
      unitLiteralEvenAdditiveInteriorProjection u = u →
      unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u →
      u = 0) :
    ‖unitEvenAdditiveFourierCompression‖ < 1 := by
  apply norm_lt_one_of_compact_selfAdjoint_of_no_fixed_vectors
    unitEvenAdditiveFourierCompression
    unitEvenAdditiveFourierCompression_isCompactOperator
    unitEvenAdditiveFourierCompression_isSelfAdjoint
    norm_unitEvenAdditiveFourierCompression_le_one
  · intro u hu
    exact hunique u
      (unitEvenAdditiveFourierCompression_fixed_supports u hu).1
      (unitEvenAdditiveFourierCompression_fixed_supports u hu).2
  · intro u hu
    exact hunique u
      (unitEvenAdditiveFourierCompression_negFixed_supports u hu).1
      (unitEvenAdditiveFourierCompression_negFixed_supports u hu).2

noncomputable local instance : CompactSpace Jadd := by
  unfold KernelInterval
  infer_instance

noncomputable def unitMonomialContinuous (n : ℕ) : C(Jadd, ℂ) :=
  ⟨fun x => (x.1 : ℂ) ^ n, by fun_prop⟩

@[simp] theorem unitMonomialContinuous_zero :
    unitMonomialContinuous 0 = 1 := by
  ext x
  simp [unitMonomialContinuous]

theorem unitMonomialContinuous_mul (m n : ℕ) :
    unitMonomialContinuous m * unitMonomialContinuous n =
      unitMonomialContinuous (m + n) := by
  ext x
  simp [unitMonomialContinuous, pow_add]

theorem star_unitMonomialContinuous (n : ℕ) :
    star (unitMonomialContinuous n) = unitMonomialContinuous n := by
  ext x
  change star ((x.1 : ℂ) ^ n) = (x.1 : ℂ) ^ n
  simp

noncomputable def unitMonomialStarSubalgebra :
    StarSubalgebra ℂ C(Jadd, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range unitMonomialContinuous)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range unitMonomialContinuous) ≤
      star (Algebra.adjoin ℂ (Set.range unitMonomialContinuous))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    exact Algebra.subset_adjoin ⟨n, (star_unitMonomialContinuous n).symm⟩

theorem unitMonomialStarSubalgebra_coe :
    unitMonomialStarSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range unitMonomialContinuous) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · exact unitMonomialContinuous_zero
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, (unitMonomialContinuous_mul m n).symm⟩

theorem unitMonomialStarSubalgebra_separatesPoints :
    unitMonomialStarSubalgebra.SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨unitMonomialContinuous 1,
    Algebra.subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  intro hvalue
  apply hxy
  apply Subtype.ext
  have hreal := congrArg Complex.re hvalue
  simpa [unitMonomialContinuous] using hreal

theorem span_unitMonomialContinuous_closure_eq_top :
    (Submodule.span ℂ
      (Set.range unitMonomialContinuous)).topologicalClosure = ⊤ := by
  rw [← unitMonomialStarSubalgebra_coe]
  exact congrArg
    (fun A : StarSubalgebra ℂ C(Jadd, ℂ) =>
      A.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      unitMonomialStarSubalgebra
      unitMonomialStarSubalgebra_separatesPoints)

noncomputable def unitMonomialRow (n : ℕ) :
    Lp ℂ 2 (volume : Measure Jadd) :=
  ContinuousMap.toLp 2 (volume : Measure Jadd) ℂ
    (unitMonomialContinuous n)

theorem span_unitMonomialRow_closure_eq_top :
    (Submodule.span ℂ
      (Set.range unitMonomialRow)).topologicalClosure = ⊤ := by
  have hp : (2 : ENNReal) ≠ ⊤ := by norm_num
  convert!
    (ContinuousMap.toLp_denseRange ℂ (volume : Measure Jadd) ℂ hp)
      |>.topologicalClosure_map_submodule
        span_unitMonomialContinuous_closure_eq_top
  rw [Submodule.map_span]
  unfold unitMonomialRow
  rw [Set.range_comp']
  simp only [ContinuousLinearMap.coe_coe]

theorem dense_span_unitMonomialRow :
    Dense (Submodule.span ℂ (Set.range unitMonomialRow) : Set
      (Lp ℂ 2 (volume : Measure Jadd))) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    span_unitMonomialRow_closure_eq_top

set_option maxHeartbeats 800000 in
-- The weak Plancherel calculation elaborates nested Fourier/Lp coercions.
theorem inner_fourierTransformL2_schwartz_eq_integral_fourier
    (g : ℝ → ℂ)
    (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume)
    (phi : SchwartzMap ℝ ℂ) :
    inner ℂ
        (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g))
        (phi.toLp 2) =
      ∫ xi : ℝ, inner ℂ (𝓕 g xi) (phi xi) ∂volume := by
  have hphiInv :
      (((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) : ℝ → ℂ) =ᵐ[volume]
        ((𝓕⁻ phi : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    have hvec :
        (Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2) =
          (𝓕⁻ phi : SchwartzMap ℝ ℂ).toLp 2 := by
      change 𝓕⁻ (phi.toLp 2) = (𝓕⁻ phi : SchwartzMap ℝ ℂ).toLp 2
      exact SchwartzMap.toLp_fourierInv_eq phi
    rw [hvec]
    exact (𝓕⁻ phi : SchwartzMap ℝ ℂ).coeFn_toLp 2 volume
  have hswap :
      (∫ xi : ℝ, inner ℂ (𝓕 g xi) (phi xi) ∂volume) =
        ∫ x : ℝ, inner ℂ (g x) ((𝓕⁻ phi : SchwartzMap ℝ ℂ) x)
          ∂volume := by
    simpa [SchwartzMap.fourierInv_coe] using
      (VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
        (μ := volume) (ν := volume) (L := innerₗ ℝ)
        (innerSL ℂ) Real.continuous_fourierChar continuous_inner
        hg1 phi.integrable)
  calc
    inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g))
        (phi.toLp 2) =
        inner ℂ (hg2.toLp g)
          ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) := by
      calc
        inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g))
            (phi.toLp 2) =
            inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (hg2.toLp g))
              (Lp.fourierTransformₗᵢ ℝ ℂ
                ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2))) := by
          rw [(Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply]
        _ = inner ℂ (hg2.toLp g)
              ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (phi.toLp 2)) :=
          (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map _ _
    _ = ∫ x : ℝ, inner ℂ (g x)
        ((𝓕⁻ phi : SchwartzMap ℝ ℂ) x) ∂volume := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp, hphiInv] with x hgAt hphiAt
      rw [hgAt, hphiAt]
    _ = ∫ xi : ℝ, inner ℂ (𝓕 g xi) (phi xi) ∂volume :=
      hswap.symm

noncomputable def unitSupportedRepresentative (u : Hadd) : ℝ → ℂ :=
  Set.Icc (-1 : ℝ) 1 |>.indicator
    (fun x => (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x)

theorem unitSupportedRepresentative_ae_eq
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u) :
    unitSupportedRepresentative u =ᵐ[volume]
      (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) := by
  have hprojection := kernelIntervalProjection_coeFn
    (-1) 1 0 ((u : Hadd) : cc20GlobalLogCrossingL2)
  have hfixed :
      (kernelIntervalProjection (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) =ᵐ[volume]
        (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) := by
    rw [← unitLiteralEvenAdditiveInteriorProjection_coe]
    rw [hphysical]
  simpa [unitSupportedRepresentative] using hprojection.symm.trans hfixed

theorem unitSupportedRepresentative_memLp_two (u : Hadd) :
    MemLp (unitSupportedRepresentative u) 2 volume := by
  unfold unitSupportedRepresentative
  exact (memLp_indicator_iff_restrict measurableSet_Icc).2
    ((Lp.memLp ((u : Hadd) : cc20GlobalLogCrossingL2)).mono_measure
      Measure.restrict_le_self)

theorem unitSupportedRepresentative_integrable (u : Hadd) :
    Integrable (unitSupportedRepresentative u) volume := by
  unfold unitSupportedRepresentative
  rw [integrable_indicator_iff measurableSet_Icc]
  exact ((Lp.memLp ((u : Hadd) : cc20GlobalLogCrossingL2)).mono_measure
    Measure.restrict_le_self).integrable (by norm_num)

theorem unitSupportedRepresentative_moment_integrable
    (u : Hadd) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • unitSupportedRepresentative u x)
      volume := by
  let scalar : ℝ → ℝ :=
    Set.Icc (-1 : ℝ) 1 |>.indicator (fun x => x ^ n)
  have hscalarMeasurable : AEStronglyMeasurable scalar volume := by
    exact ((measurable_id.pow_const n).indicator measurableSet_Icc)
      |>.aestronglyMeasurable
  have hscalarBound : ∀ᵐ x : ℝ ∂volume, ‖scalar x‖ ≤ 1 := by
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [show scalar x = x ^ n by simp [scalar, hx]]
      rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg x)
      simpa [Real.norm_eq_abs, abs_le] using hx
    · simp [scalar, hx]
  have hintegrable := (unitSupportedRepresentative_integrable u).bdd_smul
    1 hscalarMeasurable hscalarBound
  convert hintegrable using 1
  funext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · simp [scalar, unitSupportedRepresentative, hx]
  · simp [scalar, unitSupportedRepresentative, hx]

theorem unitSupportedRepresentative_toLp_eq
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u) :
    (unitSupportedRepresentative_memLp_two u).toLp
        (unitSupportedRepresentative u) =
      ((u : Hadd) : cc20GlobalLogCrossingL2) := by
  rw [Lp.ext_iff]
  exact (unitSupportedRepresentative_memLp_two u).coeFn_toLp.trans
    (unitSupportedRepresentative_ae_eq u hphysical)

theorem unitKernelIntervalProjection_schwartz_eq_zero_of_support_Ioi
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (1 : ℝ)) :
    kernelIntervalProjection (-1) 1 0 (phi.toLp 2) = 0 := by
  rw [Lp.ext_iff]
  have hprojection := kernelIntervalProjection_coeFn
    (-1) 1 0 (phi.toLp 2)
  have hphi := phi.coeFn_toLp 2 volume
  filter_upwards
    [hprojection, hphi, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with
      x hprojectionAt hphiAt hzeroAt
  rw [hprojectionAt, hzeroAt]
  simp only [sub_zero, add_zero]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx, hphiAt]
    by_contra hne
    have houter := hsupport hne
    exact (not_lt_of_ge hx.2) houter
  · rw [Set.indicator_of_notMem hx]
    rfl

set_option maxHeartbeats 800000 in
-- Reusing the weak Fourier bridge requires the same coercion budget.
theorem integral_inner_unitSupportedFourier_schwartz_eq_zero
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u)
    (phi : SchwartzMap ℝ ℂ)
    (hsupport : Function.support phi ⊆ Set.Ioi (1 : ℝ)) :
    (∫ xi : ℝ,
      inner ℂ (𝓕 (unitSupportedRepresentative u) xi) (phi xi)
        ∂volume) = 0 := by
  have hweak := inner_fourierTransformL2_schwartz_eq_integral_fourier
    (unitSupportedRepresentative u)
    (unitSupportedRepresentative_integrable u)
    (unitSupportedRepresentative_memLp_two u) phi
  rw [unitSupportedRepresentative_toLp_eq u hphysical] at hweak
  have hplancherel :
      Lp.fourierTransformₗᵢ ℝ ℂ
          ((u : Hadd) : cc20GlobalLogCrossingL2) =
        ((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2) := rfl
  rw [hplancherel] at hweak
  rw [← hweak]
  calc
    inner ℂ
        (((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2)) (phi.toLp 2) =
        inner ℂ
          (kernelIntervalProjection (-1) 1 0
            (((ccm24EvenAdditiveFourier u : Hadd) :
              cc20GlobalLogCrossingL2)))
          (phi.toLp 2) := by
      rw [← unitLiteralEvenAdditiveInteriorProjection_coe, hfourier]
    _ = inner ℂ
        (((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2))
        (kernelIntervalProjection (-1) 1 0 (phi.toLp 2)) :=
      (kernelIntervalProjection_isSelfAdjoint (-1) 1).isSymmetric
        (((ccm24EvenAdditiveFourier u : Hadd) :
          cc20GlobalLogCrossingL2)) (phi.toLp 2)
    _ = 0 := by
      rw [unitKernelIntervalProjection_schwartz_eq_zero_of_support_Ioi
        phi hsupport]
      simp

set_option maxHeartbeats 800000 in
-- Distributional support testing expands the smooth Schwartz conversion.
theorem unitSupportedFourier_eq_zero_on_Ioi
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u) :
    Set.EqOn (𝓕 (unitSupportedRepresentative u)) 0 (Set.Ioi (1 : ℝ)) := by
  let g := unitSupportedRepresentative u
  have hgIntegrable : Integrable g volume :=
    unitSupportedRepresentative_integrable u
  have hfourierContinuous : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hgIntegrable
  have hconjContinuous : Continuous (fun x => conj (𝓕 g x)) :=
    Complex.continuous_conj.comp hfourierContinuous
  have haeConj : ∀ᵐ x ∂volume,
      x ∈ Set.Ioi (1 : ℝ) → conj (𝓕 g x) = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hconjContinuous.locallyIntegrable.locallyIntegrableOn
        (Set.Ioi (1 : ℝ)))
    intro test htestDiff htestCompact htestSupport
    let testComplex : ℝ → ℂ := fun x => (test x : ℂ)
    have htestComplexDiff := Complex.ofRealCLM.contDiff.comp htestDiff
    have htestComplexCompact : HasCompactSupport testComplex := by
      exact htestCompact.comp_left (map_zero Complex.ofRealCLM)
    let phi : SchwartzMap ℝ ℂ :=
      htestComplexCompact.toSchwartzMap htestComplexDiff
    have hphiSupport : Function.support phi ⊆ Set.Ioi (1 : ℝ) := by
      intro x hx
      apply htestSupport
      apply subset_closure
      change test x ≠ 0
      intro hzero
      apply hx
      simp [phi, testComplex, hzero]
    have hzero := integral_inner_unitSupportedFourier_schwartz_eq_zero
      u hphysical hfourier phi hphiSupport
    simpa [g, phi, testComplex, RCLike.inner_apply,
      Complex.star_def, mul_comm] using hzero
  have haeConjRestrict :
      (fun x => conj (𝓕 g x)) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        (0 : ℝ → ℂ) := by
    filter_upwards [ae_restrict_of_ae haeConj,
      ae_restrict_mem measurableSet_Ioi] with x hzero hx
    exact hzero hx
  have hconjZero : Set.EqOn (fun x => conj (𝓕 g x)) 0
      (Set.Ioi (1 : ℝ)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq haeConjRestrict isOpen_Ioi
      hconjContinuous.continuousOn continuous_zero.continuousOn
  intro x hx
  have hxConj := hconjZero hx
  change conj (𝓕 g x) = 0 at hxConj
  have hxConjAgain := congrArg conj hxConj
  simpa using hxConjAgain

theorem unitSupportedFourier_iteratedDeriv_two_eq_zero
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u)
    (n : ℕ) :
    iteratedDeriv n (𝓕 (unitSupportedRepresentative u)) 2 = 0 := by
  have hzero := unitSupportedFourier_eq_zero_on_Ioi
    u hphysical hfourier
  have hwithin := iteratedDerivWithin_congr (n := n) hzero
    (show (2 : ℝ) ∈ Set.Ioi (1 : ℝ) by norm_num)
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi (by norm_num)] at hwithin
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi (by norm_num)] at hwithin
  simpa using hwithin

theorem unitSupportedFourier_moment_eq_zero
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u)
    (n : ℕ) :
    (∫ x : ℝ, (𝐞 (-(x * 2)) : ℂ) * (x : ℂ) ^ n *
      unitSupportedRepresentative u x ∂volume) = 0 := by
  let g := unitSupportedRepresentative u
  have hformula := congrFun
    (Real.iteratedDeriv_fourier
      (f := g) (N := ⊤)
      (fun k _ => unitSupportedRepresentative_moment_integrable u k)
      (n := n) le_top) 2
  have hderivZero : iteratedDeriv n (𝓕 g) 2 = 0 :=
    unitSupportedFourier_iteratedDeriv_two_eq_zero
      u hphysical hfourier n
  rw [hderivZero] at hformula
  have hraw :
      𝓕 (fun x : ℝ => (-2 * Real.pi * I * x) ^ n • g x) 2 = 0 :=
    hformula.symm
  rw [Real.fourier_eq] at hraw
  have hfactor :
      (∫ x : ℝ, 𝐞 (-inner ℝ x 2) •
          ((-2 * Real.pi * I * x) ^ n • g x) ∂volume) =
        (-2 * Real.pi * I) ^ n *
          ∫ x : ℝ, (𝐞 (-(x * 2)) : ℂ) * (x : ℂ) ^ n * g x
            ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def,
      smul_eq_mul, mul_pow]
    ring
  rw [hfactor] at hraw
  have hconstant : (-2 * Real.pi * I : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact (mul_eq_zero.mp hraw).resolve_left hconstant

noncomputable def unitMomentCharacterLInf :
    Lp ℂ ⊤ (volume : Measure Jadd) :=
  ContinuousMap.toLp ⊤ (volume : Measure Jadd) ℂ
    ⟨fun x => (𝐞 (x.1 * 2) : ℂ), by fun_prop⟩

noncomputable def unitMomentWitness (u : Hadd) :
    Lp ℂ 2 (volume : Measure Jadd) :=
  unitMomentCharacterLInf •
    star (globalL2ToKernelInterval (-1) 1 0
      ((u : Hadd) : cc20GlobalLogCrossingL2))

theorem unitMomentCharacterLInf_coeFn :
    (unitMomentCharacterLInf : Jadd → ℂ) =ᵐ[volume]
      fun x => (𝐞 (x.1 * 2) : ℂ) := by
  exact ContinuousMap.coeFn_toLp (p := ⊤)
    (volume : Measure Jadd)
    ⟨fun x => (𝐞 (x.1 * 2) : ℂ), by fun_prop⟩

theorem unitMomentWitness_coeFn (u : Hadd) :
    (unitMomentWitness u : Jadd → ℂ) =ᵐ[volume]
      fun x => (𝐞 (x.1 * 2) : ℂ) *
        conj ((globalL2ToKernelInterval (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2) : Jadd → ℂ) x) := by
  unfold unitMomentWitness
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) unitMomentCharacterLInf
      (star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2))),
      unitMomentCharacterLInf_coeFn,
      Lp.coeFn_star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2))] with x hmul hcharacter hstar
  rw [hmul]
  change (unitMomentCharacterLInf : Jadd → ℂ) x *
      ((star (globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2)) :
          Lp ℂ 2 (volume : Measure Jadd)) : Jadd → ℂ) x = _
  rw [hcharacter, hstar]
  rfl

theorem unitMonomialRow_coeFn (n : ℕ) :
    (unitMonomialRow n : Jadd → ℂ) =ᵐ[volume]
      fun x => (x.1 : ℂ) ^ n := by
  exact ContinuousMap.coeFn_toLp (p := 2)
    (volume : Measure Jadd) (unitMonomialContinuous n)

theorem unitMomentWitness_inner_unitMonomialRow
    (u : Hadd) (n : ℕ) :
    inner ℂ (unitMomentWitness u) (unitMonomialRow n) =
      ∫ x : ℝ, (𝐞 (-(x * 2)) : ℂ) * (x : ℂ) ^ n *
        unitSupportedRepresentative u x ∂volume := by
  rw [L2.inner_def]
  calc
    (∫ x : Jadd,
        inner ℂ ((unitMomentWitness u : Jadd → ℂ) x)
          ((unitMonomialRow n : Jadd → ℂ) x) ∂volume) =
        ∫ x : Jadd, (𝐞 (-(x.1 * 2)) : ℂ) *
          ((globalL2ToKernelInterval (-1) 1 0
            ((u : Hadd) : cc20GlobalLogCrossingL2) : Jadd → ℂ) x) *
          (x.1 : ℂ) ^ n ∂volume := by
      apply integral_congr_ae
      filter_upwards [unitMomentWitness_coeFn u,
        unitMonomialRow_coeFn n] with x hw hrow
      rw [hw, hrow]
      have hcharacterConj : conj (𝐞 (x.1 * 2) : ℂ) =
          (𝐞 (-(x.1 * 2)) : ℂ) := by
        simp only [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]
      simp only [RCLike.inner_apply, map_mul, hcharacterConj]
      rw [Complex.conj_conj]
      ring
    _ = ∫ x : ℝ, (𝐞 (-(x * 2)) : ℂ) * (x : ℂ) ^ n *
        unitSupportedRepresentative u x ∂volume := by
      have hrestricted := globalL2ToKernelInterval_coeFn
        (-1) 1 0 ((u : Hadd) : cc20GlobalLogCrossingL2)
      apply Eq.trans (integral_congr_ae (hrestricted.mono fun x hx => by
        rw [hx]))
      change (∫ x : Set.Icc (-1 - 0 : ℝ) (1 + 0),
          (𝐞 (-(x.1 * 2)) : ℂ) *
          (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x.1 *
          (x.1 : ℂ) ^ n ∂Measure.comap Subtype.val volume) = _
      rw [integral_subtype_comap (μ := (volume : Measure ℝ))
        measurableSet_Icc
        (fun x : ℝ => (𝐞 (-(x * 2)) : ℂ) *
          (((u : Hadd) : cc20GlobalLogCrossingL2) : ℝ → ℂ) x *
          (x : ℂ) ^ n)]
      unfold unitSupportedRepresentative
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hx]
        ring
      · simp [Set.indicator_of_notMem hx]

theorem unitMomentWitness_eq_zero_of_supports
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u) :
    unitMomentWitness u = 0 := by
  have hrows (n : ℕ) :
      inner ℂ (unitMomentWitness u) (unitMonomialRow n) = 0 := by
    rw [unitMomentWitness_inner_unitMonomialRow]
    exact unitSupportedFourier_moment_eq_zero
      u hphysical hfourier n
  have hspan : Submodule.span ℂ (Set.range unitMonomialRow) ≤
      (innerSL ℂ (unitMomentWitness u)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hrows n
  apply dense_span_unitMonomialRow.eq_zero_of_inner_left ℂ
  intro v hv
  exact hspan hv

theorem unitRestrictedVector_eq_zero_of_momentWitness_eq_zero
    (u : Hadd)
    (hwitness : unitMomentWitness u = 0) :
    globalL2ToKernelInterval (-1) 1 0
        ((u : Hadd) : cc20GlobalLogCrossingL2) = 0 := by
  rw [Lp.ext_iff]
  have hwitnessZero :
      (unitMomentWitness u : Jadd → ℂ) =ᵐ[volume]
        (0 : Lp ℂ 2 (volume : Measure Jadd)) := by
    rw [hwitness]
  filter_upwards [unitMomentWitness_coeFn u, hwitnessZero,
    Lp.coeFn_zero ℂ 2 (volume : Measure Jadd),
    Lp.coeFn_zero ℂ 2 (volume : Measure Jadd)] with
      x hw hzero hzeroWitness hzeroTarget
  rw [hzeroWitness] at hzero
  rw [hzeroTarget]
  rw [hw] at hzero
  have hcharacter : (𝐞 (x.1 * 2) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hconj := (mul_eq_zero.mp hzero).resolve_left hcharacter
  have hconjAgain := congrArg conj hconj
  simpa using hconjAgain

theorem unitCompactPhysicalFourierSupport_unique
    (u : Hadd)
    (hphysical : unitLiteralEvenAdditiveInteriorProjection u = u)
    (hfourier : unitLiteralEvenAdditiveInteriorProjection
        (ccm24EvenAdditiveFourier u) = ccm24EvenAdditiveFourier u) :
    u = 0 := by
  have hwitness := unitMomentWitness_eq_zero_of_supports
    u hphysical hfourier
  have hrestricted :=
    unitRestrictedVector_eq_zero_of_momentWitness_eq_zero u hwitness
  apply Subtype.ext
  change ((u : Hadd) : cc20GlobalLogCrossingL2) = 0
  calc
    ((u : Hadd) : cc20GlobalLogCrossingL2) =
        kernelIntervalProjection (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2) := by
      rw [← unitLiteralEvenAdditiveInteriorProjection_coe, hphysical]
    _ = kernelIntervalL2ZeroExtension (-1) 1 0
        (globalL2ToKernelInterval (-1) 1 0
          ((u : Hadd) : cc20GlobalLogCrossingL2)) :=
      unitKernelIntervalProjection_apply _
    _ = 0 := by rw [hrestricted]; simp

theorem norm_unitEvenAdditiveFourierCompression_lt_one :
    ‖unitEvenAdditiveFourierCompression‖ < 1 :=
  norm_unitEvenAdditiveFourierCompression_lt_one_of_support_uniqueness
    unitCompactPhysicalFourierSupport_unique

theorem norm_unitInteriorFourierCompression_eq_evenAdditive :
    ‖unitInteriorFourierCompression‖ =
      ‖unitEvenAdditiveFourierCompression‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _
      (M := ‖unitEvenAdditiveFourierCompression‖)
      (norm_nonneg unitEvenAdditiveFourierCompression) ?_
    intro x
    rw [unitInteriorFourierCompression_eq_evenAdditiveConjugation]
    simp only [ContinuousLinearMap.comp_apply]
    change ‖ccm24EvenLogCarrierEquiv
      (unitEvenAdditiveFourierCompression
        (ccm24EvenLogCarrierEquiv.symm x))‖ ≤ _
    rw [ccm24EvenLogCarrierEquiv.norm_map]
    calc
      ‖unitEvenAdditiveFourierCompression
          (ccm24EvenLogCarrierEquiv.symm x)‖ ≤
          ‖unitEvenAdditiveFourierCompression‖ *
            ‖ccm24EvenLogCarrierEquiv.symm x‖ :=
        unitEvenAdditiveFourierCompression.le_opNorm _
      _ = ‖unitEvenAdditiveFourierCompression‖ * ‖x‖ := by
        rw [ccm24EvenLogCarrierEquiv.symm.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _
      (M := ‖unitInteriorFourierCompression‖)
      (norm_nonneg unitInteriorFourierCompression) ?_
    intro u
    have hpoint :
        unitInteriorFourierCompression (ccm24EvenLogCarrierEquiv u) =
          ccm24EvenLogCarrierEquiv
            (unitEvenAdditiveFourierCompression u) := by
      rw [unitInteriorFourierCompression_eq_evenAdditiveConjugation]
      simp
    calc
      ‖unitEvenAdditiveFourierCompression u‖ =
          ‖ccm24EvenLogCarrierEquiv
            (unitEvenAdditiveFourierCompression u)‖ :=
        (ccm24EvenLogCarrierEquiv.norm_map _).symm
      _ = ‖unitInteriorFourierCompression
          (ccm24EvenLogCarrierEquiv u)‖ := congrArg norm hpoint.symm
      _ ≤ ‖unitInteriorFourierCompression‖ *
          ‖ccm24EvenLogCarrierEquiv u‖ :=
        unitInteriorFourierCompression.le_opNorm _
      _ = ‖unitInteriorFourierCompression‖ * ‖u‖ := by
        rw [ccm24EvenLogCarrierEquiv.norm_map]

theorem norm_unitInteriorFourierCompression_lt_one :
    ‖unitInteriorFourierCompression‖ < 1 := by
  rw [norm_unitInteriorFourierCompression_eq_evenAdditive]
  exact norm_unitEvenAdditiveFourierCompression_lt_one

noncomputable def unitInteriorSquaredComplement : H →L[ℂ] H :=
  1 - unitInteriorFourierCompression * unitInteriorFourierCompression

theorem unitInteriorCompression_sq_norm_lt_one :
    ‖unitInteriorFourierCompression * unitInteriorFourierCompression‖ < 1 := by
  calc
    ‖unitInteriorFourierCompression * unitInteriorFourierCompression‖ ≤
        ‖unitInteriorFourierCompression‖ ^ 2 := by
      simpa [pow_two] using norm_mul_le
        unitInteriorFourierCompression unitInteriorFourierCompression
    _ < 1 := by
      nlinarith [norm_unitInteriorFourierCompression_lt_one,
        norm_nonneg unitInteriorFourierCompression]

theorem unitInteriorSquaredComplement_isUnit :
    IsUnit unitInteriorSquaredComplement := by
  unfold unitInteriorSquaredComplement
  exact isUnit_one_sub_of_norm_lt_one
    unitInteriorCompression_sq_norm_lt_one

noncomputable def unitInteriorSquaredComplementInv : H →L[ℂ] H :=
  Ring.inverse unitInteriorSquaredComplement

theorem unitInteriorSquaredComplement_mul_inv :
    unitInteriorSquaredComplement * unitInteriorSquaredComplementInv = 1 := by
  exact Ring.mul_inverse_cancel _ unitInteriorSquaredComplement_isUnit

theorem unitInteriorSquaredComplement_inv_mul :
    unitInteriorSquaredComplementInv * unitInteriorSquaredComplement = 1 := by
  exact Ring.inverse_mul_cancel _ unitInteriorSquaredComplement_isUnit

noncomputable abbrev unitSoninProjection : H →L[ℂ] H :=
  cc20TransportedSoninProjection Hinf

theorem unitInterior_hardy_sonin_eq_zero :
    unitInteriorSupportProjection ∘L Hop ∘L unitSoninProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have htransported := DFunLike.congr_fun
    (cc20TransportedHalfLineProjection_comp_sonin Hinf) x
  rw [unitTransportedHalfLineProjection_eq_hardyConjugation] at htransported
  simp only [ContinuousLinearMap.comp_apply] at htransported
  have hpositive := congrArg Hop htransported
  rw [archimedeanHardyTitchmarshOperator_involutive] at hpositive
  unfold unitInteriorSupportProjection
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [hpositive]
  exact sub_self _

theorem unitSonin_hardy_interior_eq_zero :
    unitSoninProjection ∘L Hop ∘L unitInteriorSupportProjection = 0 := by
  have hInteriorSelf : IsSelfAdjoint unitInteriorSupportProjection :=
    (IsSelfAdjoint.one (H →L[ℂ] H)).sub
      cc20PositiveHalfLineProjection_isSelfAdjoint
  have hadjoint := congrArg ContinuousLinearMap.adjoint
    unitInterior_hardy_sonin_eq_zero
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp] at hadjoint
  rw [map_zero] at hadjoint
  rw [(cc20TransportedSoninProjection_isSelfAdjoint Hinf).adjoint_eq,
    archimedeanHardyTitchmarshOperator_isSelfAdjoint.adjoint_eq,
    hInteriorSelf.adjoint_eq] at hadjoint
  exact hadjoint

noncomputable abbrev unitSupportComplementProjection : H →L[ℂ] H :=
  supportComplementProjection Hinf

noncomputable def unitInteriorLeakage : H →L[ℂ] H :=
  unitInteriorSupportProjection ∘L Hop ∘L
    unitSupportComplementProjection

noncomputable def unitInteriorLeakageAdjointModel : H →L[ℂ] H :=
  unitSupportComplementProjection ∘L Hop ∘L
    unitInteriorSupportProjection

theorem unitInteriorSupportProjection_isIdempotentElem :
    IsIdempotentElem unitInteriorSupportProjection := by
  apply ContinuousLinearMap.ext
  intro x
  unfold unitInteriorSupportProjection
  simp only [ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [cc20PositiveHalfLineProjection_idempotent]
  abel

theorem hardyOperator_sq : Hop * Hop = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change Hop (Hop x) = x
  exact archimedeanHardyTitchmarshOperator_involutive x

theorem unitInteriorLeakage_mul_adjointModel :
    unitInteriorLeakage * unitInteriorLeakageAdjointModel =
      unitInteriorSupportProjection -
        unitInteriorFourierCompression * unitInteriorFourierCompression := by
  let I := unitInteriorSupportProjection
  let P := cc20PositiveHalfLineProjection
  let R := unitSoninProjection
  let B := unitSupportComplementProjection
  let C := unitInteriorFourierCompression
  have hBsq : B * B = B := supportComplementProjection_isIdempotentElem Hinf
  have hIsq : I * I = I := unitInteriorSupportProjection_isIdempotentElem
  have hHsq : Hop * Hop = 1 := hardyOperator_sq
  have hIHR : I * Hop * R = 0 := unitInterior_hardy_sonin_eq_zero
  have hP : P = 1 - I := by
    apply ContinuousLinearMap.ext
    intro x
    change P x = x - (x - P x)
    abel
  have hC : C = I * Hop * I := by rfl
  have hHH : I * Hop * Hop * I = I := by
    calc
      I * Hop * Hop * I = I * (Hop * Hop) * I := by noncomm_ring
      _ = I := by rw [hHsq, mul_one, hIsq]
  have hCsq : C * C = I * Hop * I * Hop * I := by
    rw [hC]
    calc
      (I * Hop * I) * (I * Hop * I) =
          I * Hop * (I * I) * Hop * I := by noncomm_ring
      _ = I * Hop * I * Hop * I := by rw [hIsq]
  calc
    unitInteriorLeakage * unitInteriorLeakageAdjointModel =
        I * Hop * (B * B) * Hop * I := by
      unfold unitInteriorLeakage unitInteriorLeakageAdjointModel
      rfl
    _ = I * Hop * B * Hop * I := by rw [hBsq]
    _ = I * Hop * (P - R) * Hop * I := by rfl
    _ = I * Hop * P * Hop * I := by
      calc
        I * Hop * (P - R) * Hop * I =
            I * Hop * P * Hop * I - I * Hop * R * Hop * I := by
          noncomm_ring
        _ = I * Hop * P * Hop * I := by rw [hIHR]; simp
    _ = I * Hop * (1 - I) * Hop * I := by rw [← hP]
    _ = I - C * C := by
      calc
        I * Hop * (1 - I) * Hop * I =
            I * Hop * Hop * I - I * Hop * I * Hop * I := by
          noncomm_ring
        _ = I - C * C := by rw [hHH, hCsq]

theorem unitInteriorSupportProjection_comp_compression :
    unitInteriorSupportProjection * unitInteriorFourierCompression =
      unitInteriorFourierCompression := by
  let I := unitInteriorSupportProjection
  have hIsq : I * I = I := unitInteriorSupportProjection_isIdempotentElem
  change I * (I * Hop * I) = I * Hop * I
  calc
    I * (I * Hop * I) = (I * I) * Hop * I := by noncomm_ring
    _ = I * Hop * I := by rw [hIsq]

theorem unitInteriorCompression_comp_supportProjection :
    unitInteriorFourierCompression * unitInteriorSupportProjection =
      unitInteriorFourierCompression := by
  let I := unitInteriorSupportProjection
  have hIsq : I * I = I := unitInteriorSupportProjection_isIdempotentElem
  change (I * Hop * I) * I = I * Hop * I
  rw [mul_assoc, hIsq]

theorem unitInteriorSquaredComplement_commute_interior :
    unitInteriorSquaredComplement * unitInteriorSupportProjection =
      unitInteriorSupportProjection * unitInteriorSquaredComplement := by
  let I := unitInteriorSupportProjection
  let C := unitInteriorFourierCompression
  have hIC : I * C = C :=
    unitInteriorSupportProjection_comp_compression
  have hCI : C * I = C :=
    unitInteriorCompression_comp_supportProjection
  unfold unitInteriorSquaredComplement
  calc
    (1 - C * C) * I = I - C * C := by
      rw [sub_mul, one_mul, mul_assoc, hCI]
    _ = I * (1 - C * C) := by
      rw [mul_sub, mul_one, ← mul_assoc, hIC]

theorem unitInteriorSquaredComplement_injective :
    Function.Injective unitInteriorSquaredComplement := by
  intro x y hxy
  have hcancelX := DFunLike.congr_fun
    unitInteriorSquaredComplement_inv_mul x
  have hcancelY := DFunLike.congr_fun
    unitInteriorSquaredComplement_inv_mul y
  change unitInteriorSquaredComplementInv
      (unitInteriorSquaredComplement x) = x at hcancelX
  change unitInteriorSquaredComplementInv
      (unitInteriorSquaredComplement y) = y at hcancelY
  calc
    x = unitInteriorSquaredComplementInv
        (unitInteriorSquaredComplement x) := hcancelX.symm
    _ = unitInteriorSquaredComplementInv
        (unitInteriorSquaredComplement y) := congrArg _ hxy
    _ = y := hcancelY

theorem unitInteriorSquaredComplementInv_preserves_interior
    (x : H) (hx : unitInteriorSupportProjection x = x) :
    unitInteriorSupportProjection (unitInteriorSquaredComplementInv x) =
      unitInteriorSquaredComplementInv x := by
  apply unitInteriorSquaredComplement_injective
  have hcomm := DFunLike.congr_fun
    unitInteriorSquaredComplement_commute_interior
    (unitInteriorSquaredComplementInv x)
  simp only [ContinuousLinearMap.mul_apply] at hcomm
  rw [hcomm]
  have hcancel := DFunLike.congr_fun
    unitInteriorSquaredComplement_mul_inv x
  change unitInteriorSquaredComplement
      (unitInteriorSquaredComplementInv x) = x at hcancel
  rw [hcancel, hx]

theorem positiveProjection_comp_unitSupportComplement :
    cc20PositiveHalfLineProjection * unitSupportComplementProjection =
      unitSupportComplementProjection := by
  let P := cc20PositiveHalfLineProjection
  let R := unitSoninProjection
  have hPsq : P * P = P :=
    cc20PositiveHalfLineProjection_isIdempotentElem
  have hPR : P * R = R :=
    cc20PositiveHalfLineProjection_comp_sonin Hinf
  change P * (P - R) = P - R
  rw [mul_sub, hPsq, hPR]

theorem unitSoninProjection_comp_unitSupportComplement :
    unitSoninProjection * unitSupportComplementProjection = 0 := by
  let P := cc20PositiveHalfLineProjection
  let R := unitSoninProjection
  have hRP : R * P = R :=
    cc20TransportedSonin_comp_positiveHalfLineProjection Hinf
  have hRsq : R * R = R :=
    (cc20TransportedSoninProjection_isStarProjection Hinf).isIdempotentElem
  change R * (P - R) = 0
  rw [mul_sub, hRP, hRsq, sub_self]

theorem unitInteriorLeakage_eq_zero_of_supportComplement_fixed
    (x : H) (hBx : unitSupportComplementProjection x = x)
    (hLx : unitInteriorLeakage x = 0) :
    x = 0 := by
  let P := cc20PositiveHalfLineProjection
  let Q := cc20TransportedHalfLineProjection Hinf
  let R := unitSoninProjection
  have hPx : P x = x := by
    calc
      P x = P (unitSupportComplementProjection x) :=
        congrArg P hBx.symm
      _ = x := by
        have hcomp := DFunLike.congr_fun
          positiveProjection_comp_unitSupportComplement x
        simp only [ContinuousLinearMap.mul_apply] at hcomp
        exact hcomp.trans hBx
  have hRxZero : R x = 0 := by
    calc
      R x = R (unitSupportComplementProjection x) :=
        congrArg R hBx.symm
      _ = 0 := by
        have hcomp := DFunLike.congr_fun
          unitSoninProjection_comp_unitSupportComplement x
        simpa only [ContinuousLinearMap.mul_apply] using hcomp
  have hPHx : P (Hop x) = Hop x := by
    unfold unitInteriorLeakage at hLx
    simp only [ContinuousLinearMap.comp_apply, hBx] at hLx
    unfold unitInteriorSupportProjection at hLx
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] at hLx
    exact (sub_eq_zero.mp hLx).symm
  have hQx : Q x = x := by
    rw [show Q = Hop ∘L P ∘L Hop from
      unitTransportedHalfLineProjection_eq_hardyConjugation]
    simp only [ContinuousLinearMap.comp_apply, hPHx]
    exact archimedeanHardyTitchmarshOperator_involutive x
  have hmemP : x ∈ cc20PositiveHalfLineClosedRange := by
    change x ∈ P.range
    exact (mem_range_iff_of_isIdempotentElem P
      cc20PositiveHalfLineProjection_isIdempotentElem x).2 hPx
  have hmemQ : x ∈ cc20TransportedHalfLineClosedRange Hinf := by
    change x ∈ Q.range
    exact (mem_range_iff_of_isIdempotentElem Q
      (cc20TransportedHalfLineProjection_isIdempotentElem Hinf) x).2 hQx
  have hRx : R x = x := by
    exact Submodule.starProjection_eq_self_iff.mpr ⟨hmemP, hmemQ⟩
  rw [hRxZero] at hRx
  exact hRx.symm

theorem unitInteriorSupportProjection_comp_leakage :
    unitInteriorSupportProjection * unitInteriorLeakage =
      unitInteriorLeakage := by
  let I := unitInteriorSupportProjection
  have hIsq : I * I = I := unitInteriorSupportProjection_isIdempotentElem
  unfold unitInteriorLeakage
  change I * (I * Hop * unitSupportComplementProjection) =
    I * Hop * unitSupportComplementProjection
  calc
    I * (I * Hop * unitSupportComplementProjection) =
        (I * I) * Hop * unitSupportComplementProjection := by noncomm_ring
    _ = I * Hop * unitSupportComplementProjection := by rw [hIsq]

theorem unitSupportComplement_comp_leakageAdjointModel :
    unitSupportComplementProjection * unitInteriorLeakageAdjointModel =
      unitInteriorLeakageAdjointModel := by
  let B := unitSupportComplementProjection
  have hBsq : B * B = B := supportComplementProjection_isIdempotentElem Hinf
  unfold unitInteriorLeakageAdjointModel
  change B * (B * Hop * unitInteriorSupportProjection) =
    B * Hop * unitInteriorSupportProjection
  calc
    B * (B * Hop * unitInteriorSupportProjection) =
        (B * B) * Hop * unitInteriorSupportProjection := by noncomm_ring
    _ = B * Hop * unitInteriorSupportProjection := by rw [hBsq]

theorem unitSupportComplement_reconstruction
    (x : H) (hBx : unitSupportComplementProjection x = x) :
    unitInteriorLeakageAdjointModel
        (unitInteriorSquaredComplementInv (unitInteriorLeakage x)) = x := by
  let z := unitInteriorSquaredComplementInv (unitInteriorLeakage x)
  have hLInterior : unitInteriorSupportProjection (unitInteriorLeakage x) =
      unitInteriorLeakage x := by
    have hcomp := DFunLike.congr_fun
      unitInteriorSupportProjection_comp_leakage x
    simpa only [ContinuousLinearMap.mul_apply] using hcomp
  have hzInterior : unitInteriorSupportProjection z = z :=
    unitInteriorSquaredComplementInv_preserves_interior
      (unitInteriorLeakage x) hLInterior
  have hMz : unitInteriorSquaredComplement z = unitInteriorLeakage x := by
    exact DFunLike.congr_fun unitInteriorSquaredComplement_mul_inv
      (unitInteriorLeakage x)
  have hLeakageSame : unitInteriorLeakage
      (unitInteriorLeakageAdjointModel z) = unitInteriorLeakage x := by
    have hgram := DFunLike.congr_fun
      unitInteriorLeakage_mul_adjointModel z
    simp only [ContinuousLinearMap.mul_apply] at hgram
    rw [hgram]
    unfold unitInteriorSquaredComplement at hMz
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply] at hMz
    change unitInteriorSupportProjection z -
      unitInteriorFourierCompression (unitInteriorFourierCompression z) = _
    rw [hzInterior]
    exact hMz
  let d := unitInteriorLeakageAdjointModel z - x
  have hdB : unitSupportComplementProjection d = d := by
    unfold d
    rw [map_sub, hBx]
    have hcomp := DFunLike.congr_fun
      unitSupportComplement_comp_leakageAdjointModel z
    simp only [ContinuousLinearMap.mul_apply] at hcomp
    rw [hcomp]
  have hdL : unitInteriorLeakage d = 0 := by
    unfold d
    rw [map_sub, hLeakageSame, sub_self]
  have hdZero := unitInteriorLeakage_eq_zero_of_supportComplement_fixed
    d hdB hdL
  exact sub_eq_zero.mp hdZero

noncomputable def unitLeakageReconstructionBound : ℝ :=
  max 1 (‖unitInteriorLeakageAdjointModel‖ *
    ‖unitInteriorSquaredComplementInv‖)

theorem unitLeakageReconstructionBound_one_le :
    1 ≤ unitLeakageReconstructionBound := by
  exact le_max_left _ _

theorem unitLeakageReconstructionBound_pos :
    0 < unitLeakageReconstructionBound :=
  lt_of_lt_of_le zero_lt_one unitLeakageReconstructionBound_one_le

theorem norm_le_unitLeakageReconstructionBound_mul_leakage
    (x : H) (hBx : unitSupportComplementProjection x = x) :
    ‖x‖ ≤ unitLeakageReconstructionBound * ‖unitInteriorLeakage x‖ := by
  calc
    ‖x‖ = ‖unitInteriorLeakageAdjointModel
        (unitInteriorSquaredComplementInv (unitInteriorLeakage x))‖ :=
      congrArg norm (unitSupportComplement_reconstruction x hBx).symm
    _ ≤ ‖unitInteriorLeakageAdjointModel‖ *
          ‖unitInteriorSquaredComplementInv (unitInteriorLeakage x)‖ :=
      unitInteriorLeakageAdjointModel.le_opNorm _
    _ ≤ ‖unitInteriorLeakageAdjointModel‖ *
        (‖unitInteriorSquaredComplementInv‖ * ‖unitInteriorLeakage x‖) := by
      gcongr
      exact unitInteriorSquaredComplementInv.le_opNorm _
    _ = (‖unitInteriorLeakageAdjointModel‖ *
        ‖unitInteriorSquaredComplementInv‖) * ‖unitInteriorLeakage x‖ := by
      ring
    _ ≤ unitLeakageReconstructionBound * ‖unitInteriorLeakage x‖ := by
      gcongr
      exact le_max_right _ _

theorem unitProlateFactor_leakage_norm_sq :
    ∀ x : H,
      ‖unitProlateFactor x‖ ^ 2 + ‖unitInteriorLeakage x‖ ^ 2 =
        ‖unitSupportComplementProjection x‖ ^ 2 := by
  intro x
  let b := unitSupportComplementProjection x
  let y := Hop b
  have hpyth := cc20PositiveHalfLineClosedRange.toSubmodule
    |>.norm_sq_eq_add_norm_sq_starProjection y
  rw [← cc20PositiveHalfLineProjection_eq_starProjection] at hpyth
  rw [Submodule.starProjection_orthogonal,
    ← cc20PositiveHalfLineProjection_eq_starProjection] at hpyth
  have hyNorm : ‖y‖ = ‖b‖ := by
    exact ccm24ArchimedeanHardyTitchmarsh.norm_map b
  have hprolateNorm :
      ‖unitProlateFactor x‖ =
        ‖cc20PositiveHalfLineProjection y‖ := by
    unfold unitProlateFactor prolateFactor
    rw [unitTransportedHalfLineProjection_eq_hardyConjugation]
    simp only [ContinuousLinearMap.comp_apply]
    change ‖Hinf (cc20PositiveHalfLineProjection (Hinf b))‖ = _
    rw [ccm24ArchimedeanHardyTitchmarsh.norm_map]
    change ‖cc20PositiveHalfLineProjection (Hinf b)‖ =
      ‖cc20PositiveHalfLineProjection (Hinf b)‖
    rfl
  have hleakage : unitInteriorLeakage x =
      (ContinuousLinearMap.id ℂ H -
        cc20PositiveHalfLineProjection) y := by
    rfl
  rw [hprolateNorm, hleakage, ← hyNorm]
  exact hpyth.symm

noncomputable def unitLeakageLowerBound : ℝ :=
  unitLeakageReconstructionBound⁻¹

theorem unitLeakageLowerBound_pos : 0 < unitLeakageLowerBound := by
  exact inv_pos.mpr unitLeakageReconstructionBound_pos

theorem unitLeakageLowerBound_le_one : unitLeakageLowerBound ≤ 1 := by
  exact inv_le_one_of_one_le₀ unitLeakageReconstructionBound_one_le

noncomputable def unitProlateAngleBound : ℝ :=
  Real.sqrt (1 - unitLeakageLowerBound ^ 2)

theorem unitProlateAngleBound_nonneg : 0 ≤ unitProlateAngleBound :=
  Real.sqrt_nonneg _

theorem unitProlateAngleBound_lt_one : unitProlateAngleBound < 1 := by
  have hdeltaPos := unitLeakageLowerBound_pos
  have hdeltaLe := unitLeakageLowerBound_le_one
  have hinside : 0 ≤ 1 - unitLeakageLowerBound ^ 2 := by
    nlinarith
  have hsqrt := Real.sq_sqrt hinside
  have hsqrtNonneg := unitProlateAngleBound_nonneg
  unfold unitProlateAngleBound at hsqrtNonneg ⊢
  nlinarith

theorem unitLeakageLowerBound_mul_norm_le
    (x : H) (hBx : unitSupportComplementProjection x = x) :
    unitLeakageLowerBound * ‖x‖ ≤ ‖unitInteriorLeakage x‖ := by
  have hbound := norm_le_unitLeakageReconstructionBound_mul_leakage x hBx
  unfold unitLeakageLowerBound
  rw [inv_mul_le_iff₀ unitLeakageReconstructionBound_pos]
  simpa [mul_assoc] using hbound

theorem norm_unitSupportComplementProjection_apply_le (x : H) :
    ‖unitSupportComplementProjection x‖ ≤ ‖x‖ := by
  calc
    ‖unitSupportComplementProjection x‖ ≤
        ‖unitSupportComplementProjection‖ * ‖x‖ :=
      unitSupportComplementProjection.le_opNorm x
    _ ≤ 1 * ‖x‖ := by
      gcongr
      exact (supportComplementProjection_isStarProjection Hinf).norm_le
    _ = ‖x‖ := one_mul _

theorem norm_unitProlateFactor_apply_le_angleBound (x : H) :
    ‖unitProlateFactor x‖ ≤ unitProlateAngleBound * ‖x‖ := by
  let b := unitSupportComplementProjection x
  have hBfixed : unitSupportComplementProjection b = b := by
    exact DFunLike.congr_fun
      (supportComplementProjection_isIdempotentElem Hinf) x
  have hlower := unitLeakageLowerBound_mul_norm_le b hBfixed
  have hleakageSame : unitInteriorLeakage b = unitInteriorLeakage x := by
    unfold unitInteriorLeakage
    simp only [ContinuousLinearMap.comp_apply]
    rw [hBfixed]
  rw [hleakageSame] at hlower
  have hpyth := unitProlateFactor_leakage_norm_sq x
  have hlowerSq :
      (unitLeakageLowerBound * ‖b‖) ^ 2 ≤
        ‖unitInteriorLeakage x‖ ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg unitLeakageLowerBound_pos.le (norm_nonneg _))
      (norm_nonneg _)).2 hlower
  have hdeltaLe := unitLeakageLowerBound_le_one
  have hinside : 0 ≤ 1 - unitLeakageLowerBound ^ 2 := by
    nlinarith [unitLeakageLowerBound_pos]
  have hbNorm := norm_unitSupportComplementProjection_apply_le x
  have hbSq : ‖b‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hbNorm
  have hangleSq :
      ‖unitProlateFactor x‖ ^ 2 ≤
        (1 - unitLeakageLowerBound ^ 2) * ‖x‖ ^ 2 := by
    dsimp only [b] at hpyth hlowerSq hbSq ⊢
    nlinarith
  have hsqrtSq := Real.sq_sqrt hinside
  have hrightNonneg : 0 ≤ unitProlateAngleBound * ‖x‖ :=
    mul_nonneg unitProlateAngleBound_nonneg (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hrightNonneg).mp
  unfold unitProlateAngleBound
  nlinarith

theorem norm_unitProlateFactor_lt_one : ‖unitProlateFactor‖ < 1 := by
  have hnorm : ‖unitProlateFactor‖ ≤ unitProlateAngleBound := by
    apply ContinuousLinearMap.opNorm_le_bound _ unitProlateAngleBound_nonneg
    intro x
    exact norm_unitProlateFactor_apply_le_angleBound x
  exact lt_of_le_of_lt hnorm unitProlateAngleBound_lt_one

/-- The actual unit-scale source prolate remainder has an unconditional
positive trace-class owner along every named Hilbert basis. -/
theorem sourceProlateRemainder_unit_isTraceClassAlong
    {ι : Type*} (basis : HilbertBasis ι ℂ H) :
    IsTraceClassAlong basis (sourceProlateRemainder unitSoninScale) := by
  exact sourceProlateRemainder_unit_isTraceClassAlong_of_rawCrossing
    basis norm_unitProlateFactor_lt_one
      (unitRawSupportCrossing_summable_of_additiveKernelIdentification basis)

/-- The fixed-source prolate square root is unconditionally
Hilbert--Schmidt along every named Hilbert basis. -/
theorem sourceProlateHilbertSchmidtFactor_unit_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ H) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor unitSoninScale (basis i)‖ ^ 2 := by
  exact sourceProlateHilbertSchmidtFactor_unit_summable_of_rawCrossing
    basis norm_unitProlateFactor_lt_one
      (unitRawSupportCrossing_summable_of_additiveKernelIdentification basis)

/-- The complete unit-scale source three-branch commutator has an
unconditional trace-class owner.  This is the fixed source endpoint only;
it does not assert trace legality for the moving finite-S path. -/
theorem sourceThreeBranchCommutator_unit_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure
        (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ H) :
    IsTraceClassAlong globalBasis
      (cc20ThreeBranchCommutator
        (radialSupportProjection unitSoninScale)
        (sourceFourierSupportProjection unitSoninScale)
        (sourceProlateRemainder unitSoninScale)
        (detectorOperator owner)) := by
  exact sourceThreeBranchCommutator_isTraceClassAlong owner unitSoninScale
    a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis)

end ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
