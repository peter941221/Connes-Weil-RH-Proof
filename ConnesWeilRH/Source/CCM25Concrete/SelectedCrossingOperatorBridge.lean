/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import ConnesWeilRH.Source.CC20Concrete.GlobalConvolutionCrossing
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingKernel

/-!
# Identify the compact crossing coefficient with Schwartz convolution

The finite kernel operator is first identified on restricted Schwartz inputs.
This is the dense-core equality needed before transporting `pairData` to the
whole-line convolution/crossing composition.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace SelectedCrossingOperatorBridge

open MeasureTheory
open scoped ComplexConjugate Convolution FourierTransform
open scoped InnerProductSpace
open ConnesWeilRH.Source.CC20Concrete
open SelectedCrossingKernel

noncomputable def kernelRestriction
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ) :
    ContinuousMap (KernelInterval a c b) ℂ where
  toFun t := u t.1
  continuous_toFun := u.continuous.comp continuous_subtype_val

noncomputable def sourceRestriction
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    ContinuousMap (SourceInterval b) ℂ where
  toFun s := u s.1
  continuous_toFun := u.continuous.comp continuous_subtype_val

noncomputable def shiftedSourceRestriction
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    ContinuousMap (SourceInterval b) ℂ where
  toFun s := u (s.1 - b)
  continuous_toFun := u.continuous.comp
    (continuous_subtype_val.sub continuous_const)

theorem measurePreserving_kernelIntervalSubtypeVal
    (a c b : ℝ) :
    MeasurePreserving
      (Subtype.val : KernelInterval a c b → ℝ)
      (volume : Measure (KernelInterval a c b))
      (volume.restrict (Set.Icc (a - b) (c + b))) := by
  exact measurePreserving_subtype_coe
    (μa := volume) measurableSet_Icc

noncomputable def kernelIntervalSubtypeValL2Isometry
    (a c b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b))) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  Lp.compMeasurePreservingₗᵢ ℂ Subtype.val
    (measurePreserving_kernelIntervalSubtypeVal a c b)

theorem surjective_kernelIntervalSubtypeValL2Isometry
    (a c b : ℝ) :
    Function.Surjective (kernelIntervalSubtypeValL2Isometry a c b) := by
  intro u
  let huMem : MemLp (u : KernelInterval a c b → ℂ) 2
      (volume : Measure (KernelInterval a c b)) := Lp.memLp u
  let g : KernelInterval a c b → ℂ :=
    huMem.aestronglyMeasurable.mk u
  have hgStrong : StronglyMeasurable g :=
    huMem.aestronglyMeasurable.stronglyMeasurable_mk
  obtain ⟨f, hfStrong, hcomp⟩ :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).exists_stronglyMeasurable_extend
      hgStrong (fun _ => ⟨0⟩)
  have hgMem : MemLp g 2 (volume : Measure (KernelInterval a c b)) :=
    (memLp_congr_ae huMem.aestronglyMeasurable.ae_eq_mk).mp huMem
  have hfMapMem : MemLp f 2
      (Measure.map (Subtype.val : KernelInterval a c b → ℝ)
        (volume : Measure (KernelInterval a c b))) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).memLp_map_measure_iff.mpr
      (by simpa only [hcomp] using hgMem)
  have hfMem : MemLp f 2
      (volume.restrict (Set.Icc (a - b) (c + b))) := by
    simpa only [(measurePreserving_kernelIntervalSubtypeVal a c b).map_eq]
      using hfMapMem
  refine ⟨hfMem.toLp f, ?_⟩
  change Lp.compMeasurePreserving Subtype.val
      (measurePreserving_kernelIntervalSubtypeVal a c b)
      (hfMem.toLp f) = u
  rw [Lp.toLp_compMeasurePreserving]
  calc
    _ = huMem.toLp (u : KernelInterval a c b → ℂ) := by
      apply MemLp.toLp_congr
      rw [hcomp]
      exact huMem.aestronglyMeasurable.ae_eq_mk.symm
    _ = u := Lp.toLp_coeFn u huMem

noncomputable def kernelIntervalSubtypeRestrictedL2IsometryEquiv
    (a c b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  LinearIsometryEquiv.ofSurjective
    (kernelIntervalSubtypeValL2Isometry a c b)
    (surjective_kernelIntervalSubtypeValL2Isometry a c b)

theorem surjective_globalL2RestrictionToSet
    (a c b : ℝ) :
    Function.Surjective
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (a - b) (c + b))) := by
  intro u
  let window := Set.Icc (a - b) (c + b)
  let extended : ℝ → ℂ := window.indicator fun t => u t
  have hextended : MemLp extended 2 volume := by
    exact (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)
  refine ⟨hextended.toLp extended, ?_⟩
  rw [Lp.ext_iff]
  have hrestrict := LpToLpRestrictCLM_coeFn ℂ window
    (hextended.toLp extended)
  have htoLp := ae_restrict_of_ae (s := window) hextended.coeFn_toLp
  have hmem : ∀ᵐ t ∂(volume.restrict window), t ∈ window :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hrestrict, htoLp, hmem] with t hr he hm
  rw [hr, he]
  change window.indicator (fun t => (u : ℝ → ℂ) t) t = (u : ℝ → ℂ) t
  rw [Set.indicator_of_mem hm]

noncomputable def restrictedSetZeroExtensionLinearMap
    (s : Set ℝ) (hs : MeasurableSet s) :
    Lp ℂ 2 (volume.restrict s) →ₗ[ℂ] cc20GlobalLogCrossingL2 where
  toFun u :=
    ((memLp_indicator_iff_restrict hs).2 (Lp.memLp u)).toLp
      (s.indicator fun t => u t)
  map_add' u v := by
    let hu := (memLp_indicator_iff_restrict hs).2 (Lp.memLp u)
    let hv := (memLp_indicator_iff_restrict hs).2 (Lp.memLp v)
    let huv := (memLp_indicator_iff_restrict hs).2 (Lp.memLp (u + v))
    apply MemLp.toLp_congr huv (hu.add hv)
    refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
    · filter_upwards [Lp.coeFn_add u v, ae_restrict_mem hs] with t hsum ht
      simp only [Set.indicator_of_mem ht, Pi.add_apply]
      simpa only [Pi.add_apply] using hsum
    · filter_upwards [ae_restrict_mem hs.compl] with t ht
      have hnot : t ∉ s := ht
      simp [Set.indicator, hnot]
  map_smul' z u := by
    let hu := (memLp_indicator_iff_restrict hs).2 (Lp.memLp u)
    let hzu := (memLp_indicator_iff_restrict hs).2 (Lp.memLp (z • u))
    apply MemLp.toLp_congr hzu (hu.const_smul z)
    refine ae_of_ae_restrict_of_ae_restrict_compl s ?_ ?_
    · filter_upwards [Lp.coeFn_smul z u, ae_restrict_mem hs] with t hsmul ht
      simp only [Set.indicator_of_mem ht, Pi.smul_apply]
      simpa only [Pi.smul_apply] using hsmul
    · filter_upwards [ae_restrict_mem hs.compl] with t ht
      have hnot : t ∉ s := ht
      simp [Set.indicator, hnot]

theorem norm_restrictedSetZeroExtensionLinearMap
    (s : Set ℝ) (hs : MeasurableSet s)
    (u : Lp ℂ 2 (volume.restrict s)) :
    ‖restrictedSetZeroExtensionLinearMap s hs u‖ = ‖u‖ := by
  change ‖((memLp_indicator_iff_restrict hs).2 (Lp.memLp u)).toLp
      (s.indicator fun t => u t)‖ = ‖u‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]

noncomputable def restrictedSetZeroExtension
    (s : Set ℝ) (hs : MeasurableSet s) :
    Lp ℂ 2 (volume.restrict s) →L[ℂ] cc20GlobalLogCrossingL2 :=
  LinearMap.mkContinuous (restrictedSetZeroExtensionLinearMap s hs) 1
    (fun u => by
      rw [one_mul, norm_restrictedSetZeroExtensionLinearMap s hs])

theorem norm_restrictedSetZeroExtension_apply
    (s : Set ℝ) (hs : MeasurableSet s)
    (u : Lp ℂ 2 (volume.restrict s)) :
    ‖restrictedSetZeroExtension s hs u‖ = ‖u‖ := by
  exact norm_restrictedSetZeroExtensionLinearMap s hs u

theorem restrictedSetZeroExtension_coeFn
    (s : Set ℝ) (hs : MeasurableSet s)
    (u : Lp ℂ 2 (volume.restrict s)) :
    (restrictedSetZeroExtension s hs u : ℝ → ℂ) =ᵐ[volume]
      s.indicator (fun t => u t) := by
  let h : MemLp (s.indicator fun t => u t) 2 volume :=
    (memLp_indicator_iff_restrict hs).2 (Lp.memLp u)
  change (h.toLp (s.indicator fun t => u t) : ℝ → ℂ) =ᵐ[volume]
    s.indicator (fun t => u t)
  exact h.coeFn_toLp

theorem restrict_restrictedSetZeroExtension
    (s : Set ℝ) (hs : MeasurableSet s)
    (u : Lp ℂ 2 (volume.restrict s)) :
    LpToLpRestrictCLM ℝ ℂ ℂ volume 2 s
        (restrictedSetZeroExtension s hs u) = u := by
  rw [Lp.ext_iff]
  have hrestrict := LpToLpRestrictCLM_coeFn ℂ s
    (restrictedSetZeroExtension s hs u)
  have hextend := ae_restrict_of_ae (s := s)
    (restrictedSetZeroExtension_coeFn s hs u)
  have hmem : ∀ᵐ t ∂(volume.restrict s), t ∈ s :=
    ae_restrict_mem hs
  filter_upwards [hrestrict, hextend, hmem] with t hr he hm
  rw [hr, he]
  simp only [Set.indicator_of_mem hm]

theorem restrictedSetZeroExtension_eq_adjoint_restrict
    (s : Set ℝ) (hs : MeasurableSet s) :
    restrictedSetZeroExtension s hs =
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 s).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [L2.inner_def, L2.inner_def]
  rw [← integral_indicator hs]
  have hextend := restrictedSetZeroExtension_coeFn s hs u
  have hrestrict := LpToLpRestrictCLM_coeFn ℂ s v
  have hrestrict' := (ae_restrict_iff' hs).mp hrestrict
  apply integral_congr_ae
  filter_upwards [hextend, hrestrict'] with t he hr
  by_cases ht : t ∈ s
  · rw [he]
    simp only [Set.indicator_of_mem ht]
    rw [hr ht]
  · rw [he]
    simp only [Set.indicator_of_notMem ht]
    simp

noncomputable def kernelIntervalRestrictedZeroExtensionLinearMap
    (a c b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b))) →ₗ[ℂ]
      cc20GlobalLogCrossingL2 where
  toFun u :=
    ((memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)).toLp
      ((Set.Icc (a - b) (c + b)).indicator fun t => u t)
  map_add' u v := by
    let hu := (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)
    let hv := (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp v)
    let huv := (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp (u + v))
    apply MemLp.toLp_congr huv (hu.add hv)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      (Set.Icc (a - b) (c + b)) ?_ ?_
    · filter_upwards
        [Lp.coeFn_add u v, ae_restrict_mem measurableSet_Icc] with t hsum ht
      simp only [Set.indicator_of_mem ht, Pi.add_apply]
      simpa only [Pi.add_apply] using hsum
    · filter_upwards
        [ae_restrict_mem measurableSet_Icc.compl] with t ht
      have hnot : t ∉ Set.Icc (a - b) (c + b) := ht
      simp [Set.indicator, hnot]
  map_smul' z u := by
    let hu := (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)
    let hzu := (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp (z • u))
    apply MemLp.toLp_congr hzu (hu.const_smul z)
    refine ae_of_ae_restrict_of_ae_restrict_compl
      (Set.Icc (a - b) (c + b)) ?_ ?_
    · filter_upwards
        [Lp.coeFn_smul z u, ae_restrict_mem measurableSet_Icc] with t hsmul ht
      simp only [Set.indicator_of_mem ht, Pi.smul_apply]
      simpa only [Pi.smul_apply] using hsmul
    · filter_upwards
        [ae_restrict_mem measurableSet_Icc.compl] with t ht
      have hnot : t ∉ Set.Icc (a - b) (c + b) := ht
      simp [Set.indicator, hnot]

theorem norm_kernelIntervalRestrictedZeroExtensionLinearMap
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b)))) :
    ‖kernelIntervalRestrictedZeroExtensionLinearMap a c b u‖ = ‖u‖ := by
  change ‖((memLp_indicator_iff_restrict measurableSet_Icc).2
      (Lp.memLp u)).toLp
        ((Set.Icc (a - b) (c + b)).indicator fun t => u t)‖ = ‖u‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]

noncomputable def kernelIntervalRestrictedZeroExtension
    (a c b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b))) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  LinearMap.mkContinuous
    (kernelIntervalRestrictedZeroExtensionLinearMap a c b) 1
    (fun u => by
      rw [one_mul, norm_kernelIntervalRestrictedZeroExtensionLinearMap])

theorem norm_kernelIntervalRestrictedZeroExtension_apply
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b)))) :
    ‖kernelIntervalRestrictedZeroExtension a c b u‖ = ‖u‖ := by
  change ‖kernelIntervalRestrictedZeroExtensionLinearMap a c b u‖ = ‖u‖
  exact norm_kernelIntervalRestrictedZeroExtensionLinearMap a c b u

theorem kernelIntervalRestrictedZeroExtension_coeFn
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b)))) :
    (kernelIntervalRestrictedZeroExtension a c b u : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (a - b) (c + b)).indicator (fun t => u t) := by
  let h : MemLp
      ((Set.Icc (a - b) (c + b)).indicator fun t => u t) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).2 (Lp.memLp u)
  change (h.toLp
        ((Set.Icc (a - b) (c + b)).indicator fun t => u t) : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (a - b) (c + b)).indicator (fun t => u t)
  exact h.coeFn_toLp

theorem restrict_kernelIntervalRestrictedZeroExtension
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume.restrict (Set.Icc (a - b) (c + b)))) :
    LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Icc (a - b) (c + b))
        (kernelIntervalRestrictedZeroExtension a c b u) = u := by
  rw [Lp.ext_iff]
  have hrestrict := LpToLpRestrictCLM_coeFn ℂ
    (Set.Icc (a - b) (c + b))
    (kernelIntervalRestrictedZeroExtension a c b u)
  have hextend := ae_restrict_of_ae (s := Set.Icc (a - b) (c + b))
    (kernelIntervalRestrictedZeroExtension_coeFn a c b u)
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Icc (a - b) (c + b))),
      t ∈ Set.Icc (a - b) (c + b) := ae_restrict_mem measurableSet_Icc
  filter_upwards [hrestrict, hextend, hmem] with t hr he hm
  rw [hr, he]
  simp only [Set.indicator_of_mem hm]

noncomputable def globalL2ToKernelInterval
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  ((kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (a - b) (c + b)))

theorem surjective_globalL2ToKernelInterval
    (a c b : ℝ) :
    Function.Surjective (globalL2ToKernelInterval a c b) := by
  simpa only [globalL2ToKernelInterval, ContinuousLinearMap.coe_comp',
    Function.comp_apply] using
      (kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).surjective.comp
        (surjective_globalL2RestrictionToSet a c b)

noncomputable def kernelIntervalL2ZeroExtension
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (KernelInterval a c b)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  (kernelIntervalRestrictedZeroExtension a c b).comp
    (kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem norm_kernelIntervalL2ZeroExtension
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (KernelInterval a c b))) :
    ‖kernelIntervalL2ZeroExtension a c b u‖ = ‖u‖ := by
  rw [kernelIntervalL2ZeroExtension, ContinuousLinearMap.comp_apply]
  rw [norm_kernelIntervalRestrictedZeroExtension_apply]
  exact (kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).symm.norm_map u

theorem globalL2ToKernelInterval_zeroExtension
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (KernelInterval a c b))) :
    globalL2ToKernelInterval a c b
        (kernelIntervalL2ZeroExtension a c b u) = u := by
  rw [globalL2ToKernelInterval, kernelIntervalL2ZeroExtension]
  simp only [ContinuousLinearMap.comp_apply]
  rw [restrict_kernelIntervalRestrictedZeroExtension]
  exact (kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).apply_symm_apply u

theorem measurePreserving_sourceIntervalSubtypeVal
    (b : ℝ) :
    MeasurePreserving
      (Subtype.val : SourceInterval b → ℝ)
      (volume : Measure (SourceInterval b))
      (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  exact measurePreserving_subtype_coe measurableSet_Icc

noncomputable def sourceIntervalSubtypeValL2Isometry
    (b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) b)) →ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  Lp.compMeasurePreservingₗᵢ ℂ Subtype.val
    (measurePreserving_sourceIntervalSubtypeVal b)

theorem surjective_sourceIntervalSubtypeValL2Isometry
    (b : ℝ) :
    Function.Surjective (sourceIntervalSubtypeValL2Isometry b) := by
  intro u
  let huMem : MemLp (u : SourceInterval b → ℂ) 2
      (volume : Measure (SourceInterval b)) := Lp.memLp u
  let g : SourceInterval b → ℂ := huMem.aestronglyMeasurable.mk u
  have hgStrong : StronglyMeasurable g :=
    huMem.aestronglyMeasurable.stronglyMeasurable_mk
  obtain ⟨f, hfStrong, hcomp⟩ :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).exists_stronglyMeasurable_extend
      hgStrong (fun _ => ⟨0⟩)
  have hgMem : MemLp g 2 (volume : Measure (SourceInterval b)) :=
    (memLp_congr_ae huMem.aestronglyMeasurable.ae_eq_mk).mp huMem
  have hfMapMem : MemLp f 2
      (Measure.map (Subtype.val : SourceInterval b → ℝ)
        (volume : Measure (SourceInterval b))) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).memLp_map_measure_iff.mpr
      (by simpa only [hcomp] using hgMem)
  have hfMem : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
    simpa only [(measurePreserving_sourceIntervalSubtypeVal b).map_eq]
      using hfMapMem
  refine ⟨hfMem.toLp f, ?_⟩
  change Lp.compMeasurePreserving Subtype.val
      (measurePreserving_sourceIntervalSubtypeVal b) (hfMem.toLp f) = u
  rw [Lp.toLp_compMeasurePreserving]
  calc
    _ = huMem.toLp (u : SourceInterval b → ℂ) := by
      apply MemLp.toLp_congr
      rw [hcomp]
      exact huMem.aestronglyMeasurable.ae_eq_mk.symm
    _ = u := Lp.toLp_coeFn u huMem

noncomputable def sourceIntervalSubtypeRestrictedL2IsometryEquiv
    (b : ℝ) :
    Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) b)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  LinearIsometryEquiv.ofSurjective
    (sourceIntervalSubtypeValL2Isometry b)
    (surjective_sourceIntervalSubtypeValL2Isometry b)

noncomputable def globalL2ToSourceInterval
    (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (sourceIntervalSubtypeRestrictedL2IsometryEquiv b).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Icc (0 : ℝ) b))

theorem globalL2ToSourceInterval_apply_schwartzToLp
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    globalL2ToSourceInterval b (u.toLp 2) =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (sourceRestriction u b) := by
  change sourceIntervalSubtypeValL2Isometry b
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (0 : ℝ) b) (u.toLp 2)) = _
  change Lp.compMeasurePreserving Subtype.val
      (measurePreserving_sourceIntervalSubtypeVal b)
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (0 : ℝ) b) (u.toLp 2)) = _
  rw [Lp.ext_iff]
  let restricted := LpToLpRestrictCLM ℝ ℂ ℂ volume 2
    (Set.Icc (0 : ℝ) b) (u.toLp 2)
  have hleft := Lp.coeFn_compMeasurePreserving restricted
    (measurePreserving_sourceIntervalSubtypeVal b)
  have hrestrict :=
    (measurePreserving_sourceIntervalSubtypeVal b).quasiMeasurePreserving.ae_eq_comp
      (LpToLpRestrictCLM_coeFn ℂ (Set.Icc (0 : ℝ) b) (u.toLp 2))
  have hschwartz :=
    (measurePreserving_sourceIntervalSubtypeVal b).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := Set.Icc (0 : ℝ) b)
        (u.coeFn_toLp 2 (volume : Measure ℝ)))
  have hright := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (volume : Measure (SourceInterval b))
    (𝕜 := ℂ) (sourceRestriction u b)
  filter_upwards [hleft, hrestrict, hschwartz, hright] with t hl hr hs ht
  rw [hl, hr, hs, ht]
  rfl

theorem globalL2ToKernelInterval_apply_schwartzToLp
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ) :
    globalL2ToKernelInterval a c b (u.toLp 2) =
      ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b) := by
  change kernelIntervalSubtypeValL2Isometry a c b
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (a - b) (c + b)) (u.toLp 2)) = _
  change Lp.compMeasurePreserving Subtype.val
      (measurePreserving_kernelIntervalSubtypeVal a c b)
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2
        (Set.Icc (a - b) (c + b)) (u.toLp 2)) = _
  rw [Lp.ext_iff]
  let restricted := LpToLpRestrictCLM ℝ ℂ ℂ volume 2
    (Set.Icc (a - b) (c + b)) (u.toLp 2)
  have hleft := Lp.coeFn_compMeasurePreserving restricted
    (measurePreserving_kernelIntervalSubtypeVal a c b)
  have hrestrict :=
    (measurePreserving_kernelIntervalSubtypeVal a c b).quasiMeasurePreserving.ae_eq_comp
      (LpToLpRestrictCLM_coeFn ℂ (Set.Icc (a - b) (c + b)) (u.toLp 2))
  have hschwartz :=
    (measurePreserving_kernelIntervalSubtypeVal a c b).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (s := Set.Icc (a - b) (c + b))
        (u.coeFn_toLp 2 (volume : Measure ℝ)))
  have hright := ContinuousMap.coeFn_toLp
    (p := (2 : ENNReal)) (volume : Measure (KernelInterval a c b))
    (𝕜 := ℂ) (kernelRestriction u a c b)
  filter_upwards [hleft, hrestrict, hschwartz, hright] with t hl hr hs ht
  rw [hl, hr, hs, ht]
  rfl

theorem denseRange_globalL2ToKernelInterval_schwartz
    (a c b : ℝ) :
    DenseRange (fun u : SchwartzMap ℝ ℂ =>
      globalL2ToKernelInterval a c b (u.toLp 2)) := by
  have hglobal : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hrestrict : DenseRange (globalL2ToKernelInterval a c b) :=
    (surjective_globalL2ToKernelInterval a c b).denseRange
  simpa only [Function.comp_apply] using
    hrestrict.comp hglobal (globalL2ToKernelInterval a c b).continuous

theorem denseRange_kernelRestriction_toLp
    (a c b : ℝ) :
    DenseRange (fun u : SchwartzMap ℝ ℂ =>
      ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b)) := by
  simpa only [globalL2ToKernelInterval_apply_schwartzToLp] using
    denseRange_globalL2ToKernelInterval_schwartz a c b

theorem rightCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t in Set.Icc (a - b) (c + b),
        u t * star (g.test (t - s.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (rightKernel g.test g.test.continuous a c b) s))
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ t : KernelInterval a c b,
      u t.1 * star (g.test (t.1 - s.1))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc (fun t : ℝ => u t * star (g.test (t - s.1)))

theorem rightCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t : ℝ, u t * star (g.test (t - s.1)) := by
  rw [rightCoefficient_kernelRestriction_eq_setIntegral]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [Set.indicator_of_mem ht]
  · have hgt : g.test (t - s.1) = 0 := by
      by_contra hne
      have hmem := hg (by simpa [Function.mem_support] using hne)
      have hb : 0 ≤ b := le_trans s.2.1 s.2.2
      exact ht ⟨by linarith [hmem.1, s.2.1],
        by linarith [hmem.2, s.2.2]⟩
    simp [Set.indicator, ht, hgt]

theorem rightCoefficient_kernelRestriction_eq_schwartzConvolution
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        u g.involution.test s.1 := by
  rw [rightCoefficient_kernelRestriction_eq_fullIntegral g u a c b hg s]
  let B := ContinuousLinearMap.mul ℂ ℂ
  calc
    (∫ t : ℝ, u t * star (g.test (t - s.1))) =
        (u ⋆[B] g.involution.test) s.1 := by
      rw [MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      rw [CompactLogConvolution.CompactLogTest.involution_apply]
      congr 2
      ring
    _ = SchwartzMap.convolution B
        u g.involution.test s.1 :=
      (SchwartzMap.convolution_apply
        B u g.involution.test s.1).symm

theorem schwartzConvolution_mul_real_eq_complex
    (u v : SchwartzMap ℝ ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v := by
  apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v) =
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v)
  rw [SchwartzMap.fourier_convolution, SchwartzMap.fourier_convolution]
  ext x
  rfl

theorem schwartzConvolution_mul_real_comm
    (u v : SchwartzMap ℝ ℂ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) v u := by
  have hflip : (ContinuousLinearMap.mul ℝ ℂ).flip =
      ContinuousLinearMap.mul ℝ ℂ := by
    ext x y
    exact mul_comm y x
  calc
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) u v =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ).flip v u :=
      (SchwartzMap.convolution_flip
        (ContinuousLinearMap.mul ℝ ℂ) u v).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) v u := by
      rw [hflip]

theorem schwartzConvolution_eq_on_source_of_eqOn_kernel
    (g : CompactLogConvolution.CompactLogTest)
    (u v : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (huv : ∀ t ∈ Set.Icc (a - b) (c + b), u t = v t)
    (s : SourceInterval b) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        u g.involution.test s.1 =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        v g.involution.test s.1 := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hconv (w : SchwartzMap ℝ ℂ) :
      SchwartzMap.convolution B w g.involution.test s.1 =
        ∫ t : ℝ, w t * star (g.test (t - s.1)) := by
    calc
      SchwartzMap.convolution B w g.involution.test s.1 =
          (w ⋆[B] g.involution.test) s.1 :=
        SchwartzMap.convolution_apply B w g.involution.test s.1
      _ = ∫ t : ℝ, w t * star (g.test (t - s.1)) := by
        rw [MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with t
        rw [CompactLogConvolution.CompactLogTest.involution_apply]
        simp only [B, ContinuousLinearMap.mul_apply']
        congr 2
        ring
  rw [hconv u, hconv v]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [huv t ht]
  · have hzero : g.test (t - s.1) = 0 := by
      by_contra hne
      have hmem := hg (by simpa [Function.mem_support] using hne)
      have hb : 0 ≤ b := le_trans s.2.1 s.2.2
      exact ht ⟨by linarith [hmem.1, s.2.1],
        by linarith [hmem.2, s.2.2]⟩
    simp [hzero]

theorem globalConvolutionCore_eq_on_source_of_eqOn_kernel
    (g : CompactLogConvolution.CompactLogTest)
    (u v : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (huv : ∀ t ∈ Set.Icc (a - b) (c + b), u t = v t)
    (s : SourceInterval b) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u s.1 =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test v s.1 := by
  have hlocal := schwartzConvolution_eq_on_source_of_eqOn_kernel
    g u v a c b hg huv s
  calc
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u s.1 =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          u g.involution.test s.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
        (schwartzConvolution_mul_real_comm g.involution.test u)
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        u g.involution.test s.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
        (schwartzConvolution_mul_real_eq_complex u g.involution.test)
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        v g.involution.test s.1 := hlocal
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        v g.involution.test s.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
        (schwartzConvolution_mul_real_eq_complex v g.involution.test).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test v s.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
        (schwartzConvolution_mul_real_comm v g.involution.test)

theorem rightCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u s.1 := by
  rw [rightCoefficient_kernelRestriction_eq_schwartzConvolution
    g u a c b hg s]
  rw [← schwartzConvolution_mul_real_eq_complex]
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f s.1)
    (schwartzConvolution_mul_real_comm u g.involution.test)

theorem rightCoefficient_kernelRestriction_eq_sourceRestriction
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      sourceRestriction
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u) b := by
  ext s
  exact rightCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c b hg s

theorem rightOperator_kernelRestriction_eq_sourceConvolutionToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (sourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  rw [rightCoefficient_kernelRestriction_eq_sourceRestriction g u a c b hg]

noncomputable def rightKernelCoreInputLinearMap
    (a c b : ℝ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  (globalL2ToKernelInterval a c b).toLinearMap.comp
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

noncomputable def rightGlobalConvolutionCoreLinearMap
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).toLinearMap.comp
    ((cc20GlobalLogConvolution g.involution.test).toLinearMap.comp
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap)

theorem rightKernelCoreInputLinearMap_apply
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ) :
    rightKernelCoreInputLinearMap a c b u =
      ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b) := by
  change globalL2ToKernelInterval a c b (u.toLp 2) = _
  exact globalL2ToKernelInterval_apply_schwartzToLp u a c b

theorem rightGlobalConvolutionCoreLinearMap_apply
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    rightGlobalConvolutionCoreLinearMap g b u =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (sourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [rightGlobalConvolutionCoreLinearMap, LinearMap.comp_apply,
    LinearMap.comp_apply]
  rw [← globalL2ToSourceInterval_apply_schwartzToLp
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
      g.involution.test u) b]
  apply congrArg (globalL2ToSourceInterval b)
  change cc20GlobalLogConvolution g.involution.test (u.toLp 2) = _
  exact cc20GlobalLogConvolution_toLp g.involution.test u

theorem rightKernelOperator_comp_coreInput_eq_globalCore
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel g.test g.test.continuous a c b)).toLinearMap.comp
        (rightKernelCoreInputLinearMap a c b) =
      rightGlobalConvolutionCoreLinearMap g b := by
  apply LinearMap.ext
  intro u
  change ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel g.test g.test.continuous a c b)
        (rightKernelCoreInputLinearMap a c b u) =
    rightGlobalConvolutionCoreLinearMap g b u
  rw [rightKernelCoreInputLinearMap_apply]
  rw [rightOperator_kernelRestriction_eq_sourceConvolutionToLp
    g u a c b hg]
  exact (rightGlobalConvolutionCoreLinearMap_apply g u b).symm

theorem rightKernelOperator_is_unique_bounded_core_extension
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    (rightGlobalConvolutionCoreLinearMap g b).extendOfNorm
        (rightKernelCoreInputLinearMap a c b) =
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b) := by
  let T := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (rightKernel g.test g.test.continuous a c b)
  have hdense : DenseRange (rightKernelCoreInputLinearMap a c b) := by
    have hfun : (rightKernelCoreInputLinearMap a c b :
        SchwartzMap ℝ ℂ →
          Lp ℂ 2 (volume : Measure (KernelInterval a c b))) =
        fun u => ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b) := by
      funext u
      exact rightKernelCoreInputLinearMap_apply u a c b
    rw [hfun]
    exact denseRange_kernelRestriction_toLp a c b
  have hnorm : ∀ u, ‖rightGlobalConvolutionCoreLinearMap g b u‖ ≤
      ‖T‖ * ‖rightKernelCoreInputLinearMap a c b u‖ := by
    intro u
    rw [← rightKernelOperator_comp_coreInput_eq_globalCore g a c b hg]
    exact T.le_opNorm _
  apply LinearMap.extendOfNorm_unique hdense ‖T‖ hnorm T
  simpa only [T] using
    rightKernelOperator_comp_coreInput_eq_globalCore g a c b hg

noncomputable def rightKernelGlobalRestrictionOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel g.test g.test.continuous a c b)).comp
        (globalL2ToKernelInterval a c b)

noncomputable def rightGlobalConvolutionSourceOperator
    (g : CompactLogConvolution.CompactLogTest)
    (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).comp
    (cc20GlobalLogConvolution g.involution.test)

theorem rightKernelGlobalRestrictionOperator_apply
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) (u : cc20GlobalLogCrossingL2) :
    rightKernelGlobalRestrictionOperator g a c b u =
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b)
          (globalL2ToKernelInterval a c b u) := by
  rfl

theorem rightGlobalConvolutionSourceOperator_apply
    (g : CompactLogConvolution.CompactLogTest)
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    rightGlobalConvolutionSourceOperator g b u =
      globalL2ToSourceInterval b
        (cc20GlobalLogConvolution g.involution.test u) := by
  rfl

theorem rightKernelGlobalRestrictionOperator_eq_globalConvolution
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    rightKernelGlobalRestrictionOperator g a c b =
      rightGlobalConvolutionSourceOperator g b := by
  have hglobal : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (rightKernelGlobalRestrictionOperator g a c b :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (SourceInterval b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
        (rightGlobalConvolutionSourceOperator g b :
          cc20GlobalLogCrossingL2 →
            Lp ℂ 2 (volume : Measure (SourceInterval b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    rw [Function.comp_apply, Function.comp_apply]
    rw [rightKernelGlobalRestrictionOperator_apply,
      rightGlobalConvolutionSourceOperator_apply]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [rightOperator_kernelRestriction_eq_sourceConvolutionToLp
      g u a c b hg]
    rw [cc20GlobalLogConvolution_toLp]
    exact (globalL2ToSourceInterval_apply_schwartzToLp
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u) b).symm
  have hfun := DenseRange.equalizer hglobal
    (rightKernelGlobalRestrictionOperator g a c b).continuous
    (rightGlobalConvolutionSourceOperator g b).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

theorem rightKernelOperator_eq_globalConvolution_zeroExtension
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b) =
      (rightGlobalConvolutionSourceOperator g b).comp
        (kernelIntervalL2ZeroExtension a c b) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [← rightKernelGlobalRestrictionOperator_eq_globalConvolution
    g a c b hg]
  rw [ContinuousLinearMap.comp_apply]
  rw [rightKernelGlobalRestrictionOperator_apply]
  rw [globalL2ToKernelInterval_zeroExtension]

noncomputable def leftKernelGlobalRestrictionOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.test g.test.continuous a c b)).comp
    (globalL2ToKernelInterval a c b)

noncomputable def leftGlobalTranslatedConvolutionSourceOperator
    (g : CompactLogConvolution.CompactLogTest)
    (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).comp
    ((cc20GlobalLogConvolution g.involution.test).comp
      (cc20GlobalLogTranslation (-b)).toContinuousLinearMap)

theorem cc20GlobalLogTranslation_neg_apply_schwartzToLp
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    cc20GlobalLogTranslation (-b) (u.toLp 2) =
      (SchwartzMap.compSubConstCLM ℂ b u).toLp 2 := by
  rw [Lp.ext_iff]
  filter_upwards
    [cc20GlobalLogTranslation_coeFn (-b) (u.toLp 2),
      (measurePreserving_add_right volume (-b)).quasiMeasurePreserving.ae_eq_comp
        (u.coeFn_toLp 2 (volume : Measure ℝ)),
      (SchwartzMap.compSubConstCLM ℂ b u).coeFn_toLp
        2 (volume : Measure ℝ)] with t htranslation hu hshift
  have hu' : (u.toLp 2 : ℝ → ℂ) (t + -b) = u (t + -b) := by
    simpa only [Function.comp_apply] using hu
  rw [htranslation, hu', hshift]
  rfl

theorem leftKernelGlobalRestrictionOperator_apply
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) (u : cc20GlobalLogCrossingL2) :
    leftKernelGlobalRestrictionOperator g a c b u =
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b)
          (globalL2ToKernelInterval a c b u) := by
  rfl

theorem leftGlobalTranslatedConvolutionSourceOperator_apply
    (g : CompactLogConvolution.CompactLogTest)
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    leftGlobalTranslatedConvolutionSourceOperator g b u =
      globalL2ToSourceInterval b
        (cc20GlobalLogConvolution g.involution.test
          (cc20GlobalLogTranslation (-b) u)) := by
  rfl

noncomputable def leftGlobalConvolutionCoreLinearMap
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).toLinearMap.comp
    ((cc20GlobalLogConvolution g.involution.test).toLinearMap.comp
      ((SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp
        (SchwartzMap.compSubConstCLM ℂ b).toLinearMap))

noncomputable def kernelCompressedGlobalConvolutionCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (KernelInterval a c b)) →L[ℂ]
  Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  (kernelIntervalL2ZeroExtension a c b).adjoint ∘L
    ((cc20GlobalConvolutionCrossing g.involution.test b) ∘L
      kernelIntervalL2ZeroExtension a c b)

theorem kernelCompressedGlobalConvolutionCrossing_apply
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (KernelInterval a c b))) :
    kernelCompressedGlobalConvolutionCrossing g a c b u =
      (kernelIntervalL2ZeroExtension a c b).adjoint
        (cc20GlobalConvolutionCrossing g.involution.test b
          (kernelIntervalL2ZeroExtension a c b u)) := by
  rfl

noncomputable def sourceWindowProjection (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (restrictedSetZeroExtension (Set.Icc (0 : ℝ) b) measurableSet_Icc).comp
    (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Icc (0 : ℝ) b))

theorem sourceWindowProjection_coeFn
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    (sourceWindowProjection b u : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (0 : ℝ) b).indicator (fun t => u t) := by
  rw [sourceWindowProjection, ContinuousLinearMap.comp_apply]
  have hextend := restrictedSetZeroExtension_coeFn
    (Set.Icc (0 : ℝ) b) measurableSet_Icc
      (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Set.Icc (0 : ℝ) b) u)
  have hrestrict := LpToLpRestrictCLM_coeFn ℂ
    (Set.Icc (0 : ℝ) b) u
  have hrestrict' := (ae_restrict_iff' measurableSet_Icc).mp hrestrict
  filter_upwards [hextend, hrestrict'] with t he hr
  by_cases ht : t ∈ Set.Icc (0 : ℝ) b
  · rw [Set.indicator_of_mem ht] at he ⊢
    rw [hr ht] at he
    exact he
  · simp only [Set.indicator_of_notMem ht]
    rw [he]
    simp only [Set.indicator_of_notMem ht]

theorem globalL2ToSourceInterval_adjoint_comp
    (b : ℝ) :
    (globalL2ToSourceInterval b).adjoint ∘L
        globalL2ToSourceInterval b =
      sourceWindowProjection b := by
  rw [globalL2ToSourceInterval, ContinuousLinearMap.adjoint_comp]
  rw [sourceWindowProjection]
  rw [← restrictedSetZeroExtension_eq_adjoint_restrict
    (Set.Icc (0 : ℝ) b) measurableSet_Icc]
  ext u
  simp

theorem norm_globalL2ToSourceInterval_adjoint_apply
    (b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (SourceInterval b))) :
    ‖(globalL2ToSourceInterval b).adjoint u‖ = ‖u‖ := by
  rw [globalL2ToSourceInterval, ContinuousLinearMap.adjoint_comp]
  rw [← restrictedSetZeroExtension_eq_adjoint_restrict
    (Set.Icc (0 : ℝ) b) measurableSet_Icc]
  rw [(sourceIntervalSubtypeRestrictedL2IsometryEquiv b).adjoint_eq_symm]
  rw [ContinuousLinearMap.comp_apply]
  rw [norm_restrictedSetZeroExtension_apply]
  exact (sourceIntervalSubtypeRestrictedL2IsometryEquiv b).symm.norm_map u

noncomputable def globalBoundaryTranslationProjection (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (cc20GlobalLogTranslation b).toContinuousLinearMap.comp
    (sourceWindowProjection b)

theorem globalBoundaryTranslationProjection_apply
    (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    globalBoundaryTranslationProjection b u =
      cc20GlobalLogTranslation b (sourceWindowProjection b u) := by
  rfl

theorem globalBoundaryTranslationProjection_eq_singleCrossingOperator
    (b : ℝ) (hb : 0 ≤ b) :
    globalBoundaryTranslationProjection b =
      cc20SingleCrossingOperator b := by
  apply ContinuousLinearMap.ext
  intro u
  rw [globalBoundaryTranslationProjection_apply]
  rw [Lp.ext_iff]
  have htranslation := cc20GlobalLogTranslation_coeFn b
    (sourceWindowProjection b u)
  have hprojection :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae_eq_comp
      (sourceWindowProjection_coeFn b u)
  have hcross := cc20SingleCrossingOperator_coeFn_eq_Icc_indicator
    b hb u
  filter_upwards [htranslation, hprojection, hcross] with t ht hp hc
  rw [ht, hc]
  by_cases htb : t + b ∈ Set.Icc (0 : ℝ) b
  · have hleft : t ∈ Set.Icc (-b) 0 := by
      constructor <;> linarith [htb.1, htb.2]
    have hp' : (sourceWindowProjection b u : ℝ → ℂ) (t + b) =
        (Set.Icc (0 : ℝ) b).indicator (fun x => u x) (t + b) := by
      simpa only [Function.comp_apply] using hp
    rw [hp']
    simp only [Set.indicator_of_mem htb, Set.indicator_of_mem hleft]
  · have hleft : t ∉ Set.Icc (-b) 0 := by
      intro h
      apply htb
      constructor <;> linarith [h.1, h.2]
    have hp' : (sourceWindowProjection b u : ℝ → ℂ) (t + b) =
        (Set.Icc (0 : ℝ) b).indicator (fun x => u x) (t + b) := by
      simpa only [Function.comp_apply] using hp
    rw [hp']
    simp only [Set.indicator_of_notMem htb, Set.indicator_of_notMem hleft]

noncomputable def kernelCompressedBoundaryTranslationCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (KernelInterval a c b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  (kernelIntervalL2ZeroExtension a c b).adjoint ∘L
    ((cc20GlobalConvolutionPositive g.involution.test) ∘L
      (globalBoundaryTranslationProjection b)) ∘L
    kernelIntervalL2ZeroExtension a c b

theorem kernelCompressedBoundaryTranslationCrossing_eq
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) (hb : 0 ≤ b) :
    kernelCompressedBoundaryTranslationCrossing g a c b =
      kernelCompressedGlobalConvolutionCrossing g a c b := by
  rw [kernelCompressedBoundaryTranslationCrossing,
    kernelCompressedGlobalConvolutionCrossing,
    cc20GlobalConvolutionCrossing,
    ← globalBoundaryTranslationProjection_eq_singleCrossingOperator b hb]

noncomputable def kernelCompressedSandwichedCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (KernelInterval a c b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval a c b)) :=
  (kernelIntervalL2ZeroExtension a c b).adjoint ∘L
    ((cc20GlobalLogConvolution g.involution.test).adjoint ∘L
      ((cc20SingleCrossingOperator b) ∘L
        (cc20GlobalLogConvolution g.involution.test))) ∘L
    kernelIntervalL2ZeroExtension a c b

theorem schwartzConvolution_compSubConstCLM
    (g u : SchwartzMap ℝ ℂ) (b : ℝ) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) g
        (SchwartzMap.compSubConstCLM ℂ b u) =
      SchwartzMap.compSubConstCLM ℂ b
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ) g u) := by
  rw [schwartzConvolution_mul_real_eq_complex g
    (SchwartzMap.compSubConstCLM ℂ b u)]
  rw [schwartzConvolution_mul_real_eq_complex g u]
  ext s
  simp only [SchwartzMap.compSubConstCLM_apply]
  rw [SchwartzMap.convolution_apply]
  rw [SchwartzMap.convolution_apply]
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  simp only [SchwartzMap.compSubConstCLM_apply]
  apply integral_congr_ae
  filter_upwards with t
  congr 2 <;> ring

theorem cc20GlobalLogConvolution_comp_translation_neg_eq
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    (cc20GlobalLogConvolution g.involution.test).comp
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap =
      (cc20GlobalLogTranslation (-b)).toContinuousLinearMap.comp
        (cc20GlobalLogConvolution g.involution.test) := by
  have hglobal : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      ((cc20GlobalLogConvolution g.involution.test).comp
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap :
          cc20GlobalLogCrossingL2 → cc20GlobalLogCrossingL2) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
        ((cc20GlobalLogTranslation (-b)).toContinuousLinearMap.comp
          (cc20GlobalLogConvolution g.involution.test) :
            cc20GlobalLogCrossingL2 → cc20GlobalLogCrossingL2) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    rw [Function.comp_apply, Function.comp_apply]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    have htransU := cc20GlobalLogTranslation_neg_apply_schwartzToLp u b
    have htransU' :
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap (u.toLp 2) =
          (SchwartzMap.compSubConstCLM ℂ b u).toLp 2 := by
      exact htransU
    rw [htransU']
    rw [cc20GlobalLogConvolution_toLp]
    rw [cc20GlobalLogConvolution_toLp]
    have htransConv := cc20GlobalLogTranslation_neg_apply_schwartzToLp
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u) b
    have htransConv' :
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap
            ((SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
              g.involution.test u).toLp 2) =
          (SchwartzMap.compSubConstCLM ℂ b
            (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
              g.involution.test u)).toLp 2 := by
      exact htransConv
    rw [htransConv']
    exact congrArg (fun f : SchwartzMap ℝ ℂ => f.toLp 2)
      (schwartzConvolution_compSubConstCLM
        g.involution.test u b)
  have hfun := DenseRange.equalizer hglobal
    ((cc20GlobalLogConvolution g.involution.test).comp
      (cc20GlobalLogTranslation (-b)).toContinuousLinearMap).continuous
    ((cc20GlobalLogTranslation (-b)).toContinuousLinearMap.comp
      (cc20GlobalLogConvolution g.involution.test)).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

theorem leftGlobalTranslatedConvolutionSourceOperator_eq
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    leftGlobalTranslatedConvolutionSourceOperator g b =
      (globalL2ToSourceInterval b).comp
        ((cc20GlobalLogTranslation (-b)).toContinuousLinearMap.comp
          (cc20GlobalLogConvolution g.involution.test)) := by
  rw [leftGlobalTranslatedConvolutionSourceOperator]
  rw [cc20GlobalLogConvolution_comp_translation_neg_eq]

noncomputable def cc20GlobalLogTranslationEquiv (b : ℝ) :
    cc20GlobalLogCrossingL2 ≃ₗᵢ[ℂ] cc20GlobalLogCrossingL2 :=
  LinearIsometryEquiv.ofSurjective (cc20GlobalLogTranslation b) fun u =>
    ⟨cc20GlobalLogTranslation (-b) u,
      cc20GlobalLogTranslation_neg_apply b u⟩

theorem cc20GlobalLogTranslation_neg_adjoint
    (b : ℝ) :
    (cc20GlobalLogTranslation (-b)).toContinuousLinearMap.adjoint =
      (cc20GlobalLogTranslation b).toContinuousLinearMap := by
  change ContinuousLinearMap.adjoint
      (cc20GlobalLogTranslationEquiv (-b) :
        cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2) = _
  calc
    _ = ((cc20GlobalLogTranslationEquiv (-b)).symm :
        cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2) :=
      (cc20GlobalLogTranslationEquiv (-b)).adjoint_eq_symm
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro u
      apply (cc20GlobalLogTranslationEquiv (-b)).injective
      change (cc20GlobalLogTranslationEquiv (-b))
          ((cc20GlobalLogTranslationEquiv (-b)).symm u) =
        cc20GlobalLogTranslation (-b)
          (cc20GlobalLogTranslation b u)
      rw [(cc20GlobalLogTranslationEquiv (-b)).apply_symm_apply]
      simpa only [neg_neg] using
        (cc20GlobalLogTranslation_neg_apply (-b) u).symm

theorem leftGlobalConvolutionCoreLinearMap_apply
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (b : ℝ) :
    leftGlobalConvolutionCoreLinearMap g b u =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (shiftedSourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [leftGlobalConvolutionCoreLinearMap, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  have hconv := cc20GlobalLogConvolution_toLp g.involution.test
    (SchwartzMap.compSubConstCLM ℂ b u)
  have hshift :
      shiftedSourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b =
        sourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test (SchwartzMap.compSubConstCLM ℂ b u)) b := by
    ext s
    rw [schwartzConvolution_compSubConstCLM]
    rfl
  rw [hshift]
  rw [← globalL2ToSourceInterval_apply_schwartzToLp
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
      g.involution.test (SchwartzMap.compSubConstCLM ℂ b u)) b]
  apply congrArg (globalL2ToSourceInterval b)
  change cc20GlobalLogConvolution g.involution.test
      ((SchwartzMap.compSubConstCLM ℂ b u).toLp 2) = _
  exact hconv

theorem leftCoefficient_kernelRestriction_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t in Set.Icc (a - b) (c + b),
        u t * star (g.test (t - s.1 + b)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (leftKernel g.test g.test.continuous a c b) s))
      (ContinuousMap.toLp 2
        (volume : Measure (KernelInterval a c b)) ℂ
        (kernelRestriction u a c b)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ t : KernelInterval a c b,
      u t.1 * star (g.test (t.1 - s.1 + b))
        ∂Measure.comap Subtype.val volume) = _
  exact integral_subtype_comap (μ := (volume : Measure ℝ))
    measurableSet_Icc
    (fun t : ℝ => u t * star (g.test (t - s.1 + b)))

theorem leftCoefficient_kernelRestriction_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      ∫ t : ℝ, u t * star (g.test (t - s.1 + b)) := by
  rw [leftCoefficient_kernelRestriction_eq_setIntegral]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - b) (c + b)
  · rw [Set.indicator_of_mem ht]
  · have hgt : g.test (t - s.1 + b) = 0 := by
      by_contra hne
      have hmem := hg (by simpa [Function.mem_support] using hne)
      have hb : 0 ≤ b := le_trans s.2.1 s.2.2
      exact ht ⟨by linarith [hmem.1, s.2.1],
        by linarith [hmem.2, s.2.2]⟩
    simp [Set.indicator, ht, hgt]

theorem leftCoefficient_kernelRestriction_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c)
    (s : SourceInterval b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) s =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u (s.1 - b) := by
  rw [leftCoefficient_kernelRestriction_eq_fullIntegral g u a c b hg s]
  have hcomplex :
      (∫ t : ℝ, u t * star (g.test (t - s.1 + b))) =
        SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
          u g.involution.test (s.1 - b) := by
    let B := ContinuousLinearMap.mul ℂ ℂ
    calc
      (∫ t : ℝ, u t * star (g.test (t - s.1 + b))) =
          (u ⋆[B] g.involution.test) (s.1 - b) := by
        rw [MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with t
        rw [CompactLogConvolution.CompactLogTest.involution_apply]
        congr 2
        ring
      _ = SchwartzMap.convolution B u g.involution.test (s.1 - b) :=
        (SchwartzMap.convolution_apply
          B u g.involution.test (s.1 - b)).symm
  rw [hcomplex]
  rw [← schwartzConvolution_mul_real_eq_complex]
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (s.1 - b))
    (schwartzConvolution_mul_real_comm u g.involution.test)

theorem leftCoefficient_kernelRestriction_eq_shiftedSourceRestriction
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (KernelInterval a c b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      shiftedSourceRestriction
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u) b := by
  ext s
  exact leftCoefficient_kernelRestriction_eq_globalConvolutionCore
    g u a c b hg s

theorem leftOperator_kernelRestriction_eq_shiftedSourceConvolutionToLp
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b)) =
      ContinuousMap.toLp 2 (volume : Measure (SourceInterval b)) ℂ
        (shiftedSourceRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) b) := by
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  rw [leftCoefficient_kernelRestriction_eq_shiftedSourceRestriction
    g u a c b hg]

theorem leftKernelGlobalRestrictionOperator_eq_globalTranslatedConvolution
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    leftKernelGlobalRestrictionOperator g a c b =
      leftGlobalTranslatedConvolutionSourceOperator g b := by
  have hglobal : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (leftKernelGlobalRestrictionOperator g a c b :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (SourceInterval b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
        (leftGlobalTranslatedConvolutionSourceOperator g b :
          cc20GlobalLogCrossingL2 →
            Lp ℂ 2 (volume : Measure (SourceInterval b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    rw [Function.comp_apply, Function.comp_apply]
    rw [leftKernelGlobalRestrictionOperator_apply,
      leftGlobalTranslatedConvolutionSourceOperator_apply]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [leftOperator_kernelRestriction_eq_shiftedSourceConvolutionToLp
      g u a c b hg]
    rw [cc20GlobalLogTranslation_neg_apply_schwartzToLp]
    rw [cc20GlobalLogConvolution_toLp]
    rw [schwartzConvolution_compSubConstCLM]
    exact (globalL2ToSourceInterval_apply_schwartzToLp
      (SchwartzMap.compSubConstCLM ℂ b
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
          g.involution.test u)) b).symm
  have hfun := DenseRange.equalizer hglobal
    (leftKernelGlobalRestrictionOperator g a c b).continuous
    (leftGlobalTranslatedConvolutionSourceOperator g b).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

theorem leftKernelOperator_eq_globalTranslatedConvolution_zeroExtension
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b) =
      (leftGlobalTranslatedConvolutionSourceOperator g b).comp
        (kernelIntervalL2ZeroExtension a c b) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [← leftKernelGlobalRestrictionOperator_eq_globalTranslatedConvolution
    g a c b hg]
  rw [ContinuousLinearMap.comp_apply]
  rw [leftKernelGlobalRestrictionOperator_apply]
  rw [globalL2ToKernelInterval_zeroExtension]

theorem pairData_traceProduct_eq_globalZeroExtensionProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    (pairData g.test g.test.continuous a c b basis).traceProduct =
      ((leftGlobalTranslatedConvolutionSourceOperator g b).comp
          (kernelIntervalL2ZeroExtension a c b)).adjoint ∘L
        (rightGlobalConvolutionSourceOperator g b).comp
          (kernelIntervalL2ZeroExtension a c b) := by
  change
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.test g.test.continuous a c b)).adjoint ∘L
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b) = _
  rw [leftKernelOperator_eq_globalTranslatedConvolution_zeroExtension
      g a c b hsupp,
    rightKernelOperator_eq_globalConvolution_zeroExtension
      g a c b hsupp]

theorem pairData_traceProduct_eq_kernelCompressedSandwichedCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    (pairData g.test g.test.continuous a c b basis).traceProduct =
      kernelCompressedSandwichedCrossing g a c b := by
  rw [pairData_traceProduct_eq_globalZeroExtensionProduct
    g a c b hsupp basis]
  rw [leftGlobalTranslatedConvolutionSourceOperator_eq]
  rw [rightGlobalConvolutionSourceOperator]
  rw [kernelCompressedSandwichedCrossing]
  simp only [ContinuousLinearMap.adjoint_comp]
  rw [cc20GlobalLogTranslation_neg_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  let x := cc20GlobalLogConvolution g.involution.test
    (kernelIntervalL2ZeroExtension a c b u)
  have hsource := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 => T x)
    (globalL2ToSourceInterval_adjoint_comp b)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hsource
  rw [hsource]
  have hboundary : globalBoundaryTranslationProjection b x =
      cc20SingleCrossingOperator b x := congrArg
        (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
          cc20GlobalLogCrossingL2 => T x)
        (globalBoundaryTranslationProjection_eq_singleCrossingOperator b hb)
  rw [globalBoundaryTranslationProjection_apply] at hboundary
  exact congrArg
    (fun y => (kernelIntervalL2ZeroExtension a c b).adjoint
      ((cc20GlobalLogConvolution g.involution.test).adjoint y))
    hboundary

noncomputable def kernelIntervalProjection
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (kernelIntervalL2ZeroExtension a c b).comp
    (kernelIntervalL2ZeroExtension a c b).adjoint

noncomputable def sourceCyclicProjectionProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).comp
    ((cc20GlobalLogConvolution g.involution.test).comp
      ((kernelIntervalProjection a c b).comp
        ((cc20GlobalLogConvolution g.involution.test).adjoint.comp
          ((cc20GlobalLogTranslation b).toContinuousLinearMap.comp
            (globalL2ToSourceInterval b).adjoint))))

theorem cyclicGlobalZeroExtensionProduct_eq_sourceCyclicProjectionProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    ((rightGlobalConvolutionSourceOperator g b).comp
        (kernelIntervalL2ZeroExtension a c b)).comp
      ((leftGlobalTranslatedConvolutionSourceOperator g b).comp
        (kernelIntervalL2ZeroExtension a c b)).adjoint =
      sourceCyclicProjectionProduct g a c b := by
  rw [rightGlobalConvolutionSourceOperator]
  rw [leftGlobalTranslatedConvolutionSourceOperator_eq]
  rw [sourceCyclicProjectionProduct, kernelIntervalProjection]
  simp only [ContinuousLinearMap.adjoint_comp]
  rw [cc20GlobalLogTranslation_neg_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem pairData_trace_eq_sourceCyclicProjectionProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {ι κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (targetBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b)))) :
    PositiveTrace.ordinaryTraceAlong sourceBasis
        (pairData g.test g.test.continuous a c b sourceBasis).traceProduct =
      PositiveTrace.ordinaryTraceAlong targetBasis
        (sourceCyclicProjectionProduct g a c b) := by
  let data := pairData g.test g.test.continuous a c b sourceBasis
  calc
    PositiveTrace.ordinaryTraceAlong sourceBasis data.traceProduct =
        PositiveTrace.ordinaryTraceAlong targetBasis
          (data.right ∘L data.left.adjoint) :=
      data.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
    _ = PositiveTrace.ordinaryTraceAlong targetBasis
        (sourceCyclicProjectionProduct g a c b) := by
      apply congrArg (PositiveTrace.ordinaryTraceAlong targetBasis)
      change
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (KernelInterval a c b))
          (volume : Measure (SourceInterval b))
          (rightKernel g.test g.test.continuous a c b)).comp
            (ContinuousKernelHilbertSchmidt.operator
              (volume : Measure (KernelInterval a c b))
              (volume : Measure (SourceInterval b))
              (leftKernel g.test g.test.continuous a c b)).adjoint = _
      rw [rightKernelOperator_eq_globalConvolution_zeroExtension
          g a c b hsupp,
        leftKernelOperator_eq_globalTranslatedConvolution_zeroExtension
          g a c b hsupp]
      exact cyclicGlobalZeroExtensionProduct_eq_sourceCyclicProjectionProduct
        g a c b

theorem leftKernelOperator_comp_coreInput_eq_globalCore
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.test g.test.continuous a c b)).toLinearMap.comp
        (rightKernelCoreInputLinearMap a c b) =
      leftGlobalConvolutionCoreLinearMap g b := by
  apply LinearMap.ext
  intro u
  change ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.test g.test.continuous a c b)
        (rightKernelCoreInputLinearMap a c b u) =
    leftGlobalConvolutionCoreLinearMap g b u
  rw [rightKernelCoreInputLinearMap_apply]
  rw [leftOperator_kernelRestriction_eq_shiftedSourceConvolutionToLp
    g u a c b hg]
  exact (leftGlobalConvolutionCoreLinearMap_apply g u b).symm

theorem leftKernelOperator_is_unique_bounded_core_extension
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hg : Function.support g.test ⊆ Set.Icc a c) :
    (leftGlobalConvolutionCoreLinearMap g b).extendOfNorm
        (rightKernelCoreInputLinearMap a c b) =
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b) := by
  let T := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (leftKernel g.test g.test.continuous a c b)
  have hdense : DenseRange (rightKernelCoreInputLinearMap a c b) := by
    have hfun : (rightKernelCoreInputLinearMap a c b :
        SchwartzMap ℝ ℂ →
          Lp ℂ 2 (volume : Measure (KernelInterval a c b))) =
        fun u => ContinuousMap.toLp 2
          (volume : Measure (KernelInterval a c b)) ℂ
          (kernelRestriction u a c b) := by
      funext u
      exact rightKernelCoreInputLinearMap_apply u a c b
    rw [hfun]
    exact denseRange_kernelRestriction_toLp a c b
  have hnorm : ∀ u, ‖leftGlobalConvolutionCoreLinearMap g b u‖ ≤
      ‖T‖ * ‖rightKernelCoreInputLinearMap a c b u‖ := by
    intro u
    rw [← leftKernelOperator_comp_coreInput_eq_globalCore g a c b hg]
    exact T.le_opNorm _
  apply LinearMap.extendOfNorm_unique hdense ‖T‖ hnorm T
  simpa only [T] using
    leftKernelOperator_comp_coreInput_eq_globalCore g a c b hg

theorem pairData_traceProduct_eq_extendedCoreProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    (pairData g.test g.test.continuous a c b basis).traceProduct =
      ((leftGlobalConvolutionCoreLinearMap g b).extendOfNorm
          (rightKernelCoreInputLinearMap a c b)).adjoint ∘L
        (rightGlobalConvolutionCoreLinearMap g b).extendOfNorm
          (rightKernelCoreInputLinearMap a c b) := by
  change
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.test g.test.continuous a c b)).adjoint ∘L
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.test g.test.continuous a c b) = _
  rw [← leftKernelOperator_is_unique_bounded_core_extension
      g a c b hsupp,
    ← rightKernelOperator_is_unique_bounded_core_extension
      g a c b hsupp]

theorem fourier_compactLogTest_involution
    (g : CompactLogConvolution.CompactLogTest) (xi : ℝ) :
    (𝓕 g.involution.test) xi = star ((𝓕 g.test) xi) := by
  change (∫ x : ℝ, 𝐞 (-inner ℝ x xi) • conj (g.test (-x))) =
    conj (∫ x : ℝ, 𝐞 (-inner ℝ x xi) • g.test x)
  rw [← integral_conj]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  rw [show -inner ℝ (-x) xi = inner ℝ x xi by simp]
  simp only [neg_neg]
  change ((𝐞 (inner ℝ x xi) : Circle) : ℂ) * conj (g.test x) =
    conj (((𝐞 (-inner ℝ x xi) : Circle) : ℂ) * g.test x)
  rw [map_mul]
  congr 1
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext <;> norm_num

theorem multiplier_inner_of_eq_star
    (a d b c : ℂ) (hadj : a = star d) :
    inner ℂ (a * b) c = inner ℂ b (d * c) := by
  rw [RCLike.inner_apply, RCLike.inner_apply]
  rw [map_mul (starRingEnd ℂ) a b, hadj, starRingEnd_apply, star_star]
  ring

set_option maxHeartbeats 800000 in
-- The four simultaneous `Lp` representative rewrites make elaboration exceed
-- the default heartbeat budget; the proof itself is the pointwise multiplier identity.
theorem globalLogConvolution_involution_inner_core
    (g : CompactLogConvolution.CompactLogTest)
    (u v : SchwartzMap ℝ ℂ) :
    inner ℂ
        (cc20GlobalLogConvolution g.involution.test (u.toLp 2))
        (v.toLp 2) =
      inner ℂ (u.toLp 2)
        (cc20GlobalLogConvolution g.test (v.toLp 2)) := by
  rw [cc20GlobalLogConvolution_toLp]
  rw [cc20GlobalLogConvolution_toLp]
  let leftConv := SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
    g.involution.test u
  let rightConv := SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
    g.test v
  change inner ℂ (leftConv.toLp 2) (v.toLp 2) =
    inner ℂ (u.toLp 2) (rightConv.toLp 2)
  rw [← SchwartzMap.inner_fourier_toL2_eq leftConv v]
  rw [← SchwartzMap.inner_fourier_toL2_eq u rightConv]
  change inner ℂ ((𝓕 leftConv).toLp 2) ((𝓕 v).toLp 2) =
    inner ℂ ((𝓕 u).toLp 2) ((𝓕 rightConv).toLp 2)
  dsimp only [leftConv, rightConv]
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.fourier_convolution]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
        (𝓕 g.involution.test) (𝓕 u)).coeFn_toLp 2,
      (𝓕 v).coeFn_toLp 2,
      (𝓕 u).coeFn_toLp 2,
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
        (𝓕 g.test) (𝓕 v)).coeFn_toLp 2] with xi hleft hv hu hright
  rw [hleft, hv, hu, hright]
  exact multiplier_inner_of_eq_star
    ((𝓕 g.involution.test) xi) ((𝓕 g.test) xi)
    ((𝓕 u) xi) ((𝓕 v) xi) (fourier_compactLogTest_involution g xi)

theorem globalLogConvolution_involution_eq_adjoint
    (g : CompactLogConvolution.CompactLogTest) :
    cc20GlobalLogConvolution g.involution.test =
      (cc20GlobalLogConvolution g.test).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  have hdense : DenseRange (fun f : SchwartzMap ℝ ℂ => f.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hright (f : SchwartzMap ℝ ℂ) :
      inner ℂ
          (cc20GlobalLogConvolution g.involution.test (f.toLp 2)) v =
        inner ℂ (f.toLp 2) (cc20GlobalLogConvolution g.test v) := by
    have hcore :
        (fun w : cc20GlobalLogCrossingL2 =>
          inner ℂ
            (cc20GlobalLogConvolution g.involution.test (f.toLp 2)) w) ∘
            (fun q : SchwartzMap ℝ ℂ => q.toLp 2) =
          (fun w : cc20GlobalLogCrossingL2 =>
            inner ℂ (f.toLp 2) (cc20GlobalLogConvolution g.test w)) ∘
            (fun q : SchwartzMap ℝ ℂ => q.toLp 2) := by
      funext q
      exact globalLogConvolution_involution_inner_core g f q
    have hfun := DenseRange.equalizer hdense (by fun_prop) (by fun_prop) hcore
    exact congrFun hfun v
  have hcore :
      (fun w : cc20GlobalLogCrossingL2 =>
        inner ℂ (cc20GlobalLogConvolution g.involution.test w) v) ∘
          (fun f : SchwartzMap ℝ ℂ => f.toLp 2) =
        (fun w : cc20GlobalLogCrossingL2 =>
          inner ℂ w (cc20GlobalLogConvolution g.test v)) ∘
          (fun f : SchwartzMap ℝ ℂ => f.toLp 2) := by
    funext f
    exact hright f
  have hfun := DenseRange.equalizer hdense (by fun_prop) (by fun_prop) hcore
  exact congrFun hfun u

theorem adjoint_globalLogConvolution_involution
    (g : CompactLogConvolution.CompactLogTest) :
    (cc20GlobalLogConvolution g.involution.test).adjoint =
      cc20GlobalLogConvolution g.test := by
  rw [globalLogConvolution_involution_eq_adjoint]
  exact ContinuousLinearMap.adjoint_adjoint _

theorem kernelIntervalRestrictedZeroExtension_eq_restrictedSetZeroExtension
    (a c b : ℝ) :
    kernelIntervalRestrictedZeroExtension a c b =
      restrictedSetZeroExtension (Set.Icc (a - b) (c + b)) measurableSet_Icc := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Lp.ext_iff]
  filter_upwards
    [kernelIntervalRestrictedZeroExtension_coeFn a c b u,
      restrictedSetZeroExtension_coeFn
        (Set.Icc (a - b) (c + b)) measurableSet_Icc u] with x hleft hright
  rw [hleft, hright]

theorem kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval
    (a c b : ℝ) :
    kernelIntervalL2ZeroExtension a c b =
      (globalL2ToKernelInterval a c b).adjoint := by
  rw [kernelIntervalL2ZeroExtension, globalL2ToKernelInterval]
  rw [ContinuousLinearMap.adjoint_comp]
  rw [← restrictedSetZeroExtension_eq_adjoint_restrict
    (Set.Icc (a - b) (c + b)) measurableSet_Icc]
  rw [← kernelIntervalRestrictedZeroExtension_eq_restrictedSetZeroExtension]
  congr 1
  exact (kernelIntervalSubtypeRestrictedL2IsometryEquiv a c b).adjoint_eq_symm.symm

theorem norm_globalL2ToKernelInterval_adjoint_apply
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (KernelInterval a c b))) :
    ‖(globalL2ToKernelInterval a c b).adjoint u‖ = ‖u‖ := by
  rw [← kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
  exact norm_kernelIntervalL2ZeroExtension a c b u

theorem leftKernelAdjoint_range_factorization
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    (kernelIntervalL2ZeroExtension a c b).comp
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (KernelInterval a c b))
          (volume : Measure (SourceInterval b))
          (leftKernel g.test g.test.continuous a c b)).adjoint =
      (cc20GlobalLogConvolution g.test).comp
        ((cc20GlobalLogTranslation b).toContinuousLinearMap.comp
          (globalL2ToSourceInterval b).adjoint) := by
  have hleft := leftKernelGlobalRestrictionOperator_eq_globalTranslatedConvolution
    g a c b hsupp
  rw [leftKernelGlobalRestrictionOperator] at hleft
  have hadj := congrArg ContinuousLinearMap.adjoint hleft
  rw [ContinuousLinearMap.adjoint_comp] at hadj
  rw [← kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval] at hadj
  rw [leftGlobalTranslatedConvolutionSourceOperator_eq] at hadj
  simp only [ContinuousLinearMap.adjoint_comp] at hadj
  rw [cc20GlobalLogTranslation_neg_adjoint] at hadj
  rw [adjoint_globalLogConvolution_involution] at hadj
  exact hadj

theorem rightKernelAdjoint_range_factorization
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    (kernelIntervalL2ZeroExtension a c b).comp
        (ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (KernelInterval a c b))
          (volume : Measure (SourceInterval b))
          (rightKernel g.test g.test.continuous a c b)).adjoint =
      (cc20GlobalLogConvolution g.test).comp
        (globalL2ToSourceInterval b).adjoint := by
  have hright := rightKernelGlobalRestrictionOperator_eq_globalConvolution
    g a c b hsupp
  rw [rightKernelGlobalRestrictionOperator] at hright
  have hadj := congrArg ContinuousLinearMap.adjoint hright
  rw [ContinuousLinearMap.adjoint_comp] at hadj
  rw [← kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval] at hadj
  rw [rightGlobalConvolutionSourceOperator] at hadj
  simp only [ContinuousLinearMap.adjoint_comp] at hadj
  rw [adjoint_globalLogConvolution_involution] at hadj
  exact hadj

theorem kernelIntervalProjection_zeroExtension
    (a c b : ℝ)
    (u : Lp ℂ 2 (volume : Measure (KernelInterval a c b))) :
    kernelIntervalProjection a c b (kernelIntervalL2ZeroExtension a c b u) =
      kernelIntervalL2ZeroExtension a c b u := by
  rw [kernelIntervalProjection, ContinuousLinearMap.comp_apply]
  have hadj : (kernelIntervalL2ZeroExtension a c b).adjoint =
      globalL2ToKernelInterval a c b := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [hadj]
  rw [globalL2ToKernelInterval_zeroExtension]

noncomputable def sourceCyclicUncompressedProduct
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).comp
    ((cc20GlobalLogConvolution g.involution.test).comp
      ((cc20GlobalLogConvolution g.test).comp
        ((cc20GlobalLogTranslation b).toContinuousLinearMap.comp
          (globalL2ToSourceInterval b).adjoint)))

theorem sourceCyclicProjectionProduct_eq_uncompressed
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    sourceCyclicProjectionProduct g a c b =
      sourceCyclicUncompressedProduct g b := by
  apply ContinuousLinearMap.ext
  intro u
  rw [sourceCyclicProjectionProduct, sourceCyclicUncompressedProduct]
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_globalLogConvolution_involution]
  let leftOp := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (KernelInterval a c b))
    (volume : Measure (SourceInterval b))
    (leftKernel g.test g.test.continuous a c b)
  have hrange := congrArg
    (fun T : Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
        cc20GlobalLogCrossingL2 => T u)
    (leftKernelAdjoint_range_factorization g a c b hsupp)
  simp only [ContinuousLinearMap.comp_apply] at hrange
  change kernelIntervalL2ZeroExtension a c b (leftOp.adjoint u) = _ at hrange
  rw [← hrange]
  rw [kernelIntervalProjection_zeroExtension]

theorem fourierMultiplier_comm
    (h k : SchwartzMap ℝ ℂ) :
    (cc20FourierMultiplier h).comp (cc20FourierMultiplier k) =
      (cc20FourierMultiplier k).comp (cc20FourierMultiplier h) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp only [cc20FourierMultiplier_apply]
  rw [Lp.ext_iff]
  filter_upwards
    [Lp.coeFn_lpSMul (r := 2) ((𝓕 h).toLp ⊤) ((𝓕 k).toLp ⊤ • u),
      Lp.coeFn_lpSMul (r := 2) ((𝓕 k).toLp ⊤) u,
      Lp.coeFn_lpSMul (r := 2) ((𝓕 k).toLp ⊤) ((𝓕 h).toLp ⊤ • u),
      Lp.coeFn_lpSMul (r := 2) ((𝓕 h).toLp ⊤) u] with x hleft hk hright hh
  rw [hleft, hright]
  change (((𝓕 h).toLp ⊤ : ℝ → ℂ) x) *
      (((((𝓕 k).toLp ⊤) • u : cc20GlobalLogCrossingL2) : ℝ → ℂ) x) =
    (((𝓕 k).toLp ⊤ : ℝ → ℂ) x) *
      (((((𝓕 h).toLp ⊤) • u : cc20GlobalLogCrossingL2) : ℝ → ℂ) x)
  rw [hk, hh]
  change (((𝓕 h).toLp ⊤ : ℝ → ℂ) x) *
      ((((𝓕 k).toLp ⊤ : ℝ → ℂ) x) * (u : ℝ → ℂ) x) =
    (((𝓕 k).toLp ⊤ : ℝ → ℂ) x) *
      ((((𝓕 h).toLp ⊤ : ℝ → ℂ) x) * (u : ℝ → ℂ) x)
  ring

theorem fourier_globalLogConvolution
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (cc20GlobalLogConvolution h u) =
      cc20FourierMultiplier h ((Lp.fourierTransformₗᵢ ℝ ℂ) u) := by
  rw [cc20GlobalLogConvolution_apply]
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
        (cc20FourierMultiplier h ((Lp.fourierTransformₗᵢ ℝ ℂ) u))) = _
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _

theorem globalLogConvolution_comm
    (h k : SchwartzMap ℝ ℂ) :
    (cc20GlobalLogConvolution h).comp (cc20GlobalLogConvolution k) =
      (cc20GlobalLogConvolution k).comp (cc20GlobalLogConvolution h) := by
  apply ContinuousLinearMap.ext
  intro u
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simp only [ContinuousLinearMap.comp_apply]
  rw [fourier_globalLogConvolution, fourier_globalLogConvolution,
    fourier_globalLogConvolution, fourier_globalLogConvolution]
  exact congrArg (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
      cc20GlobalLogCrossingL2 => T (𝓕 u)) (fourierMultiplier_comm h k)

noncomputable def namedSourceCrossingProduct
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (SourceInterval b)) :=
  (globalL2ToSourceInterval b).comp
    ((cc20GlobalLogConvolution g.test).comp
      ((cc20GlobalLogConvolution g.involution.test).comp
        ((cc20GlobalLogTranslation b).toContinuousLinearMap.comp
          (globalL2ToSourceInterval b).adjoint)))

theorem sourceCyclicUncompressedProduct_eq_namedSourceCrossingProduct
    (g : CompactLogConvolution.CompactLogTest) (b : ℝ) :
    sourceCyclicUncompressedProduct g b = namedSourceCrossingProduct g b := by
  rw [sourceCyclicUncompressedProduct, namedSourceCrossingProduct]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  let x := cc20GlobalLogTranslation b ((globalL2ToSourceInterval b).adjoint u)
  have hcomm := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 =>
      globalL2ToSourceInterval b (T x))
    (globalLogConvolution_comm g.involution.test g.test)
  simpa only [ContinuousLinearMap.comp_apply, x] using hcomm

theorem pairData_trace_eq_namedSourceCrossingProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {ι κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (targetBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b)))) :
    PositiveTrace.ordinaryTraceAlong sourceBasis
        (pairData g.test g.test.continuous a c b sourceBasis).traceProduct =
      PositiveTrace.ordinaryTraceAlong targetBasis
        (namedSourceCrossingProduct g b) := by
  calc
    _ = PositiveTrace.ordinaryTraceAlong targetBasis
        (sourceCyclicProjectionProduct g a c b) :=
      pairData_trace_eq_sourceCyclicProjectionProduct
        g a c b hsupp sourceBasis targetBasis
    _ = PositiveTrace.ordinaryTraceAlong targetBasis
        (sourceCyclicUncompressedProduct g b) := congrArg
      (PositiveTrace.ordinaryTraceAlong targetBasis)
      (sourceCyclicProjectionProduct_eq_uncompressed g a c b hsupp)
    _ = _ := congrArg (PositiveTrace.ordinaryTraceAlong targetBasis)
      (sourceCyclicUncompressedProduct_eq_namedSourceCrossingProduct g b)

theorem compactLogTest_involution_involution_test
    (g : CompactLogConvolution.CompactLogTest) :
    g.involution.involution.test = g.test := by
  ext x
  simp only [CompactLogConvolution.CompactLogTest.involution_apply,
    neg_neg, star_star]

theorem compactLogTest_involution_support_subset_reflected
    (g : CompactLogConvolution.CompactLogTest)
    (a c : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    Function.support g.involution.test ⊆ Set.Icc (-c) (-a) := by
  intro x hx
  have hneg : g.test (-x) ≠ 0 := by
    intro hzero
    apply hx
    rw [CompactLogConvolution.CompactLogTest.involution_apply, hzero]
    exact star_zero ℂ
  have hbounds := hsupp hneg
  constructor <;> linarith [hbounds.1, hbounds.2]

noncomputable def reflectedWholeLineLeftFactor
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)) →L[ℂ]
      cc20GlobalLogCrossingL2 :=
  (cc20GlobalLogConvolution g.test).comp
    (kernelIntervalL2ZeroExtension (-c) (-a) b)

noncomputable def reflectedWholeLineRightFactor
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)) :=
  (ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (KernelInterval (-c) (-a) b))
    (volume : Measure (SourceInterval b))
    (leftKernel g.involution.test g.involution.test.continuous
      (-c) (-a) b)).adjoint

theorem reflectedWholeLineLeftFactor_source_restriction
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    (globalL2ToSourceInterval b).comp
        (reflectedWholeLineLeftFactor g a c b) =
      ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval (-c) (-a) b))
        (volume : Measure (SourceInterval b))
        (rightKernel g.involution.test g.involution.test.continuous
          (-c) (-a) b) := by
  have hreflected := compactLogTest_involution_support_subset_reflected
    g a c hsupp
  rw [reflectedWholeLineLeftFactor]
  rw [rightKernelOperator_eq_globalConvolution_zeroExtension
    g.involution (-c) (-a) b hreflected]
  rw [rightGlobalConvolutionSourceOperator]
  rw [compactLogTest_involution_involution_test]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem reflectedWholeLineLeftRightFactor_eq_namedSourceCrossingProduct
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    ((globalL2ToSourceInterval b).comp
        (reflectedWholeLineLeftFactor g a c b)).comp
      (reflectedWholeLineRightFactor g a c b) =
        namedSourceCrossingProduct g b := by
  have hreflected := compactLogTest_involution_support_subset_reflected
    g a c hsupp
  rw [reflectedWholeLineLeftFactor, reflectedWholeLineRightFactor]
  have hrange := leftKernelAdjoint_range_factorization
    g.involution (-c) (-a) b hreflected
  rw [namedSourceCrossingProduct]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hrange_u := congrArg
    (fun T : Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
        cc20GlobalLogCrossingL2 => T u)
    hrange
  simp only [ContinuousLinearMap.comp_apply] at hrange_u
  rw [hrange_u]

theorem reflectedWholeLineBoundaryLeft_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {κ : Type*}
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)))) :
    Summable fun k =>
      ‖((globalL2ToSourceInterval b).comp
        (reflectedWholeLineLeftFactor g a c b)) (factorBasis k)‖ ^ 2 := by
  rw [reflectedWholeLineLeftFactor_source_restriction g a c b hsupp]
  exact (pairData g.involution.test g.involution.test.continuous
    (-c) (-a) b factorBasis).right_summable_normSq

theorem reflectedWholeLineRightFactor_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    {ι κ : Type*}
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)))) :
    Summable fun i =>
      ‖reflectedWholeLineRightFactor g a c b (sourceBasis i)‖ ^ 2 := by
  exact PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
    factorBasis sourceBasis
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval (-c) (-a) b))
      (volume : Measure (SourceInterval b))
      (leftKernel g.involution.test g.involution.test.continuous
        (-c) (-a) b))
    ((pairData g.involution.test g.involution.test.continuous
      (-c) (-a) b factorBasis).left_summable_normSq)

theorem reflectedWholeLineRightBoundary_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    {κ ν : Type*}
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    Summable fun j =>
      ‖((reflectedWholeLineRightFactor g a c b).comp
        (globalL2ToSourceInterval b)) (globalBasis j)‖ ^ 2 := by
  let leftOp := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (KernelInterval (-c) (-a) b))
    (volume : Measure (SourceInterval b))
    (leftKernel g.involution.test g.involution.test.continuous
      (-c) (-a) b)
  let cyclicOp := (reflectedWholeLineRightFactor g a c b).comp
    (globalL2ToSourceInterval b)
  have hadjoint : cyclicOp.adjoint =
      (globalL2ToSourceInterval b).adjoint.comp leftOp := by
    dsimp only [cyclicOp, reflectedWholeLineRightFactor, leftOp]
    rw [ContinuousLinearMap.adjoint_comp]
    rw [ContinuousLinearMap.adjoint_adjoint]
  have hadjoint_summable : Summable fun k =>
      ‖cyclicOp.adjoint (factorBasis k)‖ ^ 2 := by
    rw [hadjoint]
    simpa only [ContinuousLinearMap.comp_apply,
      norm_globalL2ToSourceInterval_adjoint_apply] using
      (pairData g.involution.test g.involution.test.continuous
        (-c) (-a) b factorBasis).left_summable_normSq
  have hcycled :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      factorBasis globalBasis cyclicOp.adjoint hadjoint_summable
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hcycled

theorem reflectedWholeLineCycleProduct_eq_globalConvolutionCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b) :
    (reflectedWholeLineLeftFactor g a c b).comp
        ((reflectedWholeLineRightFactor g a c b).comp
          (globalL2ToSourceInterval b)) =
      cc20GlobalConvolutionCrossing g.involution.test b := by
  have hreflected := compactLogTest_involution_support_subset_reflected
    g a c hsupp
  have hrange := leftKernelAdjoint_range_factorization
    g.involution (-c) (-a) b hreflected
  rw [reflectedWholeLineLeftFactor, reflectedWholeLineRightFactor]
  rw [cc20GlobalConvolutionCrossing, cc20GlobalConvolutionPositive]
  rw [adjoint_globalLogConvolution_involution]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hrange_u := congrArg
    (fun T : Lp ℂ 2 (volume : Measure (SourceInterval b)) →L[ℂ]
        cc20GlobalLogCrossingL2 =>
      T (globalL2ToSourceInterval b u))
    hrange
  simp only [ContinuousLinearMap.comp_apply] at hrange_u
  rw [hrange_u]
  have hsource := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => T u)
    (globalL2ToSourceInterval_adjoint_comp b)
  simp only [ContinuousLinearMap.comp_apply] at hsource
  have hboundary := congrArg
    (fun T : cc20GlobalLogCrossingL2 →L[ℂ]
        cc20GlobalLogCrossingL2 => T u)
    (globalBoundaryTranslationProjection_eq_singleCrossingOperator b hb)
  change globalBoundaryTranslationProjection b u =
    cc20SingleCrossingOperator b u at hboundary
  rw [globalBoundaryTranslationProjection_apply] at hboundary
  rw [← hsource] at hboundary
  change (cc20GlobalLogTranslation b).toContinuousLinearMap
      ((globalL2ToSourceInterval b).adjoint
        (globalL2ToSourceInterval b u)) =
    cc20SingleCrossingOperator b u at hboundary
  rw [hboundary]

theorem namedSource_trace_eq_globalConvolutionCrossing_of_left_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι κ ν : Type*}
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (hleft : Summable fun k =>
      ‖reflectedWholeLineLeftFactor g a c b (factorBasis k)‖ ^ 2) :
    PositiveTrace.ordinaryTraceAlong sourceBasis
        (namedSourceCrossingProduct g b) =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing g.involution.test b) := by
  let boundary := globalL2ToSourceInterval b
  let leftFactor := reflectedWholeLineLeftFactor g a c b
  let rightFactor := reflectedWholeLineRightFactor g a c b
  have hcycle :=
    PositiveTrace.BasisHilbertSchmidtPairData.ordinaryTraceAlong_three_comp_eq_cycle
      sourceBasis factorBasis globalBasis boundary leftFactor rightFactor
      (reflectedWholeLineBoundaryLeft_summable
        g a c b hsupp factorBasis)
      (reflectedWholeLineRightFactor_summable
        g a c b sourceBasis factorBasis)
      hleft
      (reflectedWholeLineRightBoundary_summable
        g a c b factorBasis globalBasis)
  calc
    _ = PositiveTrace.ordinaryTraceAlong sourceBasis
        ((boundary.comp leftFactor).comp rightFactor) := congrArg
      (PositiveTrace.ordinaryTraceAlong sourceBasis)
      (reflectedWholeLineLeftRightFactor_eq_namedSourceCrossingProduct
        g a c b hsupp).symm
    _ = PositiveTrace.ordinaryTraceAlong globalBasis
        (leftFactor.comp (rightFactor.comp boundary)) := hcycle
    _ = _ := congrArg (PositiveTrace.ordinaryTraceAlong globalBasis)
      (reflectedWholeLineCycleProduct_eq_globalConvolutionCrossing
        g a c b hsupp hb)

abbrev ReflectedWholeLineAdjointInputInterval
    (a c b : ℝ) := KernelInterval (a - c - b) (c - a + b) 0

noncomputable def reflectedWholeLineAdjointKernel
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    ContinuousMap
      ((KernelInterval (-c) (-a) b) ×
        (ReflectedWholeLineAdjointInputInterval a c b)) ℂ where
  toFun z := g.test (z.2.1 - z.1.1)
  continuous_toFun := g.test.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst))

theorem reflectedWholeLineAdjointKernel_apply
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (y : KernelInterval (-c) (-a) b)
    (t : ReflectedWholeLineAdjointInputInterval a c b) :
    reflectedWholeLineAdjointKernel g a c b (y, t) =
      g.test (t.1 - y.1) := rfl

theorem reflectedWholeLineAdjointCoefficient_eq_setIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ)
    (a c b : ℝ)
    (y : KernelInterval (-c) (-a) b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))
        (reflectedWholeLineAdjointKernel g a c b)
      (ContinuousMap.toLp 2
          (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
          (kernelRestriction u (a - c - b) (c - a + b) 0)) y =
      ∫ t in Set.Icc ((a - c - b) - 0) ((c - a + b) + 0),
        u t * star (g.test (t - y.1)) := by
  change inner ℂ
      (ContinuousMap.toLp 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
        (ContinuousKernelHilbertSchmidt.kernelSection
          (reflectedWholeLineAdjointKernel g a c b) y))
      (ContinuousMap.toLp 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
        (kernelRestriction u (a - c - b) (c - a + b) 0)) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ t : ReflectedWholeLineAdjointInputInterval a c b,
      u t.1 * star (g.test (t.1 - y.1))
        ∂Measure.comap Subtype.val volume) = _
  exact
    (integral_subtype_comap (μ := (volume : Measure ℝ))
      (s := Set.Icc ((a - c - b) - 0) ((c - a + b) + 0))
      measurableSet_Icc (fun t : ℝ => u t * star (g.test (t - y.1))))

theorem reflectedWholeLineAdjointCoefficient_eq_fullIntegral
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (y : KernelInterval (-c) (-a) b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))
        (reflectedWholeLineAdjointKernel g a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
          (kernelRestriction u (a - c - b) (c - a + b) 0)) y =
      ∫ t : ℝ, u t * star (g.test (t - y.1)) := by
  rw [reflectedWholeLineAdjointCoefficient_eq_setIntegral]
  simp only [sub_zero, add_zero]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (a - c - b) (c - a + b)
  · rw [Set.indicator_of_mem ht]
  · have hgt : g.test (t - y.1) = 0 := by
      by_contra hne
      have hmem := hsupp (by simpa [Function.mem_support] using hne)
      exact ht ⟨by linarith [hmem.1, y.2.1],
        by linarith [hmem.2, y.2.2]⟩
    simp [Set.indicator, ht, hgt]

theorem reflectedWholeLineAdjointCoefficient_eq_globalConvolutionCore
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (y : KernelInterval (-c) (-a) b) :
    ContinuousKernelHilbertSchmidt.coefficient
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))
        (reflectedWholeLineAdjointKernel g a c b)
        (ContinuousMap.toLp 2
          (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
          (kernelRestriction u (a - c - b) (c - a + b) 0)) y =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u y.1 := by
  rw [reflectedWholeLineAdjointCoefficient_eq_fullIntegral
    g u a c b hsupp y]
  let B := ContinuousLinearMap.mul ℂ ℂ
  calc
    (∫ t : ℝ, u t * star (g.test (t - y.1))) =
        (u ⋆[B] g.involution.test) y.1 := by
      rw [MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      rw [CompactLogConvolution.CompactLogTest.involution_apply]
      congr 2
      ring
    _ = SchwartzMap.convolution B u g.involution.test y.1 :=
      (SchwartzMap.convolution_apply B u g.involution.test y.1).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        u g.involution.test y.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f y.1)
        (schwartzConvolution_mul_real_eq_complex u g.involution.test).symm
    _ = SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u y.1 := by
      exact congrArg (fun f : SchwartzMap ℝ ℂ => f y.1)
        (schwartzConvolution_mul_real_comm u g.involution.test)

noncomputable def reflectedWholeLineAdjointFiniteOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    Lp ℂ 2 (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)) :=
  ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))
    (volume : Measure (KernelInterval (-c) (-a) b))
    (reflectedWholeLineAdjointKernel g a c b)

theorem reflectedWholeLineAdjointFiniteOperator_core
    (g : CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    reflectedWholeLineAdjointFiniteOperator g a c b
        (ContinuousMap.toLp 2
          (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b)) ℂ
          (kernelRestriction u (a - c - b) (c - a + b) 0)) =
      ContinuousMap.toLp 2
        (volume : Measure (KernelInterval (-c) (-a) b)) ℂ
        (kernelRestriction
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u) (-c) (-a) b) := by
  rw [reflectedWholeLineAdjointFiniteOperator]
  rw [ContinuousKernelHilbertSchmidt.operator_apply]
  apply congrArg (ContinuousMap.toLp 2
    (volume : Measure (KernelInterval (-c) (-a) b)) ℂ)
  ext y
  exact reflectedWholeLineAdjointCoefficient_eq_globalConvolutionCore
    g u a c b hsupp y

noncomputable def reflectedWholeLineAdjointGlobalRestrictionOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)) :=
  (reflectedWholeLineAdjointFiniteOperator g a c b).comp
    (globalL2ToKernelInterval (a - c - b) (c - a + b) 0)

noncomputable def reflectedWholeLineAdjointNamedRestrictionOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)) :=
  (globalL2ToKernelInterval (-c) (-a) b).comp
    (cc20GlobalLogConvolution g.involution.test)

theorem reflectedWholeLineAdjointGlobalRestrictionOperator_eq_named
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    reflectedWholeLineAdjointGlobalRestrictionOperator g a c b =
      reflectedWholeLineAdjointNamedRestrictionOperator g a c b := by
  have hdense : DenseRange (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    simpa only [SchwartzMap.toLpCLM_apply] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := volume) ENNReal.ofNat_ne_top)
  have hcore :
      (reflectedWholeLineAdjointGlobalRestrictionOperator g a c b :
        cc20GlobalLogCrossingL2 →
          Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) =
        (reflectedWholeLineAdjointNamedRestrictionOperator g a c b :
          cc20GlobalLogCrossingL2 →
            Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))) ∘
          (fun u : SchwartzMap ℝ ℂ => u.toLp 2) := by
    funext u
    rw [Function.comp_apply, Function.comp_apply]
    rw [reflectedWholeLineAdjointGlobalRestrictionOperator,
      reflectedWholeLineAdjointNamedRestrictionOperator]
    simp only [ContinuousLinearMap.comp_apply]
    rw [globalL2ToKernelInterval_apply_schwartzToLp]
    rw [reflectedWholeLineAdjointFiniteOperator_core g u a c b hsupp]
    rw [cc20GlobalLogConvolution_toLp]
    exact (globalL2ToKernelInterval_apply_schwartzToLp
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
        g.involution.test u) (-c) (-a) b).symm
  have hfun := DenseRange.equalizer hdense
    (reflectedWholeLineAdjointGlobalRestrictionOperator g a c b).continuous
    (reflectedWholeLineAdjointNamedRestrictionOperator g a c b).continuous hcore
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

theorem reflectedWholeLineAdjointNamedRestrictionOperator_eq_leftFactor_adjoint
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ) :
    reflectedWholeLineAdjointNamedRestrictionOperator g a c b =
      (reflectedWholeLineLeftFactor g a c b).adjoint := by
  rw [reflectedWholeLineAdjointNamedRestrictionOperator,
    reflectedWholeLineLeftFactor]
  rw [ContinuousLinearMap.adjoint_comp]
  have hext : (kernelIntervalL2ZeroExtension (-c) (-a) b).adjoint =
      globalL2ToKernelInterval (-c) (-a) b := by
    rw [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval]
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [hext]
  rw [← globalLogConvolution_involution_eq_adjoint]

theorem reflectedWholeLineAdjointGlobalRestrictionOperator_eq_leftFactor_adjoint
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c) :
    reflectedWholeLineAdjointGlobalRestrictionOperator g a c b =
      (reflectedWholeLineLeftFactor g a c b).adjoint := by
  exact (reflectedWholeLineAdjointGlobalRestrictionOperator_eq_named
    g a c b hsupp).trans
      (reflectedWholeLineAdjointNamedRestrictionOperator_eq_leftFactor_adjoint
        g a c b)

theorem reflectedWholeLineAdjointGlobalRestrictionOperator_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    Summable fun j =>
      ‖reflectedWholeLineAdjointGlobalRestrictionOperator g a c b
        (globalBasis j)‖ ^ 2 := by
  let finiteOp := reflectedWholeLineAdjointFiniteOperator g a c b
  let restrictOp := globalL2ToKernelInterval
    (a - c - b) (c - a + b) 0
  let globalOp := reflectedWholeLineAdjointGlobalRestrictionOperator g a c b
  have hfinite : Summable fun t => ‖finiteOp (inputBasis t)‖ ^ 2 := by
    exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))
      (volume : Measure (KernelInterval (-c) (-a) b))
      (reflectedWholeLineAdjointKernel g a c b) inputBasis
  have hfiniteAdjoint : Summable fun k =>
      ‖finiteOp.adjoint (factorBasis k)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      inputBasis factorBasis finiteOp hfinite
  have hglobalAdjoint : Summable fun k =>
      ‖globalOp.adjoint (factorBasis k)‖ ^ 2 := by
    have hadjoint : globalOp.adjoint = restrictOp.adjoint.comp finiteOp.adjoint := by
      dsimp only [globalOp, restrictOp, finiteOp,
        reflectedWholeLineAdjointGlobalRestrictionOperator]
      rw [ContinuousLinearMap.adjoint_comp]
    rw [hadjoint]
    apply hfiniteAdjoint.congr
    intro k
    rw [ContinuousLinearMap.comp_apply]
    dsimp only [restrictOp]
    rw [norm_globalL2ToKernelInterval_adjoint_apply]
  have hcycled :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      factorBasis globalBasis globalOp.adjoint hglobalAdjoint
  change Summable fun j => ‖globalOp (globalBasis j)‖ ^ 2
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hcycled

theorem reflectedWholeLineLeftFactor_summable
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    Summable fun k =>
      ‖reflectedWholeLineLeftFactor g a c b (factorBasis k)‖ ^ 2 := by
  have hadjoint : Summable fun j =>
      ‖(reflectedWholeLineLeftFactor g a c b).adjoint
        (globalBasis j)‖ ^ 2 := by
    rw [← reflectedWholeLineAdjointGlobalRestrictionOperator_eq_leftFactor_adjoint
      g a c b hsupp]
    exact reflectedWholeLineAdjointGlobalRestrictionOperator_summable
      g a c b inputBasis factorBasis globalBasis
  have hcycled :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      globalBasis factorBasis
      (reflectedWholeLineLeftFactor g a c b).adjoint hadjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hcycled

/-- The whole-line crossing written as one same-object Hilbert--Schmidt pair.
This owner supplies both diagonal trace legality and genuine compactness. -/
noncomputable def globalConvolutionCrossingPairData
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b)))
      globalBasis := by
  let leftFactor := reflectedWholeLineLeftFactor g a c b
  let rightBoundary := (reflectedWholeLineRightFactor g a c b).comp
    (globalL2ToSourceInterval b)
  have hleft : Summable fun k =>
      ‖leftFactor (factorBasis k)‖ ^ 2 := by
    simpa only [leftFactor] using reflectedWholeLineLeftFactor_summable
      g a c b hsupp inputBasis factorBasis globalBasis
  have hleftAdjoint : Summable fun j =>
      ‖leftFactor.adjoint (globalBasis j)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      factorBasis globalBasis leftFactor hleft
  have hright : Summable fun j =>
      ‖rightBoundary (globalBasis j)‖ ^ 2 := by
    simpa only [rightBoundary] using reflectedWholeLineRightBoundary_summable
      g a c b factorBasis globalBasis
  exact
    { left := leftFactor.adjoint
      right := rightBoundary
      left_summable_normSq := hleftAdjoint
      right_summable_normSq := hright }

theorem globalConvolutionCrossingPairData_traceProduct_eq
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (globalConvolutionCrossingPairData g a c b hsupp
      inputBasis factorBasis globalBasis).traceProduct =
        cc20GlobalConvolutionCrossing g.involution.test b := by
  dsimp only [globalConvolutionCrossingPairData,
    PositiveTrace.BasisHilbertSchmidtPairData.traceProduct]
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact reflectedWholeLineCycleProduct_eq_globalConvolutionCrossing
    g a c b hsupp hb

theorem globalConvolutionCrossing_isTraceClassAlong
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20GlobalConvolutionCrossing g.involution.test b) := by
  rw [← globalConvolutionCrossingPairData_traceProduct_eq
    g a c b hsupp hb inputBasis factorBasis globalBasis]
  exact (globalConvolutionCrossingPairData g a c b hsupp
    inputBasis factorBasis globalBasis).traceProduct_isTraceClassAlong

theorem globalConvolutionCrossing_isCompactOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    IsCompactOperator
      (cc20GlobalConvolutionCrossing g.involution.test b) := by
  rw [← globalConvolutionCrossingPairData_traceProduct_eq
    g a c b hsupp hb inputBasis factorBasis globalBasis]
  exact (globalConvolutionCrossingPairData g a c b hsupp
    inputBasis factorBasis globalBasis).traceProduct_isCompactOperator
      factorBasis

theorem globalConvolutionCrossing_adjoint_isCompactOperator
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    IsCompactOperator
      (cc20GlobalConvolutionCrossing g.involution.test b).adjoint := by
  rw [← globalConvolutionCrossingPairData_traceProduct_eq
    g a c b hsupp hb inputBasis factorBasis globalBasis]
  exact (globalConvolutionCrossingPairData g a c b hsupp
    inputBasis factorBasis globalBasis).traceProduct_adjoint_isCompactOperator
      factorBasis

theorem namedSource_trace_eq_globalConvolutionCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι κ τ ν : Type*}
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong sourceBasis
        (namedSourceCrossingProduct g b) =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing g.involution.test b) := by
  exact namedSource_trace_eq_globalConvolutionCrossing_of_left_summable
    g a c b hsupp hb sourceBasis factorBasis globalBasis
      (reflectedWholeLineLeftFactor_summable
        g a c b hsupp inputBasis factorBasis globalBasis)

theorem pairData_trace_eq_globalConvolutionCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι κ τ ν σ : Type*}
    (compactBasis : HilbertBasis σ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong compactBasis
        (pairData g.test g.test.continuous a c b compactBasis).traceProduct =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing g.involution.test b) := by
  calc
    _ = PositiveTrace.ordinaryTraceAlong sourceBasis
        (namedSourceCrossingProduct g b) :=
      pairData_trace_eq_namedSourceCrossingProduct
        g a c b hsupp compactBasis sourceBasis
    _ = _ := namedSource_trace_eq_globalConvolutionCrossing
      g a c b hsupp hb sourceBasis inputBasis factorBasis globalBasis

theorem reversePairData_traceProduct_eq_pairData_adjoint
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b)))) :
    (reversePairData g.test g.test.continuous a c b basis).traceProduct =
      (pairData g.test g.test.continuous a c b basis).traceProduct.adjoint := by
  change
    (ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (KernelInterval a c b))
      (volume : Measure (SourceInterval b))
      (rightKernel g.test g.test.continuous a c b)).adjoint ∘L
        ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (KernelInterval a c b))
          (volume : Measure (SourceInterval b))
          (leftKernel g.test g.test.continuous a c b) =
      ((ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval a c b))
        (volume : Measure (SourceInterval b))
        (leftKernel g.test g.test.continuous a c b)).adjoint ∘L
          ContinuousKernelHilbertSchmidt.operator
            (volume : Measure (KernelInterval a c b))
            (volume : Measure (SourceInterval b))
            (rightKernel g.test g.test.continuous a c b)).adjoint
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem reversePairData_trace_eq_globalConvolutionCrossing_adjoint
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {ι κ τ ν σ : Type*}
    (compactBasis : HilbertBasis σ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c b))))
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2
        (volume : Measure (ReflectedWholeLineAdjointInputInterval a c b))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    PositiveTrace.ordinaryTraceAlong compactBasis
        (reversePairData g.test g.test.continuous
          a c b compactBasis).traceProduct =
      PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing g.involution.test b).adjoint := by
  calc
    _ = PositiveTrace.ordinaryTraceAlong compactBasis
        (pairData g.test g.test.continuous
          a c b compactBasis).traceProduct.adjoint := congrArg
      (PositiveTrace.ordinaryTraceAlong compactBasis)
      (reversePairData_traceProduct_eq_pairData_adjoint
        g a c b compactBasis)
    _ = star (PositiveTrace.ordinaryTraceAlong compactBasis
        (pairData g.test g.test.continuous
          a c b compactBasis).traceProduct) :=
      PositiveTrace.ordinaryTraceAlong_adjoint _ _
    _ = star (PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing g.involution.test b)) := congrArg star
      (pairData_trace_eq_globalConvolutionCrossing
        g a c b hsupp hb compactBasis sourceBasis inputBasis factorBasis
          globalBasis)
    _ = _ := (PositiveTrace.ordinaryTraceAlong_adjoint _ _).symm

theorem eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν σ : Type*} [Countable σ]
    (compactBasis : HilbertBasis σ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval a c
        ((m : ℝ) * Real.log (p : ℝ))))))
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure
        (SourceInterval ((m : ℝ) * Real.log (p : ℝ))))))
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (ReflectedWholeLineAdjointInputInterval
        a c ((m : ℝ) * Real.log (p : ℝ))))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a)
        ((m : ℝ) * Real.log (p : ℝ))))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
        (PositiveTrace.ordinaryTraceAlong globalBasis
            (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
              ((m : ℝ) * Real.log (p : ℝ))) +
          PositiveTrace.ordinaryTraceAlong globalBasis
            (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
              ((m : ℝ) * Real.log (p : ℝ))).adjoint) =
      owner.finitePrimeTerm (p ^ m) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hb : 0 ≤ (m : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hp_one)
  have hforward := pairData_trace_eq_globalConvolutionCrossing
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      compactBasis sourceBasis inputBasis factorBasis globalBasis
  have hreverse := reversePairData_trace_eq_globalConvolutionCrossing_adjoint
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      compactBasis sourceBasis inputBasis factorBasis globalBasis
  rw [← hforward, ← hreverse]
  exact eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow
    owner a c hp hm hsupp compactBasis

theorem positiveInterval_eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow
    (source :
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    {ι κ τ ν σ : Type*} [Countable σ]
    (compactBasis : HilbertBasis σ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval
        (Real.log source.lower) (Real.log source.upper)
        ((m : ℝ) * Real.log (p : ℝ))))))
    (sourceBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure
        (SourceInterval ((m : ℝ) * Real.log (p : ℝ))))))
    (inputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (ReflectedWholeLineAdjointInputInterval
        (Real.log source.lower) (Real.log source.upper)
        ((m : ℝ) * Real.log (p : ℝ))))))
    (factorBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval
        (-(Real.log source.upper)) (-(Real.log source.lower))
        ((m : ℝ) * Real.log (p : ℝ))))))
    (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2) :
    (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
        (PositiveTrace.ordinaryTraceAlong globalBasis
            (cc20GlobalConvolutionCrossing
              (positiveIntervalSquareOwner source).sourceTest.involution.test
              ((m : ℝ) * Real.log (p : ℝ))) +
          PositiveTrace.ordinaryTraceAlong globalBasis
            (cc20GlobalConvolutionCrossing
              (positiveIntervalSquareOwner source).sourceTest.involution.test
              ((m : ℝ) * Real.log (p : ℝ))).adjoint) =
      (positiveIntervalSquareOwner source).finitePrimeTerm (p ^ m) := by
  apply eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow
    (positiveIntervalSquareOwner source)
    (Real.log source.lower) (Real.log source.upper) hp hm
    (by
      simpa only [positiveIntervalSquareOwner] using
        SelectedYoshidaBridge.compactLogTestOfPositiveIntervalCompactTest_support_subset
          source)
    compactBasis sourceBasis inputBasis factorBasis globalBasis

/-- The whole-line forward/adjoint trace atom at one named prime power.  The
definition deliberately contains no compact-factor basis: those bases are
analytic witnesses used to prove the read-off, not part of the arithmetic
main term consumed by a later semilocal owner. -/
noncomputable def eulerLogWeightedGlobalPairTraceAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (p m : ℕ) : ℂ :=
  (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) *
    (PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
          ((m : ℝ) * Real.log (p : ℝ))) +
      PositiveTrace.ordinaryTraceAlong globalBasis
        (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
          ((m : ℝ) * Real.log (p : ℝ))).adjoint)

/-- The actual whole-line single-crossing operator at one prime power, with
the Euler-log coefficient inserted before taking its ordinary trace. -/
noncomputable def eulerLogWeightedGlobalPairTraceOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p m : ℕ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ) •
    (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
        ((m : ℝ) * Real.log (p : ℝ)) +
      (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
        ((m : ℝ) * Real.log (p : ℝ))).adjoint)

theorem eulerLogWeightedGlobalPairTraceOperator_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p m : ℕ) :
    IsSelfAdjoint (eulerLogWeightedGlobalPairTraceOperator owner p m) := by
  rw [eulerLogWeightedGlobalPairTraceOperator]
  apply IsSelfAdjoint.smul
  · rw [← RCLike.im_eq_zero_iff_isSelfAdjoint]
    simp
  · simpa only [ContinuousLinearMap.star_eq_adjoint] using
      IsSelfAdjoint.add_star_self
        (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
          ((m : ℝ) * Real.log (p : ℝ)))

/-- The interval-dependent Hilbert bases needed to justify one whole-line
prime-power trace read-off.  Keeping these witnesses in one structure ensures
that the compact kernel, source window, reflected input, and reflected factor
all belong to the same `(p,m)` crossing length. -/
structure GlobalPrimePowerTraceBasisData
    (a c : ℝ) (p m : ℕ) where
  compactIndex : Type*
  sourceIndex : Type*
  inputIndex : Type*
  factorIndex : Type*
  compactCountable : Countable compactIndex
  compactBasis : HilbertBasis compactIndex ℂ
    (Lp ℂ 2 (volume : Measure (KernelInterval a c
      ((m : ℝ) * Real.log (p : ℝ)))))
  sourceBasis : HilbertBasis sourceIndex ℂ
    (Lp ℂ 2 (volume : Measure
      (SourceInterval ((m : ℝ) * Real.log (p : ℝ)))))
  inputBasis : HilbertBasis inputIndex ℂ
    (Lp ℂ 2 (volume : Measure (ReflectedWholeLineAdjointInputInterval
      a c ((m : ℝ) * Real.log (p : ℝ)))))
  factorBasis : HilbertBasis factorIndex ℂ
    (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a)
      ((m : ℝ) * Real.log (p : ℝ)))))

theorem eulerLogWeightedGlobalPairTraceOperator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p m) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (eulerLogWeightedGlobalPairTraceOperator owner p m) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hb : 0 ≤ (m : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hp_one)
  have hforward := globalConvolutionCrossing_isTraceClassAlong
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      basisData.inputBasis basisData.factorBasis globalBasis
  have hadjoint := PositiveTrace.isTraceClassAlong_adjoint globalBasis
    (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
      ((m : ℝ) * Real.log (p : ℝ))) hforward
  exact PositiveTrace.isTraceClassAlong_smul globalBasis _ _
    (PositiveTrace.isTraceClassAlong_add globalBasis _ _ hforward hadjoint)

theorem eulerLogWeightedGlobalPairTraceOperator_isCompactOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p m) :
    IsCompactOperator
      (eulerLogWeightedGlobalPairTraceOperator owner p m) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hb : 0 ≤ (m : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hp_one)
  have hforward := globalConvolutionCrossing_isCompactOperator
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      basisData.inputBasis basisData.factorBasis globalBasis
  have hadjoint := globalConvolutionCrossing_adjoint_isCompactOperator
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      basisData.inputBasis basisData.factorBasis globalBasis
  rw [eulerLogWeightedGlobalPairTraceOperator]
  exact (hforward.add hadjoint).smul
    (((1 / Real.sqrt ((p ^ m : ℕ) : ℝ)) / (m : ℝ) : ℝ) : ℂ)

theorem ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperator_eq_atom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p m) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperator owner p m) =
      eulerLogWeightedGlobalPairTraceAtom owner globalBasis p m := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hb : 0 ≤ (m : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hp_one)
  have hforward := globalConvolutionCrossing_isTraceClassAlong
    owner.sourceTest a c ((m : ℝ) * Real.log (p : ℝ)) hsupp hb
      basisData.inputBasis basisData.factorBasis globalBasis
  have hadjoint := PositiveTrace.isTraceClassAlong_adjoint globalBasis
    (cc20GlobalConvolutionCrossing owner.sourceTest.involution.test
      ((m : ℝ) * Real.log (p : ℝ))) hforward
  rw [eulerLogWeightedGlobalPairTraceOperator]
  rw [PositiveTrace.ordinaryTraceAlong_smul globalBasis _ _
    (PositiveTrace.isTraceClassAlong_add globalBasis _ _ hforward hadjoint)]
  rw [PositiveTrace.ordinaryTraceAlong_add globalBasis _ _ hforward hadjoint]
  rfl

theorem eulerLogWeightedGlobalPairTraceAtom_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p m) :
    eulerLogWeightedGlobalPairTraceAtom owner globalBasis p m =
      owner.finitePrimeTerm (p ^ m) := by
  letI : Countable basisData.compactIndex := basisData.compactCountable
  simpa only [eulerLogWeightedGlobalPairTraceAtom] using
    eulerLog_weighted_global_pair_traces_eq_finitePrimeTerm_pow
      owner a c hp hm hsupp basisData.compactBasis basisData.sourceBasis
        basisData.inputBasis basisData.factorBasis globalBasis

theorem ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperator_eq_finitePrimeTerm_pow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : GlobalPrimePowerTraceBasisData a c p m) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperator owner p m) =
      owner.finitePrimeTerm (p ^ m) := by
  rw [ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperator_eq_atom
    owner a c hp hsupp globalBasis basisData]
  exact eulerLogWeightedGlobalPairTraceAtom_eq_finitePrimeTerm_pow
    owner a c hp hm hsupp globalBasis basisData

/-- The finite-S single-crossing main operator assembled before taking a
trace. Every summand acts on the same whole-line Hilbert space and uses the
same selected convolution square. -/
noncomputable def eulerLogWeightedGlobalPairTraceOperatorSum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (terms : Finset (ℕ × ℕ)) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  ∑ pm ∈ terms,
    eulerLogWeightedGlobalPairTraceOperator owner pm.1 pm.2

theorem eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (terms : Finset (ℕ × ℕ)) :
    IsSelfAdjoint (eulerLogWeightedGlobalPairTraceOperatorSum owner terms) := by
  rw [eulerLogWeightedGlobalPairTraceOperatorSum]
  exact isSelfAdjoint_sum terms fun pm _ =>
    eulerLogWeightedGlobalPairTraceOperator_isSelfAdjoint owner pm.1 pm.2

theorem eulerLogWeightedGlobalPairTraceOperatorSum_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (eulerLogWeightedGlobalPairTraceOperatorSum owner terms) := by
  rw [eulerLogWeightedGlobalPairTraceOperatorSum]
  apply PositiveTrace.isTraceClassAlong_finset_sum globalBasis terms
  intro pm hpm
  exact eulerLogWeightedGlobalPairTraceOperator_isTraceClassAlong
    owner a c (hprime pm hpm) hsupp globalBasis (basisData ⟨pm, hpm⟩)

theorem eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    IsCompactOperator
      (eulerLogWeightedGlobalPairTraceOperatorSum owner terms) := by
  rw [eulerLogWeightedGlobalPairTraceOperatorSum]
  apply PositiveTrace.isCompactOperator_finset_sum terms
  intro pm hpm
  exact eulerLogWeightedGlobalPairTraceOperator_isCompactOperator
    owner a c (hprime pm hpm) hsupp globalBasis (basisData ⟨pm, hpm⟩)

theorem positiveInterval_operatorSum_isCompactOperator
    (source :
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData (Real.log source.lower)
        (Real.log source.upper) pm.1.1 pm.1.2) :
    IsCompactOperator
      (eulerLogWeightedGlobalPairTraceOperatorSum
        (positiveIntervalSquareOwner source) terms) := by
  exact eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator
    (positiveIntervalSquareOwner source) (Real.log source.lower)
      (Real.log source.upper) terms hprime (by
        simpa only [positiveIntervalSquareOwner] using
          SelectedYoshidaBridge.compactLogTestOfPositiveIntervalCompactTest_support_subset
            source) globalBasis basisData

theorem ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperatorSum owner terms) =
      ∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  rw [eulerLogWeightedGlobalPairTraceOperatorSum]
  rw [PositiveTrace.ordinaryTraceAlong_finset_sum globalBasis terms _]
  · apply Finset.sum_congr rfl
    intro pm hpm
    exact ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperator_eq_finitePrimeTerm_pow
      owner a c (hprime pm hpm) (hnonzero pm hpm) hsupp globalBasis
        (basisData ⟨pm, hpm⟩)
  · intro pm hpm
    exact eulerLogWeightedGlobalPairTraceOperator_isTraceClassAlong
      owner a c (hprime pm hpm) hsupp globalBasis (basisData ⟨pm, hpm⟩)

theorem positiveInterval_operatorSum_trace_eq_finitePrimeTerm_pow_sum
    (source :
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData (Real.log source.lower)
        (Real.log source.upper) pm.1.1 pm.1.2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (eulerLogWeightedGlobalPairTraceOperatorSum
          (positiveIntervalSquareOwner source) terms) =
      ∑ pm ∈ terms,
        (positiveIntervalSquareOwner source).finitePrimeTerm (pm.1 ^ pm.2) := by
  exact
    ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
      (positiveIntervalSquareOwner source) (Real.log source.lower)
        (Real.log source.upper) terms hprime hnonzero (by
          simpa only [positiveIntervalSquareOwner] using
            SelectedYoshidaBridge.compactLogTestOfPositiveIntervalCompactTest_support_subset
              source) globalBasis basisData

/-- Multi-prime assembly of the genuine whole-line forward/adjoint crossing
atoms.  Every summand uses the same selected convolution square and the same
whole-line Hilbert basis; only the finite-interval factorization witnesses vary
with the prime-power crossing length. -/
theorem eulerLogWeightedGlobalPairTraceAtom_sum_eq_finitePrimeTerm_pow_sum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    (∑ pm ∈ terms,
        eulerLogWeightedGlobalPairTraceAtom owner globalBasis pm.1 pm.2) =
      ∑ pm ∈ terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  apply Finset.sum_congr rfl
  intro pm hpm
  exact eulerLogWeightedGlobalPairTraceAtom_eq_finitePrimeTerm_pow
    owner a c (hprime pm hpm) (hnonzero pm hpm) hsupp globalBasis
      (basisData ⟨pm, hpm⟩)

theorem positiveInterval_eulerLogWeightedGlobalPairTraceAtom_sum_eq_finitePrimeTerm_pow_sum
    (source :
      CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest)
    (terms : Finset (ℕ × ℕ))
    (hprime : ∀ pm ∈ terms, pm.1.Prime)
    (hnonzero : ∀ pm ∈ terms, pm.2 ≠ 0)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ terms},
      GlobalPrimePowerTraceBasisData (Real.log source.lower)
        (Real.log source.upper) pm.1.1 pm.1.2) :
    (∑ pm ∈ terms,
        eulerLogWeightedGlobalPairTraceAtom (positiveIntervalSquareOwner source)
          globalBasis pm.1 pm.2) =
      ∑ pm ∈ terms,
        (positiveIntervalSquareOwner source).finitePrimeTerm (pm.1 ^ pm.2) := by
  exact eulerLogWeightedGlobalPairTraceAtom_sum_eq_finitePrimeTerm_pow_sum
    (positiveIntervalSquareOwner source) (Real.log source.lower)
      (Real.log source.upper) terms hprime hnonzero (by
        simpa only [positiveIntervalSquareOwner] using
          SelectedYoshidaBridge.compactLogTestOfPositiveIntervalCompactTest_support_subset
            source) globalBasis basisData

end SelectedCrossingOperatorBridge
end CCM25Concrete
end Source
end ConnesWeilRH
