/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Analytic finite-window uniqueness bridge

This module separates the topological uniqueness step from the missing source
producer.  A representative which is analytic on the whole real line and is
zero almost everywhere on a nontrivial interval is zero everywhere.  The
restriction operator used by the full-boundary chain is then converted from
its subtype `KernelInterval` carrier back to the ambient restricted measure.

No theorem here constructs an analytic representative for the current root
convolution.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedAnalyticWindowUniquenessBridge

open MeasureTheory
open Set
open scoped FourierTransform Topology

open CC20Concrete
open CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge

theorem analytic_eq_zero_of_ae_eq_zero_on_Icc
    (d e : ℝ) (hde : d < e) {f : ℝ → ℂ}
    (hanalytic : AnalyticOnNhd ℝ f Set.univ)
    (hzero : ∀ᵐ x ∂(volume.restrict (Set.Icc d e)), f x = 0) :
    ∀ x : ℝ, f x = 0 := by
  have hzeroOpen : ∀ᵐ x ∂(volume.restrict (Set.Ioo d e)), f x = 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hzero
  have hzeroOn : EqOn f 0 (Set.Ioo d e) :=
    Measure.eqOn_Ioo_of_ae_eq (volume : Measure ℝ) hzeroOpen
      hanalytic.continuous.continuousOn continuous_const.continuousOn
  let x₀ : ℝ := (d + e) / 2
  have hx₀ : x₀ ∈ Set.Ioo d e := by
    dsimp [x₀]
    constructor <;> linarith
  have hfrequently : ∃ᶠ x in 𝓝[≠] x₀, f x = 0 := by
    have heventually : ∀ᶠ x in 𝓝[≠] x₀, x ∈ Set.Ioo d e :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioo_mem_nhds hx₀.1 hx₀.2)
    exact (heventually.mono fun x hx => hzeroOn hx).frequently
  have hglobal : EqOn f 0 Set.univ :=
    hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ x₀) hfrequently
  intro x
  exact hglobal (Set.mem_univ x)

theorem globalL2ToKernelInterval_zero_implies_ae_zero_on_Icc
    (a c b : ℝ) (u : cc20GlobalLogCrossingL2)
    (hzero : globalL2ToKernelInterval a c b u = 0) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc (a - b) (c + b))), u x = 0 := by
  have hzeroFn :
      (globalL2ToKernelInterval a c b u : KernelInterval a c b → ℂ) =ᵐ[volume] 0 := by
    exact (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  have hsubtype :
      ∀ᵐ x ∂(volume : Measure (KernelInterval a c b)), u x.1 = 0 := by
    filter_upwards [globalL2ToKernelInterval_coeFn a c b u, hzeroFn]
      with x hread hzeroAt
    rw [hread] at hzeroAt
    exact hzeroAt
  apply (ae_restrict_iff_subtype measurableSet_Icc).2
  simpa only [volume_set_coe_def] using hsubtype

theorem cc20GlobalLogConvolution_eq_zero_of_analytic_representative_of_kernelInterval_zero
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2)
    (a c b : ℝ) (hwidth : a - b < c + b)
    (f : ℝ → ℂ)
    (hanalytic : AnalyticOnNhd ℝ f Set.univ)
    (hrep : f =ᵐ[(volume : Measure ℝ)]
      (cc20GlobalLogConvolution h u : ℝ → ℂ))
    (hwindow : globalL2ToKernelInterval a c b
      (cc20GlobalLogConvolution h u) = 0) :
    cc20GlobalLogConvolution h u = 0 := by
  have hwindowAe :
      ∀ᵐ x ∂(volume.restrict (Set.Icc (a - b) (c + b))),
        (cc20GlobalLogConvolution h u : ℝ → ℂ) x = 0 :=
    globalL2ToKernelInterval_zero_implies_ae_zero_on_Icc a c b
      (cc20GlobalLogConvolution h u) hwindow
  have hrepRestrict :
      f =ᵐ[(volume : Measure ℝ).restrict (Set.Icc (a - b) (c + b))]
        (cc20GlobalLogConvolution h u : ℝ → ℂ) :=
    ae_restrict_of_ae hrep
  have hzeroRestrict :
      ∀ᵐ x ∂(volume.restrict (Set.Icc (a - b) (c + b))), f x = 0 := by
    filter_upwards [hrepRestrict, hwindowAe] with x hrepAt hwindowAt
    exact hrepAt.trans hwindowAt
  have hglobal := analytic_eq_zero_of_ae_eq_zero_on_Icc
    (a - b) (c + b) hwidth hanalytic hzeroRestrict
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hrep] with x hrepAt
  exact hrepAt.symm.trans (hglobal x)

end CCM24FiniteSFixedAnalyticWindowUniquenessBridge
end CCM25Concrete
end Source
end ConnesWeilRH
