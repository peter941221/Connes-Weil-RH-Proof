/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelL2LimitAeIdentification
import ConnesWeilRH.Dev.C1G8R3KernelReadbackLpCore

/-!
# L2-limit kernel readback

This leaf combines the representative-level subsequence argument with the
root convolution operator.  It is the exact conditional interface needed by
the annular S3 consumer: L2 convergence of an approximating input sequence,
a.e. kernel readback for every approximant, and pointwise convergence of the
honest row integrals imply a.e. readback for the limiting input.

No regularity of arbitrary L2 inputs and no diagonal bound are assumed here;
those remain the analytic instantiation obligations.
-/

namespace ConnesWeilRH
namespace Dev

open Filter MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CompactLogConvolution
open scoped Topology

theorem ae_eq_of_lp_operator_tendsto_of_ae_readback
    {v : Lp ℂ 2 (volume : Measure ℝ)}
    {v_seq : ℕ → Lp ℂ 2 (volume : Measure ℝ)}
    {r : ℝ → ℂ} {r_seq : ℕ → ℝ → ℂ}
    (hLp : Tendsto v_seq atTop (𝓝 v))
    (hread : ∀ n, (v_seq n : ℝ → ℂ) =ᵐ[volume] r_seq n)
    (hpoint : ∀ x, Tendsto (fun n => r_seq n x) atTop (𝓝 (r x))) :
    (v : ℝ → ℂ) =ᵐ[volume] r := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  have hrep_all : ∀ᵐ x : ℝ, ∀ i : ℕ,
      (v_seq (ns i) : ℝ → ℂ) x = r_seq (ns i) x := by
    rw [ae_all_iff]
    intro i
    exact hread (ns i)
  have hsub_raw : ∀ᵐ x : ℝ, Tendsto
      (fun i => r_seq (ns i) x) atTop (𝓝 ((v : ℝ → ℂ) x)) := by
    filter_upwards [hsub, hrep_all] with x hx hrep
    exact hx.congr' (Eventually.of_forall hrep)
  have hpoint_sub : ∀ᵐ x : ℝ, Tendsto
      (fun i => r_seq (ns i) x) atTop (𝓝 (r x)) := by
    exact Eventually.of_forall fun x =>
      (hpoint x).comp hns.tendsto_atTop
  exact AEEqFun.tendsto_ae_unique hsub_raw hpoint_sub

theorem sourceKernelReadback_ae_of_l2_limit
    (g : CompactLogTest) {u : ℝ → ℂ} {u_seq : ℕ → ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hu_seq : ∀ n, MemLp (u_seq n) 2 (volume : Measure ℝ))
    (hLp : Tendsto
      (fun n => (hu_seq n).toLp (u_seq n)) atTop
        (𝓝 (hu.toLp u)))
    (hread : ∀ n,
      (cc20GlobalLogConvolution g.involution.test
        ((hu_seq n).toLp (u_seq n)) : ℝ → ℂ) =ᵐ[volume]
        (fun t : ℝ => ∫ x : ℝ,
          u_seq n x * star (g.test (x - t))))
    (hpoint : ∀ t, Tendsto
      (fun n => ∫ x : ℝ, u_seq n x * star (g.test (x - t))) atTop
        (𝓝 (∫ x : ℝ, u x * star (g.test (x - t))))) :
    (cc20GlobalLogConvolution g.involution.test
      (hu.toLp u) : ℝ → ℂ) =ᵐ[volume]
      (fun t : ℝ => ∫ x : ℝ, u x * star (g.test (x - t))) := by
  apply ae_eq_of_lp_operator_tendsto_of_ae_readback
    (hLp :=
      ((cc20GlobalLogConvolution g.involution.test).continuous.tendsto _).comp
        hLp)
    (hread := hread)
    (hpoint := hpoint)

end Dev
end ConnesWeilRH
