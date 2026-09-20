/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelRowPointwiseTendsto
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A.e. identification of an L2 limit with a pointwise row limit

If canonical L2 representatives converge in L2 and the corresponding raw
functions converge pointwise, the two limiting representatives agree almost
everywhere.  The proof extracts an a.e.-convergent subsequence from
convergence in measure and uses uniqueness of metric limits.  This is the
global representative-identification socket for the root row readback.
-/

namespace ConnesWeilRH
namespace Dev

open Filter MeasureTheory
open Source.CCM25Concrete.CompactLogConvolution
open scoped Topology

theorem ae_eq_of_lp_tendsto_of_pointwise_tendsto
    {u : ℝ → ℂ} {u_seq : ℕ → ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hu_seq : ∀ n, MemLp (u_seq n) 2 (volume : Measure ℝ))
    (hLp : Tendsto
      (fun n => (hu_seq n).toLp (u_seq n)) atTop
        (𝓝 (hu.toLp u)))
    (hpoint : ∀ x, Tendsto (fun n => u_seq n x) atTop (𝓝 (u x))) :
    (hu.toLp u : ℝ → ℂ) =ᵐ[volume] u := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
  have hrep_all : ∀ᵐ x : ℝ, ∀ i : ℕ,
      ((hu_seq (ns i)).toLp (u_seq (ns i)) : ℝ → ℂ) x = u_seq (ns i) x := by
    rw [ae_all_iff]
    intro i
    exact (hu_seq (ns i)).coeFn_toLp
  have hsub_raw : ∀ᵐ x : ℝ, Tendsto
      (fun i => u_seq (ns i) x) atTop
        (𝓝 ((hu.toLp u : ℝ → ℂ) x)) := by
    filter_upwards [hsub, hrep_all] with x hx hrep
    exact hx.congr' (Eventually.of_forall hrep)
  have hpoint_sub : ∀ᵐ x : ℝ, Tendsto
      (fun i => u_seq (ns i) x) atTop (𝓝 (u x)) := by
    exact Eventually.of_forall fun x =>
      (hpoint x).comp hns.tendsto_atTop
  exact AEEqFun.tendsto_ae_unique hsub_raw hpoint_sub

end Dev
end ConnesWeilRH
