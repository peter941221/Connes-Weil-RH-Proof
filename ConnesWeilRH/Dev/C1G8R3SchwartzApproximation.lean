/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelReadbackSchwartzL2Tendsto

/-!
# Schwartz sequence approximation in L2

The Schwartz-to-Lp map has dense range.  Since the target L2 space is metric,
the density is converted into an explicit sequential approximation, which is
the input required by the complete kernel-readback socket.
-/

namespace ConnesWeilRH
namespace Dev

open Filter MeasureTheory
open scoped Topology

theorem exists_schwartz_l2_tendsto
    {u : Lp ℂ 2 (volume : Measure ℝ)} :
    ∃ u_seq : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n => (u_seq n).toLp 2) atTop (𝓝 u) := by
  let F : SchwartzMap ℝ ℂ → Lp ℂ 2 (volume : Measure ℝ) :=
    fun s => s.toLp 2
  have hF : DenseRange F := by
    simpa [F] using
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
        (p := 2) (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top)
  have hu_cl : u ∈ closure (Set.range F) := hF u
  have hchoice : ∀ n : ℕ, ∃ s : SchwartzMap ℝ ℂ,
      dist (F s) u < (1 : ℝ) / (n + 1) := by
    intro n
    obtain ⟨v, hv, hvu⟩ :=
      (Metric.mem_closure_iff.1 hu_cl) ((1 : ℝ) / (n + 1)) (by positivity)
    rcases hv with ⟨s, rfl⟩
    exact ⟨s, by simpa [dist_comm] using hvu⟩
  let u_seq : ℕ → SchwartzMap ℝ ℂ := fun n => (hchoice n).choose
  have hdist : ∀ n : ℕ,
      dist (F (u_seq n)) u < (1 : ℝ) / (n + 1) := by
    intro n
    exact (hchoice n).choose_spec
  refine ⟨u_seq, ?_⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hNprod : 1 < ε * (N : ℝ) := by
    have hN' := (div_lt_iff₀ hε).mp hN
    simpa [mul_comm] using hN'
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : ε * (N : ℝ) ≤ ε * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnreal (le_of_lt hε)
  have hden : 1 ≤ ε * ((n : ℝ) + 1) := by
    nlinarith
  have hfrac : (1 : ℝ) / ((n : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hnpos]
    exact hden
  exact (hdist n).trans_le (by simpa [Nat.cast_add, Nat.cast_one] using hfrac)

end Dev
end ConnesWeilRH
