import ConnesWeilRH.Dev.C1ExplicitFiniteNodeCorrection
import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction

noncomputable section

theorem l1Mass_correction_le
    (nodes : Finset ℂ) (seed : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (y : ℂ → ℂ) :
    CC20YoshidaCriticalContraction.CompactLogTest.l1Mass
        (correction nodes seed y) ≤
      ∑ z ∈ nodes,
        ‖y z / (nodeProduct nodes z z * laplaceAt seed 0)‖ *
          CC20YoshidaCriticalContraction.CompactLogTest.l1Mass
            (cardinalRaw nodes seed z) := by
  unfold CC20YoshidaCriticalContraction.CompactLogTest.l1Mass
  simp only [correction, SchwartzMap.sum_apply]
  change (∫ x : ℝ, ‖∑ z ∈ nodes,
      (y z / (nodeProduct nodes z z * laplaceAt seed 0)) •
        (cardinalRaw nodes seed z).test x‖) ≤ _
  have hleft : Integrable (fun x : ℝ =>
      ‖∑ z ∈ nodes,
        (y z / (nodeProduct nodes z z * laplaceAt seed 0)) •
          (cardinalRaw nodes seed z).test x‖) := by
    fun_prop
  have hright : Integrable (fun x : ℝ =>
      ∑ z ∈ nodes,
        ‖y z / (nodeProduct nodes z z * laplaceAt seed 0)‖ *
          ‖(cardinalRaw nodes seed z).test x‖) := by
    fun_prop
  calc
    _ ≤ ∫ x : ℝ, ∑ z ∈ nodes,
        ‖y z / (nodeProduct nodes z z * laplaceAt seed 0)‖ *
          ‖(cardinalRaw nodes seed z).test x‖ := by
      apply integral_mono_ae hleft hright
      filter_upwards with x
      simpa only [norm_smul] using
        (norm_sum_le (s := nodes)
          (fun z =>
            (y z / (nodeProduct nodes z z * laplaceAt seed 0)) •
              (cardinalRaw nodes seed z).test x))
    _ = ∑ z ∈ nodes,
        ‖y z / (nodeProduct nodes z z * laplaceAt seed 0)‖ *
          ∫ x : ℝ, ‖(cardinalRaw nodes seed z).test x‖ := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro z hz
        exact ((cardinalRaw nodes seed z).test.integrable.norm.const_mul _)
    _ = _ := by
      rfl

end
end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection