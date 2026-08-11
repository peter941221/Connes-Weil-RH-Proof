import ConnesWeilRH.Dev.Wall14PlateauProbe
open MeasureTheory
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

lemma plateauAffine_hasCompactSupport (y : ℝ) :
    HasCompactSupport (fun t : ℝ => plateauReal (y - t)) := by
  change IsCompact (tsupport _)
  let B : Set ℝ := Metric.closedBall (0 : ℝ) 1
  have hB : tsupport plateauReal = B := by
    have ht := ContDiffBump.tsupport_eq plateauBump
    simpa [plateauReal, B] using ht
  let pre : Set ℝ := (fun u : ℝ => y - u) ⁻¹' B
  have hsuppfun : Function.support (fun t : ℝ => plateauReal (y - t)) ⊆ pre := by
    intro t ht
    have hts : y - t ∈ tsupport plateauReal :=
      subset_tsupport _ (by simpa [Function.mem_support] using ht)
    simpa [pre] using (by rwa [hB] at hts)
  have hpre_closed : IsClosed pre := by
    exact (continuous_const.sub continuous_id).isClosed_preimage Metric.isClosed_closedBall
  have hsubcl : closure (Function.support (fun t : ℝ => plateauReal (y - t))) ⊆ pre := by
    have h1 : closure (Function.support (fun t : ℝ => plateauReal (y - t))) ⊆ pre := from? 
  sorry
end ConnesWeilRH.Source.Dev.Wall14Plateau

