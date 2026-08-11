import ConnesWeilRH.Dev.Wall14PlateauFDeriv

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

noncomputable def bd (u : ℝ) : ℝ := deriv (fun w : ℝ => bumpReal w) u

lemma bd_continuous : Continuous bd := by
  have hcf : Continuous (fun x : ℝ => fderiv ℝ (fun w : ℝ => bumpReal w) x) :=
    bumpReal_contDiff_one.continuous_fderiv (by norm_num)
  have hbc : Continuous (fun u : ℝ => ((fderiv ℝ (fun w : ℝ => bumpReal w) u) : ℝ →L[ℝ] ℝ) 1) := by
    fun_prop
  simpa [bd] using hbc

end ConnesWeilRH.Source.Dev.Wall14Plateau
