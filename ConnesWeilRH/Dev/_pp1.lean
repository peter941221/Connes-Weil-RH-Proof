import ConnesWeilRH.Dev.Wall14PlateauFDeriv

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory

noncomputable def bd (u : ℝ) : ℝ := deriv (fun w : ℝ => bumpReal w) u

-- 1) bumpFderiv unfolds to the convolution integral (in t).
lemma bumpFderiv_as_int (x : ℝ) :
    bumpFderiv x = ∫ t : ℝ, bumpReal t * (bd (x - t)) := by
  rw [bumpFderiv]
  rw [convolution_def]
  rfl

end ConnesWeilRH.Source.Dev.Wall14Plateau
