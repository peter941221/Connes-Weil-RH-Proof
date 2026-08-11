import ConnesWeilRH.Dev.Wall14PlateauFDeriv

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

lemma bump_real_neg (x : ℝ) : bumpReal (-x) = bumpReal x := bumpReal_even x

-- derivative of even function is odd
lemma deriv_bumpReal_neg_neg (x : ℝ) :
    deriv (fun t : ℝ => bumpReal t) (-x) = -deriv (fun t : ℝ => bumpReal t) x := by
  have hodd : HasDerivAt (fun t : ℝ => bumpReal (-(-t))) ... := by
  simp [bumpReal_even]

end ConnesWeilRH.Source.Dev.Wall14Plateau
