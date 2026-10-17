import ConnesWeilRH.Dev.C1RationalProductJet2747
import ConnesWeilRH.Dev.C1SeedJetSemantics2731

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def rationalTransitionJet2749
    (E D : ℕ → RationalBox2744) (n : ℕ) : RationalBox2744 :=
  rationalProductJet2747 E D n

theorem rationalTransitionJet_mem2749
    (E D : ℕ → RationalBox2744) (n : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hE : ∀ j ≤ n, (E j).Mem (iteratedDeriv j transitionExp2731 x))
    (hD : ∀ j ≤ n, (D j).Mem (iteratedDeriv j transitionReciprocal2731 x)) :
    (rationalTransitionJet2749 E D n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  rw [ConnesWeilRH.Source.C1ExplicitSmoothSeed.iteratedDeriv_smoothTransition_product2731
    n hx0 hx1]
  exact rationalProductJet_mem2747 E D n
    (fun j => iteratedDeriv j transitionExp2731 x)
    (fun j => iteratedDeriv j transitionReciprocal2731 x)
    hE hD

end
end ConnesWeilRH.Dev
