import ConnesWeilRH.Dev.C1RationalE0Box2751

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

theorem unitRationalExponentialJet_mem2752
    (X : ℕ → RationalBox2744) (N : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hxhalf : x ≤ (1 / 2 : ℝ))
    (hX : ∀ j ≤ N, (X j).Mem (iteratedDeriv j transitionPhase2731 x)) :
    ∀ n ≤ N, (rationalExponentialJet2750 X unitExpBox2751 n).Mem
      (iteratedDeriv n transitionExp2731 x) := by
  apply rationalExponentialJet_mem2750 X unitExpBox2751 N hx0
    (by linarith)
    (unitExpBox_mem_of_half2751 hx0 hxhalf)
  exact hX

end
end ConnesWeilRH.Dev
