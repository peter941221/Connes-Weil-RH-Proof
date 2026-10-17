import ConnesWeilRH.Dev.C1RationalProductJet2747
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def rationalExponentialJet2750
    (X : ℕ → RationalBox2744) (e0 : RationalBox2744) : ℕ → RationalBox2744
  | 0 => e0
  | n + 1 =>
    RationalBox2744.sum
      (fun j => RationalBox2744.nsmul (n.choose j : ℚ) (by positivity)
        (RationalBox2744.mul (X (j + 1))
          (rationalExponentialJet2750 X e0 (n - j)))) (n + 1)
termination_by n => n
decreasing_by omega

theorem rationalExponentialJet_mem2750
    (X : ℕ → RationalBox2744) (e0 : RationalBox2744) (N : ℕ)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (he0 : e0.Mem (transitionExp2731 x))
    (hX : ∀ j ≤ N, (X j).Mem (iteratedDeriv j transitionPhase2731 x)) :
    ∀ n ≤ N, (rationalExponentialJet2750 X e0 n).Mem
      (iteratedDeriv n transitionExp2731 x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simpa only [rationalExponentialJet2750, iteratedDeriv_zero] using he0
    | succ m =>
      rw [rationalExponentialJet2750,
        iteratedDeriv_transitionExp2731 m hx0 hx1]
      apply RationalBox2744.mem_sum
      intro j hj
      have hslot := RationalBox2744.mem_nsmul
        (c := (m.choose j : ℚ)) (by positivity)
        (RationalBox2744.mem_mul (hX (j + 1) (by omega))
          (ih (m - j) (by omega) (by omega)))
      simpa [mul_assoc] using hslot

end
end ConnesWeilRH.Dev
