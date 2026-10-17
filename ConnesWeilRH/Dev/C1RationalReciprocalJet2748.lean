import ConnesWeilRH.Dev.C1RationalProductJet2747
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Dev
noncomputable section

def rationalReciprocalJet2748 (X : ℕ → RationalBox2744) (hpos : 0 < (X 0).lo) : ℕ → RationalBox2744
  | 0 => (X 0).invPositive hpos
  | n + 1 =>
    (RationalBox2744.zero.sub
      (RationalBox2744.sum
        (fun j => RationalBox2744.nsmul ((n + 1).choose (j + 1) : ℚ) (by positivity)
          (RationalBox2744.mul (X (j + 1))
            (rationalReciprocalJet2748 X hpos (n - j)))) (n + 1))).mul
      ((X 0).invPositive hpos)
termination_by n => n
decreasing_by omega

theorem rationalReciprocalJet_mem2748
    (X : ℕ → RationalBox2744) (hpos : 0 < (X 0).lo)
    (f : ℝ → ℝ) (N : ℕ) {x : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (hX : ∀ j ≤ N, (X j).Mem (iteratedDeriv j f x))
    (hfx : f x ≠ 0) :
    ∀ n ≤ N, (rationalReciprocalJet2748 X hpos n).Mem
      (iteratedDeriv n (fun y => (f y)⁻¹) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero =>
      simpa only [rationalReciprocalJet2748, iteratedDeriv_zero] using
        RationalBox2744.mem_invPositive hpos (hX 0 (by omega))
    | succ m =>
      rw [rationalReciprocalJet2748,
        ConnesWeilRH.Source.C1ExplicitSmoothSeed.iteratedDeriv_reciprocal_general2734 f m
          (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfx]
      apply RationalBox2744.mem_mul
      · have hsum :
          (RationalBox2744.sum
            (fun j => RationalBox2744.nsmul ((m + 1).choose (j + 1) : ℚ)
              (by positivity)
              (RationalBox2744.mul (X (j + 1))
                (rationalReciprocalJet2748 X hpos (m - j)))) (m + 1)).Mem
            (∑ j ∈ Finset.range (m + 1),
              (m + 1).choose (j + 1) * iteratedDeriv (j + 1) f x *
                iteratedDeriv (m - j) (fun y => (f y)⁻¹) x) := by
            apply RationalBox2744.mem_sum
            intro j hj
            have hslot := RationalBox2744.mem_nsmul
              (c := ((m + 1).choose (j + 1) : ℚ)) (by positivity)
              (RationalBox2744.mem_mul (hX (j + 1) (by omega))
                (ih (m - j) (by omega) (by omega)))
            simpa [mul_assoc] using hslot
        have hz : RationalBox2744.zero.Mem 0 := by
          simp [RationalBox2744.Mem, RationalBox2744.zero]
        simpa only [zero_sub] using RationalBox2744.mem_sub
          (RationalBox2744.mem_toRealInterval hz) hsum
      · exact RationalBox2744.mem_invPositive hpos (hX 0 (by omega))

end
end ConnesWeilRH.Dev
