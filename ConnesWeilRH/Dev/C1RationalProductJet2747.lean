import ConnesWeilRH.Dev.C1RationalBoxBridge2744

namespace ConnesWeilRH.Dev

noncomputable section

def rationalProductJet2747 (X Y : ℕ → RationalBox2744) (n : ℕ) : RationalBox2744 :=
  RationalBox2744.sum
    (fun j =>
      RationalBox2744.nsmul (n.choose j : ℚ) (by positivity)
        (RationalBox2744.mul (X j) (Y (n - j)))) (n + 1)

theorem rationalProductJet_mem2747
    (X Y : ℕ → RationalBox2744) (n : ℕ)
    (a b : ℕ → ℝ)
    (hX : ∀ j ≤ n, (X j).Mem (a j))
    (hY : ∀ j ≤ n, (Y j).Mem (b j)) :
    (rationalProductJet2747 X Y n).Mem
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a j * b (n - j)) := by
  apply RationalBox2744.mem_sum
  intro j hj
  have hm := RationalBox2744.mem_mul (hX j (by omega))
    (hY (n - j) (by omega))
  have hs := RationalBox2744.mem_nsmul (c := (n.choose j : ℚ))
    (by positivity) hm
  simpa [mul_assoc] using hs

end
end ConnesWeilRH.Dev
