import ConnesWeilRH.Dev.Wall14PlateauNear
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Wall14PlateauExplicit

Decisive unblock for the Wall-A 1.4 `hI` near band (docs/971): an explicit flat-top
compact smooth bump built from `Real.smoothTransition` (0 for `x<=0`, 1 for `x>=1`,
`0<s<1` between, monotone, smooth) instead of the opaque mathlib `ContDiffBump`.
We write the bump in `x^2` so that it is genuinely smooth at 0.
RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open Set
open scoped Topology

noncomputable def bplateau : ℝ := 9 / 10

noncomputable def bSq : ℝ := (bplateau : ℝ) ^ 2

lemma bSq_pos : (0 : ℝ) < bSq := by
  unfold bSq bplateau
  positivity

lemma bSq_lt_one : bSq < (1 : ℝ) := by
  unfold bSq bplateau
  norm_num

lemma one_sub_bSq_pos : (0 : ℝ) < 1 - bSq := by
  exact sub_pos.mpr bSq_lt_one

noncomputable def bumpEx (x : ℝ) : ℝ :=
  1 - Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq))

lemma bump_eq_one_of_sq_le (x : ℝ) (hx : x ^ 2 <= bSq) : bumpEx x = 1 := by
  unfold bumpEx
  have hden : 0 < 1 - bSq := one_sub_bSq_pos
  have harg : (x ^ 2 - bSq) / (1 - bSq) <= 0 := by
    rw [div_le_iff₀ hden]
    linarith
  have hst : Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq)) = 0 :=
    Real.smoothTransition.zero_of_nonpos harg
  simp [hst]

lemma bumpEx_eq_zero_of_one_le_sq (x : ℝ) (hx : (1 : ℝ) <= x ^ 2) : bumpEx x = 0 := by
  unfold bumpEx
  have hden : 0 < 1 - bSq := one_sub_bSq_pos
  have hone : (1 : ℝ) <= (x ^ 2 - bSq) / (1 - bSq) := by
    rw [le_div_iff₀ hden]
    nlinarith [hx, hden, bSq_lt_one]
  have hst : Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq)) = 1 :=
    Real.smoothTransition.one_of_one_le hone
  simp [hst]

lemma bumpEx_nonneg (x : ℝ) : (0 : ℝ) <= bumpEx x := by
  unfold bumpEx
  exact sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma bumpEx_le_one (x : ℝ) : bumpEx x <= 1 := by
  unfold bumpEx
  have hst : 0 <= Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq)) :=
    Real.smoothTransition.nonneg _
  linarith

theorem bumpEx_even (x : ℝ) : bumpEx (-x) = bumpEx x := by
  rw [bumpEx, bumpEx]
  congr 1
  rw [neg_sq]

end Wall14Plateau
end Dev
end Source
end ConnesWeilRH