import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620

namespace ConnesWeilRH.Dev

/-!
# L1 pair-magnitude product law (record 2659)

`pairMagnitude` is `|re| + |im|`.  It is a convenient rational enclosure
scale because it avoids introducing a second floating-point norm.  This
lemma is the algebraic step used by the P095 certified-ball assembly.
-/

theorem pairMagnitude_mul_le2659 (a b : RatPair2542) :
    pairMagnitude2542 (pairMul2542 a b) ≤
      pairMagnitude2542 a * pairMagnitude2542 b := by
  unfold pairMagnitude2542 pairMul2542
  have hs : |a.1 * b.1 - a.2 * b.2| ≤
      |a.1 * b.1| + |a.2 * b.2| := abs_sub _ _
  have ha : |a.1 * b.2 + a.2 * b.1| ≤
      |a.1 * b.2| + |a.2 * b.1| := abs_add_le _ _
  have h1 : |a.1 * b.1| ≤ |a.1| * |b.1| := by rw [abs_mul]
  have h2 : |a.2 * b.2| ≤ |a.2| * |b.2| := by rw [abs_mul]
  have h3 : |a.1 * b.2| ≤ |a.1| * |b.2| := by rw [abs_mul]
  have h4 : |a.2 * b.1| ≤ |a.2| * |b.1| := by rw [abs_mul]
  nlinarith [hs, ha, h1, h2, h3, h4, abs_nonneg a.1, abs_nonneg a.2,
    abs_nonneg b.1, abs_nonneg b.2]

theorem pairMagnitude_add_le2659 (a b : RatPair2542) :
    pairMagnitude2542 (pairAdd2542 a b) ≤
      pairMagnitude2542 a + pairMagnitude2542 b := by
  unfold pairMagnitude2542 pairAdd2542
  change |a.1 + b.1| + |a.2 + b.2| ≤
    (|a.1| + |a.2|) + (|b.1| + |b.2|)
  have h1 := abs_add_le a.1 b.1
  have h2 := abs_add_le a.2 b.2
  linarith

theorem pairMagnitude_sub_le2659 (a b : RatPair2542) :
    pairMagnitude2542 (pairAdd2542 a (-b.1, -b.2)) ≤
      pairMagnitude2542 a + pairMagnitude2542 b := by
  simpa [pairMagnitude2542, pairAdd2542] using
    pairMagnitude_add_le2659 a (-b.1, -b.2)

theorem pairMagnitude_scale_eq2659 (q : ℚ) (a : RatPair2542) :
    pairMagnitude2542 (pairScale2542 q a) =
      |q| * pairMagnitude2542 a := by
  simp [pairMagnitude2542, pairScale2542, abs_mul, mul_add]

theorem pairMagnitude_add_mul_le2659 (a da b : RatPair2542) :
    pairMagnitude2542 (pairMul2542 (pairAdd2542 a da) b) ≤
      (pairMagnitude2542 a + pairMagnitude2542 da) * pairMagnitude2542 b := by
  have hmul := pairMagnitude_mul_le2659 (pairAdd2542 a da) b
  have hadd := pairMagnitude_add_le2659 a da
  have hb : 0 ≤ pairMagnitude2542 b := by
    unfold pairMagnitude2542
    positivity
  exact le_trans hmul (mul_le_mul_of_nonneg_right hadd hb)

theorem pairMagnitude_add_mul_le_of_radius2659
    (a da b : RatPair2542) (r : ℚ)
    (hda : pairMagnitude2542 da ≤ r) :
    pairMagnitude2542 (pairMul2542 (pairAdd2542 a da) b) ≤
      (pairMagnitude2542 a + r) * pairMagnitude2542 b := by
  have hmain := pairMagnitude_add_mul_le2659 a da b
  have hright : 0 ≤ pairMagnitude2542 b := by
    unfold pairMagnitude2542
    positivity
  have hsum : pairMagnitude2542 a + pairMagnitude2542 da ≤
      pairMagnitude2542 a + r := by linarith
  exact le_trans hmain (mul_le_mul_of_nonneg_right hsum hright)

#print axioms pairMagnitude_mul_le2659
#print axioms pairMagnitude_add_le2659
#print axioms pairMagnitude_sub_le2659
#print axioms pairMagnitude_scale_eq2659
#print axioms pairMagnitude_add_mul_le2659
#print axioms pairMagnitude_add_mul_le_of_radius2659

end ConnesWeilRH.Dev
