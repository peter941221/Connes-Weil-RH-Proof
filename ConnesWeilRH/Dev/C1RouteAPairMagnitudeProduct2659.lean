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

#print axioms pairMagnitude_mul_le2659
#print axioms pairMagnitude_add_le2659
#print axioms pairMagnitude_sub_le2659

end ConnesWeilRH.Dev
