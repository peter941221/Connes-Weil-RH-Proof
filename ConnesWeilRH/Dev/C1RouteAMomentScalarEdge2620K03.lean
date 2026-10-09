import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarEdge2620K03Input : RatPair2542 := (momentEdgeArgument2620K03 / (2 : ℚ) ^ 20, 0)

def momentScalarEdge2620K03Expected : RatState2542 :=
  ((((3839907376778220683205157741 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarEdge2620K03_replay :
    compactExp2620 momentScalarEdge2620K03Input 20 = momentScalarEdge2620K03Expected := by
  decide +kernel

theorem momentScalarEdge2620K03_error :
    |Real.exp (-30 / (1 - (9 / 10 : ℝ) ^ 2) + |((capturedNodes2584 3).re * (storedWidth 3 ^ 2))|) - (momentScalarEdge2620K03Expected.1.1 : ℝ)| ≤
      (momentScalarEdge2620K03Expected.2 : ℝ) := by
  have hsmall : |((momentEdgeArgument2620K03 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentEdgeArgument2620K03]
  have h := compactExp_real_error2620 momentEdgeArgument2620K03 20 hsmall
  change |Real.exp (momentEdgeArgument2620K03 : ℝ) -
    ((compactExp2620 momentScalarEdge2620K03Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarEdge2620K03Input 20).2 : ℝ) at h
  rw [momentScalarEdge2620K03_replay] at h
  simpa only [momentEdgeArgument_owner2620K03] using h

theorem momentScalarEdge2620K03_radius_le :
    (momentScalarEdge2620K03Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarEdge2620K03Expected]

end ConnesWeilRH.Dev
