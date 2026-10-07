import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarEdge2620Input : RatPair2542 := (momentEdgeArgument2620 / (2 : ℚ) ^ 20, 0)

def momentScalarEdge2620Expected : RatState2542 :=
  ((((32092303841647457648738843093 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarEdge2620_replay :
    compactExp2620 momentScalarEdge2620Input 20 = momentScalarEdge2620Expected := by
  decide +kernel

theorem momentScalarEdge2620_error :
    |Real.exp (-30 / (1 - (9 / 10 : ℝ) ^ 2) + |((capturedNodes2584 0).re * (storedWidth 0 ^ 2))|) - (momentScalarEdge2620Expected.1.1 : ℝ)| ≤
      (momentScalarEdge2620Expected.2 : ℝ) := by
  have hsmall : |((momentEdgeArgument2620 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentEdgeArgument2620]
  have h := compactExp_real_error2620 momentEdgeArgument2620 20 hsmall
  change |Real.exp (momentEdgeArgument2620 : ℝ) -
    ((compactExp2620 momentScalarEdge2620Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarEdge2620Input 20).2 : ℝ) at h
  rw [momentScalarEdge2620_replay] at h
  simpa only [momentEdgeArgument_owner2620] using h

theorem momentScalarEdge2620_radius_le :
    (momentScalarEdge2620Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarEdge2620Expected]

end ConnesWeilRH.Dev
