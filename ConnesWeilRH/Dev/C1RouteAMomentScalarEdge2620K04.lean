import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarEdge2620K04Input : RatPair2542 :=
  (momentEdgeArgument2620K04 / (2 : ℚ) ^ 20, 0)

def momentScalarEdge2620K04Expected : RatState2542 :=
  ((((9256431484834097195894081033603 : ℚ) /
    266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072),
    0),
   ((2417851639229258349412353 : ℚ) /
    2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarEdge2620K04_replay :
    compactExp2620 momentScalarEdge2620K04Input 20 = momentScalarEdge2620K04Expected := by
  decide +kernel

theorem momentScalarEdge2620K04_error :
    |Real.exp (-30 / (1 - (9 / 10 : ℝ) ^ 2) +
        |((capturedNodes2584 4).re * (storedWidth 4 ^ 2))|) -
      (momentScalarEdge2620K04Expected.1.1 : ℝ)| ≤
      (momentScalarEdge2620K04Expected.2 : ℝ) := by
  have hsmall :
      |((momentEdgeArgument2620K04 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤
        (1 : ℝ) / 1000 := by
    norm_num [momentEdgeArgument2620K04]
  have h := compactExp_real_error2620 momentEdgeArgument2620K04 20 hsmall
  change |Real.exp (momentEdgeArgument2620K04 : ℝ) -
      ((compactExp2620 momentScalarEdge2620K04Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarEdge2620K04Input 20).2 : ℝ) at h
  rw [momentScalarEdge2620K04_replay] at h
  simpa only [momentEdgeArgument_owner2620K04] using h

theorem momentScalarEdge2620K04_radius_le :
    (momentScalarEdge2620K04Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarEdge2620K04Expected]

end ConnesWeilRH.Dev
