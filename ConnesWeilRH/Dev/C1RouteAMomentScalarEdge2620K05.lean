import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarEdge2620K05Input : RatPair2542 := (momentEdgeArgument2620K05 / (2 : ℚ) ^ 20, 0)

def momentScalarEdge2620K05Expected : RatState2542 :=
  ((((23424053604927332236880751893 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarEdge2620K05_replay :
    compactExp2620 momentScalarEdge2620K05Input 20 = momentScalarEdge2620K05Expected := by
  decide +kernel

theorem momentScalarEdge2620K05_error :
    |Real.exp (-30 / (1 - (9 / 10 : ℝ) ^ 2) + |((capturedNodes2584 5).re * (storedWidth 5 ^ 2))|) - (momentScalarEdge2620K05Expected.1.1 : ℝ)| ≤
      (momentScalarEdge2620K05Expected.2 : ℝ) := by
  have hsmall : |((momentEdgeArgument2620K05 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentEdgeArgument2620K05]
  have h := compactExp_real_error2620 momentEdgeArgument2620K05 20 hsmall
  change |Real.exp (momentEdgeArgument2620K05 : ℝ) -
    ((compactExp2620 momentScalarEdge2620K05Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarEdge2620K05Input 20).2 : ℝ) at h
  rw [momentScalarEdge2620K05_replay] at h
  simpa only [momentEdgeArgument_owner2620K05] using h

theorem momentScalarEdge2620K05_radius_le :
    (momentScalarEdge2620K05Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarEdge2620K05Expected]

end ConnesWeilRH.Dev
