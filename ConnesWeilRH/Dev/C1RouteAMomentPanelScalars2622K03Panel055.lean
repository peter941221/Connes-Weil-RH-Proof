import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P055 : ℚ := ((-219882737866563230580275771924495468181015233929791675 : ℚ) / 6437732024737960991822456227511137166206925860241408)

def momentPanelGrowth2622K03P055 : ℚ := ((1034155951753336449199184145925121490303925247032675 : ℚ) / 3751217983766761883866920314072474673013136358899712)

theorem momentPanelPhase_owner2622K03P055 :
    (momentPanelPhase2622K03P055 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P055 :
    (momentPanelGrowth2622K03P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P055Input : RatPair2542 := (momentPanelPhase2622K03P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P055Expected : RatState2542 :=
  ((((3134264354881737344219945894694463383218431540254616409362664970303159137862714045 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1986640756458934914575848002498299 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P055_replay :
    compactExp2620 momentScalarAmp2622K03P055Input 20 = momentScalarAmp2622K03P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K03P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P055_replay] at h
  simpa only [momentPanelPhase_owner2622K03P055] using h

theorem momentScalarAmp2622K03P055_radius_le :
    (momentScalarAmp2622K03P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P055Expected]

def momentScalarGrow2622K03P055Input : RatPair2542 := (momentPanelGrowth2622K03P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P055Expected : RatState2542 :=
  ((((2814020463796904012928293791630454171964068773229670643343023972914551359561422450303527463562423 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3567193792121120647429691134273922197960575637287 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P055_replay :
    compactExp2620 momentScalarGrow2622K03P055Input 20 = momentScalarGrow2622K03P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P055] using h

theorem momentScalarGrow2622K03P055_radius_le :
    (momentScalarGrow2622K03P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P055Expected]

end ConnesWeilRH.Dev
