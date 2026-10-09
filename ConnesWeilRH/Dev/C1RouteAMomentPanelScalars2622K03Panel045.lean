import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P045 : ℚ := ((-73332422020431399700901904261769979064224523684438725 : ℚ) / 1953479625997418113044000239529401791147610835255296)

def momentPanelGrowth2622K03P045 : ℚ := ((3973571310872339725046424497966445574177321979051625 : ℚ) / 9295241757276875741207823266377604772700459469111296)

theorem momentPanelPhase_owner2622K03P045 :
    (momentPanelPhase2622K03P045 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P045 :
    (momentPanelGrowth2622K03P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P045Input : RatPair2542 := (momentPanelPhase2622K03P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P045Expected : RatState2542 :=
  ((((106279925642079973022609956088859057023417637160507988974031102797957957046227843 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((134730637267315499040917759511631 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P045_replay :
    compactExp2620 momentScalarAmp2622K03P045Input 20 = momentScalarAmp2622K03P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K03P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P045_replay] at h
  simpa only [momentPanelPhase_owner2622K03P045] using h

theorem momentScalarAmp2622K03P045_radius_le :
    (momentScalarAmp2622K03P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P045Expected]

def momentScalarGrow2622K03P045Input : RatPair2542 := (momentPanelGrowth2622K03P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P045Expected : RatState2542 :=
  ((((409414069640685068519614902487010258243531957426208781089723567498829939917646227244735013845985 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2075975118151924653664571283855639670427728681197 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P045_replay :
    compactExp2620 momentScalarGrow2622K03P045Input 20 = momentScalarGrow2622K03P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P045] using h

theorem momentScalarGrow2622K03P045_radius_le :
    (momentScalarGrow2622K03P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P045Expected]

end ConnesWeilRH.Dev
