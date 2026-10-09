import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P105 : ℚ := ((-72965998858236469292028210486276588432128430117489725 : ℚ) / 2377315100823379959323068841017123866847831272718336)

def momentPanelGrowth2622K03P105 : ℚ := ((1175227764425913122588627875526329736400632874517475 : ℚ) / 11292566432394220941797934050888495054437748280655872)

theorem momentPanelPhase_owner2622K03P105 :
    (momentPanelPhase2622K03P105 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P105 :
    (momentPanelGrowth2622K03P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P105Input : RatPair2542 := (momentPanelPhase2622K03P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P105Expected : RatState2542 :=
  ((((24998193658332842093590950487663774647598929506039643966805033580307413128948124577 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((63379805539797777974003660335964069 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P105_replay :
    compactExp2620 momentScalarAmp2622K03P105Input 20 = momentScalarAmp2622K03P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K03P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P105_replay] at h
  simpa only [momentPanelPhase_owner2622K03P105] using h

theorem momentScalarAmp2622K03P105_radius_le :
    (momentScalarAmp2622K03P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P105Expected]

def momentScalarGrow2622K03P105Input : RatPair2542 := (momentPanelGrowth2622K03P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P105Expected : RatState2542 :=
  ((((296282534605871455328929887600645772095242347544651278137864525099671600854310051792990208539417 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3004661564430231808051912625893687117068560372055 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P105_replay :
    compactExp2620 momentScalarGrow2622K03P105Input 20 = momentScalarGrow2622K03P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P105] using h

theorem momentScalarGrow2622K03P105_radius_le :
    (momentScalarGrow2622K03P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P105Expected]

end ConnesWeilRH.Dev
