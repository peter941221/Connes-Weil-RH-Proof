import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K12
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K12P124 : ℚ := ((-2395698457618611928491704550830698564821 : ℚ) / 71473183202308121406947718806791782400)

def momentPanelGrowth2622K12P124 : ℚ := ((12003176344690521149494191006883568723 : ℚ) / 41646885759658157465012088428140953600)

theorem momentPanelPhase_owner2622K12P124 :
    (momentPanelPhase2622K12P124 : ℝ) = momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (69 / 200) 0 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P124, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K12P124 :
    (momentPanelGrowth2622K12P124 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2))
      (69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P124, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K12P124Input : RatPair2542 := (momentPanelPhase2622K12P124 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K12P124Expected : RatState2542 :=
  ((((2961554651178331010171901442435252857939593384951702457315848725052991374189956187 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3754336541814213291953355107804839 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K12P124_replay :
    compactExp2620 momentScalarAmp2622K12P124Input 20 = momentScalarAmp2622K12P124Expected := by
  decide +kernel

theorem momentScalarAmp2622K12P124_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (69 / 200) 0) -
      (momentScalarAmp2622K12P124Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K12P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K12P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelPhase2622K12P124]
  have h := compactExp_real_error2620 momentPanelPhase2622K12P124 20 hsmall
  change |Real.exp (momentPanelPhase2622K12P124 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K12P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K12P124Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K12P124_replay] at h
  simpa only [momentPanelPhase_owner2622K12P124] using h

theorem momentScalarAmp2622K12P124_radius_le :
    (momentScalarAmp2622K12P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarAmp2622K12P124Expected]

def momentScalarGrow2622K12P124Input : RatPair2542 := (momentPanelGrowth2622K12P124 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K12P124Expected : RatState2542 :=
  ((((356186919596874484232923664590982418434610345202471499328981580112187316859999911547338459309985 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3612163506518950043083313794100245256017175045515 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K12P124_replay :
    compactExp2620 momentScalarGrow2622K12P124Input 20 = momentScalarGrow2622K12P124Expected := by
  decide +kernel

theorem momentScalarGrow2622K12P124_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 12).re * (storedWidth 12 ^ 2)) (69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K12P124Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K12P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K12P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentPanelGrowth2622K12P124]
  have h := compactExp_real_error2620 momentPanelGrowth2622K12P124 20 hsmall
  change |Real.exp (momentPanelGrowth2622K12P124 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K12P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K12P124Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K12P124_replay] at h
  simpa only [momentPanelGrowth_owner2622K12P124] using h

theorem momentScalarGrow2622K12P124_radius_le :
    (momentScalarGrow2622K12P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, momentScalarGrow2622K12P124Expected]

end ConnesWeilRH.Dev
