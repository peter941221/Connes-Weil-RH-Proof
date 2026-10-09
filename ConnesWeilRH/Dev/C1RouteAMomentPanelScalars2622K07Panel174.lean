import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P174 : ℚ := ((-30341428613641572607501211371635388225 : ℚ) / 309347311274895277306043476614316032)

def momentPanelGrowth2622K07P174 : ℚ := ((1116813676825790969466097808024720425 : ℚ) / 166599712484394820862302722063335424)

theorem momentPanelPhase_owner2622K07P174 :
    (momentPanelPhase2622K07P174 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P174 :
    (momentPanelGrowth2622K07P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P174Input : RatPair2542 := (momentPanelPhase2622K07P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P174Expected : RatState2542 :=
  ((((67608495322634889486427866470770655639509785068719887 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1208925819614629175050241 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P174_replay :
    compactExp2620 momentScalarAmp2622K07P174Input 20 = momentScalarAmp2622K07P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K07P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P174_replay] at h
  simpa only [momentPanelPhase_owner2622K07P174] using h

theorem momentScalarAmp2622K07P174_radius_le :
    (momentScalarAmp2622K07P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P174Expected]

def momentScalarGrow2622K07P174Input : RatPair2542 := (momentPanelGrowth2622K07P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P174Expected : RatState2542 :=
  ((((1741503164690713365821649396028247992881623559847594075800848472930231542623128336967953261778464017 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2207603418705378434158218614601517023580179158146215 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P174_replay :
    compactExp2620 momentScalarGrow2622K07P174Input 20 = momentScalarGrow2622K07P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P174] using h

theorem momentScalarGrow2622K07P174_radius_le :
    (momentScalarGrow2622K07P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P174Expected]

end ConnesWeilRH.Dev
