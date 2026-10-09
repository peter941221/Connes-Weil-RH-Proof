import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P093 : ℚ := ((-32146559296162903300895709219270794575 : ℚ) / 1080403394767317180142822181503500288)

def momentPanelGrowth2622K07P093 : ℚ := ((2155621926179219042150358333180025 : ℚ) / 20566363338102793809882512804020224)

theorem momentPanelPhase_owner2622K07P093 :
    (momentPanelPhase2622K07P093 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P093, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P093 :
    (momentPanelGrowth2622K07P093 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P093, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P093Input : RatPair2542 := (momentPanelPhase2622K07P093 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P093Expected : RatState2542 :=
  ((((63891850087283255179429805650722204708468831819134047711839685534131308464835606205 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((323979361508088649584970699139412115 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P093_replay :
    compactExp2620 momentScalarAmp2622K07P093Input 20 = momentScalarAmp2622K07P093Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P093_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 200) 0) -
      (momentScalarAmp2622K07P093Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P093]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P093 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P093 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P093Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P093_replay] at h
  simpa only [momentPanelPhase_owner2622K07P093] using h

theorem momentScalarAmp2622K07P093_radius_le :
    (momentScalarAmp2622K07P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P093Expected]

def momentScalarGrow2622K07P093Input : RatPair2542 := (momentPanelGrowth2622K07P093 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P093Expected : RatState2542 :=
  ((((74125619341619210198121072289001663879631566026587989909647335881318042017524522221878611713817 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((751723011665222483034276397318855827227703013279 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P093_replay :
    compactExp2620 momentScalarGrow2622K07P093Input 20 = momentScalarGrow2622K07P093Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P093_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P093Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P093Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P093]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P093 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P093 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P093Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P093Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P093_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P093] using h

theorem momentScalarGrow2622K07P093_radius_le :
    (momentScalarGrow2622K07P093Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P093Expected]

end ConnesWeilRH.Dev
