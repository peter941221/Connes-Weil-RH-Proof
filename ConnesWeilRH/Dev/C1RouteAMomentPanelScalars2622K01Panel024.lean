import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P024 : ℚ := ((-28611215896700353863774020957831730999253373452011719 : ℚ) / 543281834228523628724836554270950323664092502425600)

def momentPanelGrowth2622K01P024 : ℚ := ((88443230235394112851706079568586052512941639098557433 : ℚ) / 71038435090246058808911094014558957660556857285017600)

theorem momentPanelPhase_owner2622K01P024 :
    (momentPanelPhase2622K01P024 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P024 :
    (momentPanelGrowth2622K01P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P024Input : RatPair2542 := (momentPanelPhase2622K01P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P024Expected : RatState2542 :=
  ((((897236282443824253579681684377898124835647414943855222705704274047596047 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((2425994202032003943939125 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K01P024_replay :
    compactExp2620 momentScalarAmp2622K01P024Input 20 = momentScalarAmp2622K01P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K01P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P024_replay] at h
  simpa only [momentPanelPhase_owner2622K01P024] using h

theorem momentScalarAmp2622K01P024_radius_le :
    (momentScalarAmp2622K01P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P024Expected]

def momentScalarGrow2622K01P024Input : RatPair2542 := (momentPanelGrowth2622K01P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P024Expected : RatState2542 :=
  ((((927272904715884704847539438261947808605523858668543209391729073138858541115150766435906185623599 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((9403653268665162910496354977049526177309287579605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P024_replay :
    compactExp2620 momentScalarGrow2622K01P024Input 20 = momentScalarGrow2622K01P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P024] using h

theorem momentScalarGrow2622K01P024_radius_le :
    (momentScalarGrow2622K01P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P024Expected]

end ConnesWeilRH.Dev
