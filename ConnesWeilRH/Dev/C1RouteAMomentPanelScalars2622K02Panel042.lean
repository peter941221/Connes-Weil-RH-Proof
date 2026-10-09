import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P042 : ℚ := ((-959227557249664210800164324534550810696085630007113 : ℚ) / 23578131883502457235082884215305659653042974228480)

def momentPanelGrowth2622K02P042 : ℚ := ((17406580722407789414850806257217134773196168001191119 : ℚ) / 33020945343214358404152610017780464424864864167526400)

theorem momentPanelPhase_owner2622K02P042 :
    (momentPanelPhase2622K02P042 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P042 :
    (momentPanelGrowth2622K02P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P042Input : RatPair2542 := (momentPanelPhase2622K02P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P042Expected : RatState2542 :=
  ((((4583796701276235073598437224496152670210437234293481297569849208630810287832167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5810880505181751439247085469785 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P042_replay :
    compactExp2620 momentScalarAmp2622K02P042Input 20 = momentScalarAmp2622K02P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K02P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P042_replay] at h
  simpa only [momentPanelPhase_owner2622K02P042] using h

theorem momentScalarAmp2622K02P042_radius_le :
    (momentScalarAmp2622K02P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P042Expected]

def momentScalarGrow2622K02P042Input : RatPair2542 := (momentPanelGrowth2622K02P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P042Expected : RatState2542 :=
  ((((1809262377909975201653625561466095677463788064407106540022445977548647360610343391399630938976193 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((573377846584800727851681843886991227196414350535 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P042_replay :
    compactExp2620 momentScalarGrow2622K02P042Input 20 = momentScalarGrow2622K02P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P042] using h

theorem momentScalarGrow2622K02P042_radius_le :
    (momentScalarGrow2622K02P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P042Expected]

end ConnesWeilRH.Dev
