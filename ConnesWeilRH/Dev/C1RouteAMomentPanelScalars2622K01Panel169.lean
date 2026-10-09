import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P169 : ℚ := ((-85479367745778705445272904418717194771879565595656367 : ℚ) / 1050382939446951174464845559216355945620882377932800)

def momentPanelGrowth2622K01P169 : ℚ := ((3569913145098852592139102732904096331138043099371 : ℚ) / 963392192576522919714343029378409217058353971200)

theorem momentPanelPhase_owner2622K01P169 :
    (momentPanelPhase2622K01P169 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (159 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P169, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P169 :
    (momentPanelGrowth2622K01P169 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P169, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P169Input : RatPair2542 := (momentPanelPhase2622K01P169 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P169Expected : RatState2542 :=
  ((((4853027372146745310578137684704682455908057394937764536375275 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639241563200775939 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P169_replay :
    compactExp2620 momentScalarAmp2622K01P169Input 20 = momentScalarAmp2622K01P169Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P169_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (159 / 200) 0) -
      (momentScalarAmp2622K01P169Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P169]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P169 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P169 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P169Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P169_replay] at h
  simpa only [momentPanelPhase_owner2622K01P169] using h

theorem momentScalarAmp2622K01P169_radius_le :
    (momentScalarAmp2622K01P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P169Expected]

def momentScalarGrow2622K01P169Input : RatPair2542 := (momentPanelGrowth2622K01P169 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P169Expected : RatState2542 :=
  ((((21719278457777149872112664859032567013279115129984512554635080506596042491738891677838839487339429 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((110129436306677288198921131808514976381816467587021 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P169_replay :
    compactExp2620 momentScalarGrow2622K01P169Input 20 = momentScalarGrow2622K01P169Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P169_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P169Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P169]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P169 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P169 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P169Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P169_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P169] using h

theorem momentScalarGrow2622K01P169_radius_le :
    (momentScalarGrow2622K01P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P169Expected]

end ConnesWeilRH.Dev
