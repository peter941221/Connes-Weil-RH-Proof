import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P076 : ℚ := ((-219511962773580180495810664189957009634970919940530725 : ℚ) / 7174328849952736062597113383200143808113515861901312)

def momentPanelGrowth2622K03P076 : ℚ := ((16526655318334937720326515814656764468716481612544475 : ℚ) / 182913049950068823369161134744679819345084766970970112)

theorem momentPanelPhase_owner2622K03P076 :
    (momentPanelPhase2622K03P076 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P076 :
    (momentPanelGrowth2622K03P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P076Input : RatPair2542 := (momentPanelPhase2622K03P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P076Expected : RatState2542 :=
  ((((110039724608042580546981245536312546276989244408525461053195951982300067082946936457 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((139495993306777090124323969250124615 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P076_replay :
    compactExp2620 momentScalarAmp2622K03P076Input 20 = momentScalarAmp2622K03P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K03P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P076_replay] at h
  simpa only [momentPanelPhase_owner2622K03P076] using h

theorem momentScalarAmp2622K03P076_radius_le :
    (momentScalarAmp2622K03P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P076Expected]

def momentScalarGrow2622K03P076Input : RatPair2542 := (momentPanelGrowth2622K03P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P076Expected : RatState2542 :=
  ((((18265360340745113991648841280224853793412171918265653096233730017975811472428770837491205875313 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((740930976134861303848984861925817094791612434459 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P076_replay :
    compactExp2620 momentScalarGrow2622K03P076Input 20 = momentScalarGrow2622K03P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P076] using h

theorem momentScalarGrow2622K03P076_radius_le :
    (momentScalarGrow2622K03P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P076Expected]

end ConnesWeilRH.Dev
