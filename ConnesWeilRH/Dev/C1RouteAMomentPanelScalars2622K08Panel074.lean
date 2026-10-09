import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P074 : ℚ := ((-817632513238177981956835994627420950707 : ℚ) / 26393499617231918722682558098492620800)

def momentPanelGrowth2622K08P074 : ℚ := ((14618277955565802058597570543439473363 : ℚ) / 125372672603532252975066341736815001600)

theorem momentPanelPhase_owner2622K08P074 :
    (momentPanelPhase2622K08P074 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P074 :
    (momentPanelGrowth2622K08P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P074Input : RatPair2542 := (momentPanelPhase2622K08P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P074Expected : RatState2542 :=
  ((((75124667712012691751173608063790388593850391626319219018579450166443686859908969605 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((23808660909550074155670643677282181 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K08P074_replay :
    compactExp2620 momentScalarAmp2622K08P074Input 20 = momentScalarAmp2622K08P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K08P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P074_replay] at h
  simpa only [momentPanelPhase_owner2622K08P074] using h

theorem momentScalarAmp2622K08P074_radius_le :
    (momentScalarAmp2622K08P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P074Expected]

def momentScalarGrow2622K08P074Input : RatPair2542 := (momentPanelGrowth2622K08P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P074Expected : RatState2542 :=
  ((((2400140915859068515039150650403368992376486071797012917637638926158517956401447082447340852328083 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3042539734299500004856603440852375792044374943573 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K08P074_replay :
    compactExp2620 momentScalarGrow2622K08P074Input 20 = momentScalarGrow2622K08P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P074] using h

theorem momentScalarGrow2622K08P074_radius_le :
    (momentScalarGrow2622K08P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P074Expected]

end ConnesWeilRH.Dev
