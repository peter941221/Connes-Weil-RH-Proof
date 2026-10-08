import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P015 : ℚ := ((-126128160141478202382641623081130206968018023140902959 : ℚ) / 1693572112164891994863762131348770928831767144038400)

def momentPanelGrowth2622K04P015 : ℚ := ((17104175809932431434825021065003332318743049856303 : ℚ) / 6993513694259203417185601250302526168275458457600)

theorem momentPanelPhase_owner2622K04P015 :
    (momentPanelPhase2622K04P015 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-149 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P015, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P015 :
    (momentPanelGrowth2622K04P015 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P015, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P015Input : RatPair2542 := (momentPanelPhase2622K04P015 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P015Expected : RatState2542 :=
  ((((9675575594433997912854670473452597363700767282670430574781408809 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851651495379049379221 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P015_replay :
    compactExp2620 momentScalarAmp2622K04P015Input 20 = momentScalarAmp2622K04P015Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P015_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-149 / 200) 0) -
      (momentScalarAmp2622K04P015Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P015]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P015 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P015 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P015Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P015_replay] at h
  simpa only [momentPanelPhase_owner2622K04P015] using h

theorem momentScalarAmp2622K04P015_radius_le :
    (momentScalarAmp2622K04P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P015Expected]

def momentScalarGrow2622K04P015Input : RatPair2542 := (momentPanelGrowth2622K04P015 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P015Expected : RatState2542 :=
  ((((770213813444428674298236839504576605759858077400095247362814320896216095769915321888513837526813 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((7810877805064180012731658064216619219982222229555 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P015_replay :
    compactExp2620 momentScalarGrow2622K04P015Input 20 = momentScalarGrow2622K04P015Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P015_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P015Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P015]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P015 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P015 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P015Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P015_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P015] using h

theorem momentScalarGrow2622K04P015_radius_le :
    (momentScalarGrow2622K04P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P015Expected]

end ConnesWeilRH.Dev
