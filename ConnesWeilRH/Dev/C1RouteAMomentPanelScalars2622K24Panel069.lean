import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P069 : ℚ := ((-819521871940245274559328310019071187717 : ℚ) / 25906721786744278632507824067628236800)

def momentPanelGrowth2622K24P069 : ℚ := ((14213109428006367386023293585777012748489 : ℚ) / 92664732548154354488561502881814727884800)

theorem momentPanelPhase_owner2622K24P069 :
    (momentPanelPhase2622K24P069 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-41 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P069, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P069 :
    (momentPanelGrowth2622K24P069 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P069, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P069Input : RatPair2542 := (momentPanelPhase2622K24P069 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P069Expected : RatState2542 :=
  ((((4877839500861904264626457867678365349698746009906497152850601072531165730025774749 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((12367165431214261055525185985668279 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K24P069_replay :
    compactExp2620 momentScalarAmp2622K24P069Input 20 = momentScalarAmp2622K24P069Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P069_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-41 / 200) 0) -
      (momentScalarAmp2622K24P069Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P069]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P069 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P069 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P069Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P069_replay] at h
  simpa only [momentPanelPhase_owner2622K24P069] using h

theorem momentScalarAmp2622K24P069_radius_le :
    (momentScalarAmp2622K24P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P069Expected]

def momentScalarGrow2622K24P069Input : RatPair2542 := (momentPanelGrowth2622K24P069 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P069Expected : RatState2542 :=
  ((((2490070272164054361941704982727624362214744831991655878025472574535998609243839869507333387003347 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3156538613391620882402703960499552724493190246867 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K24P069_replay :
    compactExp2620 momentScalarGrow2622K24P069Input 20 = momentScalarGrow2622K24P069Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P069_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P069Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P069]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P069 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P069 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P069Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P069_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P069] using h

theorem momentScalarGrow2622K24P069_radius_le :
    (momentScalarGrow2622K24P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P069Expected]

end ConnesWeilRH.Dev
