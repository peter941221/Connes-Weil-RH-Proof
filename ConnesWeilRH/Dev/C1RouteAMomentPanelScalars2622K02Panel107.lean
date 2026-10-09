import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P107 : ℚ := ((-892320833291200236866491874851857245533349393539699 : ℚ) / 29515482285159250340285353848215559420395200184320)

def momentPanelGrowth2622K02P107 : ℚ := ((130484411700798411784385139614773770202017676432706919 : ℚ) / 835162693597817930756530490567785720974696121788006400)

theorem momentPanelPhase_owner2622K02P107 :
    (momentPanelPhase2622K02P107 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P107 :
    (momentPanelGrowth2622K02P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P107Input : RatPair2542 := (momentPanelPhase2622K02P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P107Expected : RatState2542 :=
  ((((158445077336210714156937301271330447062360014820631632484106015603168477149082717231 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((200858788420855168102407813326040837 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P107_replay :
    compactExp2620 momentScalarAmp2622K02P107Input 20 = momentScalarAmp2622K02P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K02P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P107_replay] at h
  simpa only [momentPanelPhase_owner2622K02P107] using h

theorem momentScalarAmp2622K02P107_radius_le :
    (momentScalarAmp2622K02P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P107Expected]

def momentScalarGrow2622K02P107Input : RatPair2542 := (momentPanelGrowth2622K02P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P107Expected : RatState2542 :=
  ((((312149082964611346680612178673524287173810612344571023238286299437444535981243911034823583406885 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3165567307375202513517698320334988205896758204387 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P107_replay :
    compactExp2620 momentScalarGrow2622K02P107Input 20 = momentScalarGrow2622K02P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P107] using h

theorem momentScalarGrow2622K02P107_radius_le :
    (momentScalarGrow2622K02P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P107Expected]

end ConnesWeilRH.Dev
