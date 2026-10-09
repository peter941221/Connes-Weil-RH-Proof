import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P046 : ℚ := ((-359003524474498767325428979411500919425210384857165463 : ℚ) / 9257413984429396980520254455043315353605771152588800)

def momentPanelGrowth2622K02P046 : ℚ := ((84378818230541014041375852679462615580200322669317 : ℚ) / 188824869744998492264011233758168206543437378355200)

theorem momentPanelPhase_owner2622K02P046 :
    (momentPanelPhase2622K02P046 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P046 :
    (momentPanelGrowth2622K02P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P046Input : RatPair2542 := (momentPanelPhase2622K02P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P046Expected : RatState2542 :=
  ((((7683360723750538921860270307412918922242051333761749510766394694642923727956065 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((19480355315576570813495456454617 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P046_replay :
    compactExp2620 momentScalarAmp2622K02P046Input 20 = momentScalarAmp2622K02P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K02P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P046_replay] at h
  simpa only [momentPanelPhase_owner2622K02P046] using h

theorem momentScalarAmp2622K02P046_radius_le :
    (momentScalarAmp2622K02P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P046Expected]

def momentScalarGrow2622K02P046Input : RatPair2542 := (momentPanelGrowth2622K02P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P046Expected : RatState2542 :=
  ((((3339401820604786436290545280860009153553144008201245621015135600476612830208114529383573689732799 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1058298229567044171500595450291565126864475208537 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P046_replay :
    compactExp2620 momentScalarGrow2622K02P046Input 20 = momentScalarGrow2622K02P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P046] using h

theorem momentScalarGrow2622K02P046_radius_le :
    (momentScalarGrow2622K02P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P046Expected]

end ConnesWeilRH.Dev
