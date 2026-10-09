import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P176 : ℚ := ((-110790942582633994743716292386748831423660384077766281 : ℚ) / 958254100882781464142533199888391034567376083353600)

def momentPanelGrowth2622K02P176 : ℚ := ((7484717758636387049825302300898704120582658924773624719 : ℚ) / 843469275169366617264289714909981782668443707139686400)

theorem momentPanelPhase_owner2622K02P176 :
    (momentPanelPhase2622K02P176 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (173 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P176, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P176 :
    (momentPanelGrowth2622K02P176 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P176, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P176Input : RatPair2542 := (momentPanelPhase2622K02P176 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P176Expected : RatState2542 :=
  ((((3277153465973687733963608474276846239512850979 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P176_replay :
    compactExp2620 momentScalarAmp2622K02P176Input 20 = momentScalarAmp2622K02P176Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P176_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (173 / 200) 0) -
      (momentScalarAmp2622K02P176Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P176]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P176 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P176 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P176Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P176_replay] at h
  simpa only [momentPanelPhase_owner2622K02P176] using h

theorem momentScalarAmp2622K02P176_radius_le :
    (momentScalarAmp2622K02P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P176Expected]

def momentScalarGrow2622K02P176Input : RatPair2542 := (momentPanelGrowth2622K02P176 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P176Expected : RatState2542 :=
  ((((15254927445594660243694134801259484357159761963690048614605155162263510045424865427446931504014227035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19337754283557161944254090588526975625285936229142093 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P176_replay :
    compactExp2620 momentScalarGrow2622K02P176Input 20 = momentScalarGrow2622K02P176Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P176_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P176Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P176Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P176 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P176]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P176 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P176 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P176Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P176Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P176_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P176] using h

theorem momentScalarGrow2622K02P176_radius_le :
    (momentScalarGrow2622K02P176Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P176Expected]

end ConnesWeilRH.Dev
