import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P071 : ℚ := ((-818779824700071800690244039104089694681 : ℚ) / 26117658846622256004916875481002803200)

def momentPanelGrowth2622K10P071 : ℚ := ((4340095942279694619717784497665467024483 : ℚ) / 31407419782145991187919086734190156185600)

theorem momentPanelPhase_owner2622K10P071 :
    (momentPanelPhase2622K10P071 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-37 / 200) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P071, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P071 :
    (momentPanelGrowth2622K10P071 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (-37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P071, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P071Input : RatPair2542 := (momentPanelPhase2622K10P071 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P071Expected : RatState2542 :=
  ((((51833746972874418198837323766826195219483657971366603974397937720167186411671383073 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4106815310179469652965785167383107 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K10P071_replay :
    compactExp2620 momentScalarAmp2622K10P071Input 20 = momentScalarAmp2622K10P071Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P071_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-37 / 200) 0) -
      (momentScalarAmp2622K10P071Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P071]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P071 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P071 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P071Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P071_replay] at h
  simpa only [momentPanelPhase_owner2622K10P071] using h

theorem momentScalarAmp2622K10P071_radius_le :
    (momentScalarAmp2622K10P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P071Expected]

def momentScalarGrow2622K10P071Input : RatPair2542 := (momentPanelGrowth2622K10P071 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P071Expected : RatState2542 :=
  ((((2452519379437837182586339776627718075011892571525405316055288242450398251341032767574050566570795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((777234313425826486471253860598201103925996889047 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K10P071_replay :
    compactExp2620 momentScalarGrow2622K10P071Input 20 = momentScalarGrow2622K10P071Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P071_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P071Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P071]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P071 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P071 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P071Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P071_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P071] using h

theorem momentScalarGrow2622K10P071_radius_le :
    (momentScalarGrow2622K10P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P071Expected]

end ConnesWeilRH.Dev
