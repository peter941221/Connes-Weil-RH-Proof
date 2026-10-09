import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P166 : ℚ := ((-2397561100038682595433296236812371437353 : ℚ) / 33650545773418486400370884608629145600)

def momentPanelGrowth2622K05P166 : ℚ := ((15696515806448900791722026820391289593883 : ℚ) / 5602353432335214727576086290007431577600)

theorem momentPanelPhase_owner2622K05P166 :
    (momentPanelPhase2622K05P166 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (153 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P166, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P166 :
    (momentPanelGrowth2622K05P166 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P166, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P166Input : RatPair2542 := (momentPanelPhase2622K05P166 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P166Expected : RatState2542 :=
  ((((15223577766332766220234281352274059400268556028323066810959844643 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1208925974010540496681061 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P166_replay :
    compactExp2620 momentScalarAmp2622K05P166Input 20 = momentScalarAmp2622K05P166Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P166_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (153 / 200) 0) -
      (momentScalarAmp2622K05P166Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P166]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P166 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P166 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P166Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P166_replay] at h
  simpa only [momentPanelPhase_owner2622K05P166] using h

theorem momentScalarAmp2622K05P166_radius_le :
    (momentScalarAmp2622K05P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P166Expected]

def momentScalarGrow2622K05P166Input : RatPair2542 := (momentPanelGrowth2622K05P166 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P166Expected : RatState2542 :=
  ((((35187842595368202514691366140009513998112067794067355256275771252903864655245777233770465098556011 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22302885300483534652349846415927801786486129351447 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P166_replay :
    compactExp2620 momentScalarGrow2622K05P166Input 20 = momentScalarGrow2622K05P166Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P166_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P166Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P166Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P166 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P166]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P166 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P166 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P166Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P166Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P166_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P166] using h

theorem momentScalarGrow2622K05P166_radius_le :
    (momentScalarGrow2622K05P166Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P166Expected]

end ConnesWeilRH.Dev
