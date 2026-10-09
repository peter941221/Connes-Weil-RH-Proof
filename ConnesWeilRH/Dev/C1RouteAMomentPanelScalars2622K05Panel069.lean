import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P069 : ℚ := ((-818791095132084791215583011984382321677 : ℚ) / 25906721786744278632507824067628236800)

def momentPanelGrowth2622K05P069 : ℚ := ((14085602756020106866513062965719049149809 : ℚ) / 92664732548154354488561502881814727884800)

theorem momentPanelPhase_owner2622K05P069 :
    (momentPanelPhase2622K05P069 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-41 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P069, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P069 :
    (momentPanelGrowth2622K05P069 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P069, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P069Input : RatPair2542 := (momentPanelPhase2622K05P069 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P069Expected : RatState2542 :=
  ((((40139140808952490443030035115346493780542023375131546512941820987763801288184852817 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((50883939622116824670521054075248183 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P069_replay :
    compactExp2620 momentScalarAmp2622K05P069Input 20 = momentScalarAmp2622K05P069Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P069_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-41 / 200) 0) -
      (momentScalarAmp2622K05P069Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P069]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P069 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P069 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P069Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P069_replay] at h
  simpa only [momentPanelPhase_owner2622K05P069] using h

theorem momentScalarAmp2622K05P069_radius_le :
    (momentScalarAmp2622K05P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P069Expected]

def momentScalarGrow2622K05P069Input : RatPair2542 := (momentPanelGrowth2622K05P069 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P069Expected : RatState2542 :=
  ((((1243323145854175164322395697728722145032017679309152507388345477446620009323590814849078395344469 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1576099103641584393512504582278046256971525259581 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P069_replay :
    compactExp2620 momentScalarGrow2622K05P069Input 20 = momentScalarGrow2622K05P069Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P069_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P069Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P069]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P069 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P069 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P069Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P069_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P069] using h

theorem momentScalarGrow2622K05P069_radius_le :
    (momentScalarGrow2622K05P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P069Expected]

end ConnesWeilRH.Dev
