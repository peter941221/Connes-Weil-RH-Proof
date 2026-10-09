import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P127 : ℚ := ((-30681509300069857265810808215664639 : ℚ) / 892426022560673498653679056584704)

def momentPanelGrowth2622K05P127 : ℚ := ((503533443422339668183978542456200821523 : ℚ) / 1546642243169819406262746028353100185600)

theorem momentPanelPhase_owner2622K05P127 :
    (momentPanelPhase2622K05P127 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P127 :
    (momentPanelGrowth2622K05P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P127Input : RatPair2542 := (momentPanelPhase2622K05P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P127Expected : RatState2542 :=
  ((((1251905958720749764588815494113147539416053960661904712357946268194620665652772355 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1587031374702700417195845523598901 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P127_replay :
    compactExp2620 momentScalarAmp2622K05P127Input 20 = momentScalarAmp2622K05P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K05P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P127_replay] at h
  simpa only [momentPanelPhase_owner2622K05P127] using h

theorem momentScalarAmp2622K05P127_radius_le :
    (momentScalarAmp2622K05P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P127Expected]

def momentScalarGrow2622K05P127Input : RatPair2542 := (momentPanelGrowth2622K05P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P127Expected : RatState2542 :=
  ((((1478971965073249942101029892496584933381052538554765778249599656069909276917479643508307927252179 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3749638234290637394472849210440019794709510063013 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P127_replay :
    compactExp2620 momentScalarGrow2622K05P127Input 20 = momentScalarGrow2622K05P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P127] using h

theorem momentScalarGrow2622K05P127_radius_le :
    (momentScalarGrow2622K05P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P127Expected]

end ConnesWeilRH.Dev
