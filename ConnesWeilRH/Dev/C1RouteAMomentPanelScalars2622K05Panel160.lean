import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P160 : ℚ := ((-2393291247298729266426362325272616687669 : ℚ) / 40806179881586795725939474862335590400)

def momentPanelGrowth2622K05P160 : ℚ := ((14517823532819882394825772504054243560203 : ℚ) / 8312975781405638569714092740875753881600)

theorem momentPanelPhase_owner2622K05P160 :
    (momentPanelPhase2622K05P160 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (141 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P160, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P160 :
    (momentPanelGrowth2622K05P160 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P160, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P160Input : RatPair2542 := (momentPanelPhase2622K05P160 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P160Expected : RatState2542 :=
  ((((72132937915800690993808333036316417966578282313043565594855465036133761 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((313662014489361178233913 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P160_replay :
    compactExp2620 momentScalarAmp2622K05P160Input 20 = momentScalarAmp2622K05P160Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P160_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (141 / 200) 0) -
      (momentScalarAmp2622K05P160Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P160]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P160 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P160 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P160Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P160_replay] at h
  simpa only [momentPanelPhase_owner2622K05P160] using h

theorem momentScalarAmp2622K05P160_radius_le :
    (momentScalarAmp2622K05P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P160Expected]

def momentScalarGrow2622K05P160Input : RatPair2542 := (momentPanelGrowth2622K05P160 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P160Expected : RatState2542 :=
  ((((12247648748398724921285247312937174925374109406524132207993321686751321341530236116838111209881267 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7762856714584133291794222553416613809344331207459 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P160_replay :
    compactExp2620 momentScalarGrow2622K05P160Input 20 = momentScalarGrow2622K05P160Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P160_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P160Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P160Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P160 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P160]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P160 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P160 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P160Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P160Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P160_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P160] using h

theorem momentScalarGrow2622K05P160_radius_le :
    (momentScalarGrow2622K05P160Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P160Expected]

end ConnesWeilRH.Dev
