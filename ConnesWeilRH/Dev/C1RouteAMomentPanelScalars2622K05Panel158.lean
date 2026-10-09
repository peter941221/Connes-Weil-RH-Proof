import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P158 : ℚ := ((-797420908358185862040463329673832301139 : ℚ) / 14353861276504287159027469735113523200)

def momentPanelGrowth2622K05P158 : ℚ := ((42377390989956203201179267538593041854769 : ℚ) / 27834687528149471998910075183234337996800)

theorem momentPanelPhase_owner2622K05P158 :
    (momentPanelPhase2622K05P158 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (137 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P158, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P158 :
    (momentPanelGrowth2622K05P158 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (137 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P158, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P158Input : RatPair2542 := (momentPanelPhase2622K05P158 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P158Expected : RatState2542 :=
  ((((1594433201034060554169813000655569354617381196009431658062295441851142475 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((138723216576613237115213 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K05P158_replay :
    compactExp2620 momentScalarAmp2622K05P158Input 20 = momentScalarAmp2622K05P158Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P158_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (137 / 200) 0) -
      (momentScalarAmp2622K05P158Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P158]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P158 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P158 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P158Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P158_replay] at h
  simpa only [momentPanelPhase_owner2622K05P158] using h

theorem momentScalarAmp2622K05P158_radius_le :
    (momentScalarAmp2622K05P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P158Expected]

def momentScalarGrow2622K05P158Input : RatPair2542 := (momentPanelGrowth2622K05P158 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P158Expected : RatState2542 :=
  ((((4895167975810238957193375423628081518017630431058150129699900192447444366927791353590726732616741 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6205353612961088608007506191061514442776642621703 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P158_replay :
    compactExp2620 momentScalarGrow2622K05P158Input 20 = momentScalarGrow2622K05P158Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P158_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (137 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P158Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P158Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P158 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P158]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P158 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P158 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P158Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P158Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P158_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P158] using h

theorem momentScalarGrow2622K05P158_radius_le :
    (momentScalarGrow2622K05P158Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P158Expected]

end ConnesWeilRH.Dev
