import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P035 : ℚ := ((-120141416923474211400165580671734219292223219815394103 : ℚ) / 2675518524746592393031862878330023582663096821350400)

def momentPanelGrowth2622K02P035 : ℚ := ((2663362599423283454124732185693596171873640784877013 : ℚ) / 3703279588264154103381934604930605030372312665292800)

theorem momentPanelPhase_owner2622K02P035 :
    (momentPanelPhase2622K02P035 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P035 :
    (momentPanelGrowth2622K02P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P035Input : RatPair2542 := (momentPanelPhase2622K02P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P035Expected : RatState2542 :=
  ((((33652711520841361506433722639769823331553837587594603768787139353488611146899 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((42662915780426531617146349433 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P035_replay :
    compactExp2620 momentScalarAmp2622K02P035Input 20 = momentScalarAmp2622K02P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K02P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P035_replay] at h
  simpa only [momentPanelPhase_owner2622K02P035] using h

theorem momentScalarAmp2622K02P035_radius_le :
    (momentScalarAmp2622K02P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P035Expected]

def momentScalarGrow2622K02P035Input : RatPair2542 := (momentPanelGrowth2622K02P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P035Expected : RatState2542 :=
  ((((4384690794256732069422534927820474808522470748960562182317611410748037228685778578376050589228855 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2779126052448423118029824415083420724249904528177 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P035_replay :
    compactExp2620 momentScalarGrow2622K02P035Input 20 = momentScalarGrow2622K02P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P035] using h

theorem momentScalarGrow2622K02P035_radius_le :
    (momentScalarGrow2622K02P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P035Expected]

end ConnesWeilRH.Dev
