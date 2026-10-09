import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P144 : ℚ := ((-108218213909479369569160174440185002529016240024605897 : ℚ) / 2675518524746592393031862878330023582663096821350400)

def momentPanelGrowth2622K02P144 : ℚ := ((2663362599423283454124732185693596171873640784877013 : ℚ) / 3703279588264154103381934604930605030372312665292800)

theorem momentPanelPhase_owner2622K02P144 :
    (momentPanelPhase2622K02P144 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (109 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P144 :
    (momentPanelGrowth2622K02P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P144Input : RatPair2542 := (momentPanelPhase2622K02P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P144Expected : RatState2542 :=
  ((((5800208438252065773145508797687890381202163510995874177572074231504163046433865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((919115468842220016227411656575 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P144_replay :
    compactExp2620 momentScalarAmp2622K02P144Input 20 = momentScalarAmp2622K02P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K02P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P144_replay] at h
  simpa only [momentPanelPhase_owner2622K02P144] using h

theorem momentScalarAmp2622K02P144_radius_le :
    (momentScalarAmp2622K02P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P144Expected]

def momentScalarGrow2622K02P144Input : RatPair2542 := (momentPanelGrowth2622K02P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P144Expected : RatState2542 :=
  ((((4384690794256732069422534927820474808522470748960562182317611410748037228685778578376050589228855 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2779126052448423118029824415083420724249904528177 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P144_replay :
    compactExp2620 momentScalarGrow2622K02P144Input 20 = momentScalarGrow2622K02P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P144] using h

theorem momentScalarGrow2622K02P144_radius_le :
    (momentScalarGrow2622K02P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P144Expected]

end ConnesWeilRH.Dev
