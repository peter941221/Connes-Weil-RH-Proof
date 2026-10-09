import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P131 : ℚ := ((-798186246359859111878350993140707458681 : ℚ) / 22385695479550348646910581244375859200)

def momentPanelGrowth2622K05P131 : ℚ := ((1657912105976632041808988815283939134809 : ℚ) / 4299344507444939369029315841464519884800)

theorem momentPanelPhase_owner2622K05P131 :
    (momentPanelPhase2622K05P131 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (83 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P131 :
    (momentPanelGrowth2622K05P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P131Input : RatPair2542 := (momentPanelPhase2622K05P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P131Expected : RatState2542 :=
  ((((174702025235547728719258249744294412329161522482593890461544570671255070885570289 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((442937317024473426894637965280429 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P131_replay :
    compactExp2620 momentScalarAmp2622K05P131Input 20 = momentScalarAmp2622K05P131Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622K05P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P131]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P131 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P131_replay] at h
  simpa only [momentPanelPhase_owner2622K05P131] using h

theorem momentScalarAmp2622K05P131_radius_le :
    (momentScalarAmp2622K05P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P131Expected]

def momentScalarGrow2622K05P131Input : RatPair2542 := (momentPanelGrowth2622K05P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P131Expected : RatState2542 :=
  ((((3141023149251066071697374898208109000745922068045937491585261971145423911158574147572639658605083 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((497714802022400063697603837033146622644330195999 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K05P131_replay :
    compactExp2620 momentScalarGrow2622K05P131Input 20 = momentScalarGrow2622K05P131Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P131_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P131] using h

theorem momentScalarGrow2622K05P131_radius_le :
    (momentScalarGrow2622K05P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P131Expected]

end ConnesWeilRH.Dev
