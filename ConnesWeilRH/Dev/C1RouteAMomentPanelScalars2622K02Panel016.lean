import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P016 : ℚ := ((-358314850868918973308016453464217516794780755463489883 : ℚ) / 5249702463311061634508587452829133010643018632396800)

def momentPanelGrowth2622K02P016 : ℚ := ((134508476925770291130601795345441867285214250724415773 : ℚ) / 60855986194981611580479937965566188271683018476748800)

theorem momentPanelPhase_owner2622K02P016 :
    (momentPanelPhase2622K02P016 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-147 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P016 :
    (momentPanelGrowth2622K02P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P016Input : RatPair2542 := (momentPanelPhase2622K02P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P016Expected : RatState2542 :=
  ((((2432740634367308362249677464052396202050287431956045593158247781567 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208928903680500858300039 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P016_replay :
    compactExp2620 momentScalarAmp2622K02P016Input 20 = momentScalarAmp2622K02P016Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622K02P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P016]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P016 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P016_replay] at h
  simpa only [momentPanelPhase_owner2622K02P016] using h

theorem momentScalarAmp2622K02P016_radius_le :
    (momentScalarAmp2622K02P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P016Expected]

def momentScalarGrow2622K02P016Input : RatPair2542 := (momentPanelGrowth2622K02P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P016Expected : RatState2542 :=
  ((((4869102791789183847150339286008029643430857824237465489673510084889994124939079206209692773918971 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((12344616132138949093510548100578184085652246078569 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P016_replay :
    compactExp2620 momentScalarGrow2622K02P016Input 20 = momentScalarGrow2622K02P016Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P016_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P016] using h

theorem momentScalarGrow2622K02P016_radius_le :
    (momentScalarGrow2622K02P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P016Expected]

end ConnesWeilRH.Dev
