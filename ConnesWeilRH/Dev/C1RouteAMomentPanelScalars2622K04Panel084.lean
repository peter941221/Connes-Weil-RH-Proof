import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P084 : ℚ := ((-116156160679886749175455188232029211458234708624753521 : ℚ) / 3794480715828064939781559078378427769587170174566400)

def momentPanelGrowth2622K04P084 : ℚ := ((115980743995557198566572435811534009016771799014495687 : ℚ) / 885618754030359024471703016159764273036098980439654400)

theorem momentPanelPhase_owner2622K04P084 :
    (momentPanelPhase2622K04P084 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P084 :
    (momentPanelGrowth2622K04P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P084Input : RatPair2542 := (momentPanelPhase2622K04P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P084Expected : RatState2542 :=
  ((((27100120486065509179605200033854164532988237265079900342250208827529523610197861367 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((34354486922918730789757770173641803 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P084_replay :
    compactExp2620 momentScalarAmp2622K04P084Input 20 = momentScalarAmp2622K04P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K04P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P084_replay] at h
  simpa only [momentPanelPhase_owner2622K04P084] using h

theorem momentScalarAmp2622K04P084_radius_le :
    (momentScalarAmp2622K04P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P084Expected]

def momentScalarGrow2622K04P084Input : RatPair2542 := (momentPanelGrowth2622K04P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P084Expected : RatState2542 :=
  ((((76089353555567943216327847810722893873264298927465894380385672955396181891100873158102936933677 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((1543275242546334805313223000647330404223215936459 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P084_replay :
    compactExp2620 momentScalarGrow2622K04P084Input 20 = momentScalarGrow2622K04P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P084] using h

theorem momentScalarGrow2622K04P084_radius_le :
    (momentScalarGrow2622K04P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P084Expected]

end ConnesWeilRH.Dev
