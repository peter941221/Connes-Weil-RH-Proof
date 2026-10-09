import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P063 : ℚ := ((-118013799440233386324306526606366610975863876051587839 : ℚ) / 3538717929295156929095914232653078241147381979545600)

def momentPanelGrowth2622K02P063 : ℚ := ((2813687515176782750745923834979445393848176081315285439 : ℚ) / 12267399585200244106514828406426608369458859987068518400)

theorem momentPanelPhase_owner2622K02P063 :
    (momentPanelPhase2622K02P063 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-53 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P063, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P063 :
    (momentPanelGrowth2622K02P063 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P063, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P063Input : RatPair2542 := (momentPanelPhase2622K02P063 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P063Expected : RatState2542 :=
  ((((7017420858648646844638554794321622159574868198247973797690822707362745838307221145 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1111990086335025553464385143726369 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P063_replay :
    compactExp2620 momentScalarAmp2622K02P063Input 20 = momentScalarAmp2622K02P063Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P063_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-53 / 200) 0) -
      (momentScalarAmp2622K02P063Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P063]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P063 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P063 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P063Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P063_replay] at h
  simpa only [momentPanelPhase_owner2622K02P063] using h

theorem momentScalarAmp2622K02P063_radius_le :
    (momentScalarAmp2622K02P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P063Expected]

def momentScalarGrow2622K02P063Input : RatPair2542 := (momentPanelGrowth2622K02P063 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P063Expected : RatState2542 :=
  ((((671660339158704609457345460045805859952812520209694826538937639600898293592142585964870062389109 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3405721783376628735267709298061503201704643480893 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P063_replay :
    compactExp2620 momentScalarGrow2622K02P063Input 20 = momentScalarGrow2622K02P063Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P063_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P063Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P063]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P063 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P063 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P063Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P063_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P063] using h

theorem momentScalarGrow2622K02P063_radius_le :
    (momentScalarGrow2622K02P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P063Expected]

end ConnesWeilRH.Dev
