import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P163 : ℚ := ((-326764041629941769599960811871540148668937624056510117 : ℚ) / 5249702463311061634508587452829133010643018632396800)

def momentPanelGrowth2622K02P163 : ℚ := ((134508476925770291130601795345441867285214250724415773 : ℚ) / 60855986194981611580479937965566188271683018476748800)

theorem momentPanelPhase_owner2622K02P163 :
    (momentPanelPhase2622K02P163 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P163 :
    (momentPanelGrowth2622K02P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P163Input : RatPair2542 := (momentPanelPhase2622K02P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P163Expected : RatState2542 :=
  ((((1982639259557633815008247972767284337131037112962941966339969203324457 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1210182541136175449999845 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P163_replay :
    compactExp2620 momentScalarAmp2622K02P163Input 20 = momentScalarAmp2622K02P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K02P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P163_replay] at h
  simpa only [momentPanelPhase_owner2622K02P163] using h

theorem momentScalarAmp2622K02P163_radius_le :
    (momentScalarAmp2622K02P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P163Expected]

def momentScalarGrow2622K02P163Input : RatPair2542 := (momentPanelGrowth2622K02P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P163Expected : RatState2542 :=
  ((((4869102791789183847150339286008029643430857824237465489673510084889994124939079206209692773918971 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((12344616132138949093510548100578184085652246078569 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P163_replay :
    compactExp2620 momentScalarGrow2622K02P163Input 20 = momentScalarGrow2622K02P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P163] using h

theorem momentScalarGrow2622K02P163_radius_le :
    (momentScalarGrow2622K02P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P163Expected]

end ConnesWeilRH.Dev
