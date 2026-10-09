import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P073 : ℚ := ((-350032246588369594004240965369510486958578061206629777 : ℚ) / 11107126994176320986371793071449861050357810777292800)

def momentPanelGrowth2622K02P073 : ℚ := ((668691730138847526301997951334246334592965560200169253 : ℚ) / 4486482758709934482284585771466194101108940343135436800)

theorem momentPanelPhase_owner2622K02P073 :
    (momentPanelPhase2622K02P073 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-33 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P073 :
    (momentPanelGrowth2622K02P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P073Input : RatPair2542 := (momentPanelPhase2622K02P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P073Expected : RatState2542 :=
  ((((10992449506044790150030035356542185343923834206269481846019218339542943071788333807 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((27870008030426954573458761577881689 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P073_replay :
    compactExp2620 momentScalarAmp2622K02P073Input 20 = momentScalarAmp2622K02P073Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622K02P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P073]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P073 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P073_replay] at h
  simpa only [momentPanelPhase_owner2622K02P073] using h

theorem momentScalarAmp2622K02P073_radius_le :
    (momentScalarAmp2622K02P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P073Expected]

def momentScalarGrow2622K02P073Input : RatPair2542 := (momentPanelGrowth2622K02P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P073Expected : RatState2542 :=
  ((((2479296182882330525102773782088740497123398760806459401877890399059980413370724774946303930340537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3142880847641397560306972611731845550379828691375 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P073_replay :
    compactExp2620 momentScalarGrow2622K02P073Input 20 = momentScalarGrow2622K02P073Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P073_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P073] using h

theorem momentScalarGrow2622K02P073_radius_le :
    (momentScalarGrow2622K02P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P073Expected]

end ConnesWeilRH.Dev
