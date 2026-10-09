import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P106 : ℚ := ((-335046645910491148903736299966247178505140318313370223 : ℚ) / 11107126994176320986371793071449861050357810777292800)

def momentPanelGrowth2622K02P106 : ℚ := ((668691730138847526301997951334246334592965560200169253 : ℚ) / 4486482758709934482284585771466194101108940343135436800)

theorem momentPanelPhase_owner2622K02P106 :
    (momentPanelPhase2622K02P106 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P106, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P106 :
    (momentPanelGrowth2622K02P106 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P106, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P106Input : RatPair2542 := (momentPanelPhase2622K02P106 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P106Expected : RatState2542 :=
  ((((169472526763220948126631460119108234846642732840954174086510146991681805711786566827 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((214838130564411192656725308358660303 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P106_replay :
    compactExp2620 momentScalarAmp2622K02P106Input 20 = momentScalarAmp2622K02P106Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P106_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 200) 0) -
      (momentScalarAmp2622K02P106Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P106]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P106 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P106 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P106Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P106_replay] at h
  simpa only [momentPanelPhase_owner2622K02P106] using h

theorem momentScalarAmp2622K02P106_radius_le :
    (momentScalarAmp2622K02P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P106Expected]

def momentScalarGrow2622K02P106Input : RatPair2542 := (momentPanelGrowth2622K02P106 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P106Expected : RatState2542 :=
  ((((2479296182882330525102773782088740497123398760806459401877890399059980413370724774946303930340537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3142880847641397560306972611731845550379828691375 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P106_replay :
    compactExp2620 momentScalarGrow2622K02P106Input 20 = momentScalarGrow2622K02P106Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P106_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P106Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P106Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P106 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P106]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P106 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P106 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P106Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P106Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P106_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P106] using h

theorem momentScalarGrow2622K02P106_radius_le :
    (momentScalarGrow2622K02P106Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P106Expected]

end ConnesWeilRH.Dev
