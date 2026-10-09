import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P027 : ℚ := ((-52853201019410156674674388576371745 : ℚ) / 1054685299389886862045257066872832)

def momentPanelGrowth2622K05P027 : ℚ := ((38854297351595008593401826783701899694529 : ℚ) / 36886564674982383295754341854172990668800)

theorem momentPanelPhase_owner2622K05P027 :
    (momentPanelPhase2622K05P027 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-5 / 8) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P027 :
    (momentPanelGrowth2622K05P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P027Input : RatPair2542 := (momentPanelPhase2622K05P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P027Expected : RatState2542 :=
  ((((368043763201673465776511282680739635744003194824166284607772579643259898933 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((468991046560637067739097697 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P027_replay :
    compactExp2620 momentScalarAmp2622K05P027Input 20 = momentScalarAmp2622K05P027Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622K05P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P027]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P027 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P027_replay] at h
  simpa only [momentPanelPhase_owner2622K05P027] using h

theorem momentScalarAmp2622K05P027_radius_le :
    (momentScalarAmp2622K05P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P027Expected]

def momentScalarGrow2622K05P027Input : RatPair2542 := (momentPanelGrowth2622K05P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P027Expected : RatState2542 :=
  ((((1531090156978523942240975415600567236606357844669064545238736196317110581461145417718101149856529 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3881770813565476113158453525319444509553434404127 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P027_replay :
    compactExp2620 momentScalarGrow2622K05P027Input 20 = momentScalarGrow2622K05P027Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P027_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P027] using h

theorem momentScalarGrow2622K05P027_radius_le :
    (momentScalarGrow2622K05P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P027Expected]

end ConnesWeilRH.Dev
