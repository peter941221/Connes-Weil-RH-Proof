import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P145 : ℚ := ((-2389919655619642521796646280615727530159 : ℚ) / 56139681541947458566443596834563686400)

def momentPanelGrowth2622K05P145 : ℚ := ((45245724379255631763871475771360386883 : ℚ) / 62213249097760951274894601232161177600)

theorem momentPanelPhase_owner2622K05P145 :
    (momentPanelPhase2622K05P145 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (111 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P145 :
    (momentPanelGrowth2622K05P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P145Input : RatPair2542 := (momentPanelPhase2622K05P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P145Expected : RatState2542 :=
  ((((173463989436750684520790923910525570125021092087816494744885586295725370235513 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((879605049268201537608574619257 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P145_replay :
    compactExp2620 momentScalarAmp2622K05P145Input 20 = momentScalarAmp2622K05P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K05P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P145_replay] at h
  simpa only [momentPanelPhase_owner2622K05P145] using h

theorem momentScalarAmp2622K05P145_radius_le :
    (momentScalarAmp2622K05P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P145Expected]

def momentScalarGrow2622K05P145Input : RatPair2542 := (momentPanelGrowth2622K05P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P145Expected : RatState2542 :=
  ((((2210126997379167548746834312535050659630177062347528055196354903026594746425467645676136282905581 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5603333743271282694644193087617669236684098546865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P145_replay :
    compactExp2620 momentScalarGrow2622K05P145Input 20 = momentScalarGrow2622K05P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P145] using h

theorem momentScalarGrow2622K05P145_radius_le :
    (momentScalarGrow2622K05P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P145Expected]

end ConnesWeilRH.Dev
