import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K21
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K21P011 : ℚ := ((-823914658409273224728873914803136128161 : ℚ) / 10378508994188559755933808483054387200)

def momentPanelGrowth2622K21P011 : ℚ := ((16097082558531855165508062265950047854963 : ℚ) / 4776534842912933314594650006646004121600)

theorem momentPanelPhase_owner2622K21P011 :
    (momentPanelPhase2622K21P011 : ℝ) = momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K21P011 :
    (momentPanelGrowth2622K21P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K21P011Input : RatPair2542 := (momentPanelPhase2622K21P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K21P011Expected : RatState2542 :=
  ((((278093900721921390180188876571481962155120114828930681009231 : ℚ) / 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096), 0), ((1208925819659755920255805 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K21P011_replay :
    compactExp2620 momentScalarAmp2622K21P011Input 20 = momentScalarAmp2622K21P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K21P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K21P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K21P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K21P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K21P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K21P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K21P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K21P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K21P011_replay] at h
  simpa only [momentPanelPhase_owner2622K21P011] using h

theorem momentScalarAmp2622K21P011_radius_le :
    (momentScalarAmp2622K21P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarAmp2622K21P011Expected]

def momentScalarGrow2622K21P011Input : RatPair2542 := (momentPanelGrowth2622K21P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K21P011Expected : RatState2542 :=
  ((((15528359799222579467487227721663833753489855469615958607372949175290847630698196323043488589317271 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((78737885422945699109449242268267187096836011035303 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K21P011_replay :
    compactExp2620 momentScalarGrow2622K21P011Input 20 = momentScalarGrow2622K21P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K21P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K21P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K21P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K21P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K21P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K21P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K21P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K21P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K21P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K21P011] using h

theorem momentScalarGrow2622K21P011_radius_le :
    (momentScalarGrow2622K21P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarGrow2622K21P011Expected]

end ConnesWeilRH.Dev
