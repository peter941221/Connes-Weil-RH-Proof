import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K21
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K21P104 : ℚ := ((-805350817806350741308462554629524314847 : ℚ) / 26474629255646525404378347103636684800)

def momentPanelGrowth2622K21P104 : ℚ := ((17004590611118933857969825975319498089 : ℚ) / 155039753130793551304173986192870604800)

theorem momentPanelPhase_owner2622K21P104 :
    (momentPanelPhase2622K21P104 : ℝ) = momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (29 / 200) 0 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P104, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K21P104 :
    (momentPanelGrowth2622K21P104 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2))
      (29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P104, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K21P104Input : RatPair2542 := (momentPanelPhase2622K21P104 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K21P104Expected : RatState2542 :=
  ((((65682842075492845737893807112509914922183177488220573176467456982206710252216488177 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((166530619433263410672055897250561295 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K21P104_replay :
    compactExp2620 momentScalarAmp2622K21P104Input 20 = momentScalarAmp2622K21P104Expected := by
  decide +kernel

theorem momentScalarAmp2622K21P104_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (29 / 200) 0) -
      (momentScalarAmp2622K21P104Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K21P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K21P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelPhase2622K21P104]
  have h := compactExp_real_error2620 momentPanelPhase2622K21P104 20 hsmall
  change |Real.exp (momentPanelPhase2622K21P104 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K21P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K21P104Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K21P104_replay] at h
  simpa only [momentPanelPhase_owner2622K21P104] using h

theorem momentScalarAmp2622K21P104_radius_le :
    (momentScalarAmp2622K21P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarAmp2622K21P104Expected]

def momentScalarGrow2622K21P104Input : RatPair2542 := (momentPanelGrowth2622K21P104 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K21P104Expected : RatState2542 :=
  ((((595897502300105724758229802038374221672517847292077005672042851917241865687660159568431171830885 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1510779494906007601523374725131654553683058673101 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K21P104_replay :
    compactExp2620 momentScalarGrow2622K21P104Input 20 = momentScalarGrow2622K21P104Expected := by
  decide +kernel

theorem momentScalarGrow2622K21P104_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 21).re * (storedWidth 21 ^ 2)) (29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K21P104Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K21P104Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K21P104 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentPanelGrowth2622K21P104]
  have h := compactExp_real_error2620 momentPanelGrowth2622K21P104 20 hsmall
  change |Real.exp (momentPanelGrowth2622K21P104 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K21P104Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K21P104Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K21P104_replay] at h
  simpa only [momentPanelGrowth_owner2622K21P104] using h

theorem momentScalarGrow2622K21P104_radius_le :
    (momentScalarGrow2622K21P104Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, momentScalarGrow2622K21P104Expected]

end ConnesWeilRH.Dev
