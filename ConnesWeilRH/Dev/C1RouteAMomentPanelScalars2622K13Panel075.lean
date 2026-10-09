import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P075 : ℚ := ((-817241950485782892607317548251755685153 : ℚ) / 26474629255646525404378347103636684800)

def momentPanelGrowth2622K13P075 : ℚ := ((17004590611118933857969825975319498089 : ℚ) / 155039753130793551304173986192870604800)

theorem momentPanelPhase_owner2622K13P075 :
    (momentPanelPhase2622K13P075 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-29 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P075, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P075 :
    (momentPanelGrowth2622K13P075 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (-29 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P075, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P075Input : RatPair2542 := (momentPanelPhase2622K13P075 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P075Expected : RatState2542 :=
  ((((83833519061896194357444757737360300313575400647430805966980218796398823107536686747 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26568684830152578074605783521986645 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K13P075_replay :
    compactExp2620 momentScalarAmp2622K13P075Input 20 = momentScalarAmp2622K13P075Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P075_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-29 / 200) 0) -
      (momentScalarAmp2622K13P075Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P075]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P075 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P075 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P075Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P075_replay] at h
  simpa only [momentPanelPhase_owner2622K13P075] using h

theorem momentScalarAmp2622K13P075_radius_le :
    (momentScalarAmp2622K13P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P075Expected]

def momentScalarGrow2622K13P075Input : RatPair2542 := (momentPanelGrowth2622K13P075 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P075Expected : RatState2542 :=
  ((((595897502300105724758229802038374221672517847292077005672042851917241865687660159568431171830885 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1510779494906007601523374725131654553683058673101 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K13P075_replay :
    compactExp2620 momentScalarGrow2622K13P075Input 20 = momentScalarGrow2622K13P075Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P075_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (-29 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P075Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P075Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P075 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P075]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P075 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P075 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P075Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P075Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P075_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P075] using h

theorem momentScalarGrow2622K13P075_radius_le :
    (momentScalarGrow2622K13P075Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P075Expected]

end ConnesWeilRH.Dev
