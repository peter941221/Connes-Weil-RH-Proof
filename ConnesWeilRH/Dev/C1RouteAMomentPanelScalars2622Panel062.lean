import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P062 : ℚ := ((-14914608717044508625669580665148853528767789019622233 : ℚ) / 450325192002584461671510389080704705431484214804480)

def momentPanelGrowth2622P062 : ℚ := ((13687328601506354312582255228828227496596780904717 : ℚ) / 61657100324897466861717953880218189891734654156800)

theorem momentPanelPhase_owner2622P062 :
    (momentPanelPhase2622P062 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 40) 0 := by
  norm_num [momentPanelPhase2622P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P062 :
    (momentPanelGrowth2622P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P062Input : RatPair2542 := (momentPanelPhase2622P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P062Expected : RatState2542 :=
  ((((2207299517954746631022120362788714877748006845999459947777113327184238478966362907 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5596345878604126778657327066048391 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P062_replay :
    compactExp2620 momentScalarAmp2622P062Input 20 = momentScalarAmp2622P062Expected := by
  decide +kernel

theorem momentScalarAmp2622P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P062]
  have h := compactExp_real_error2620 momentPanelPhase2622P062 20 hsmall
  change |Real.exp (momentPanelPhase2622P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P062_replay] at h
  simpa only [momentPanelPhase_owner2622P062] using h

theorem momentScalarAmp2622P062_radius_le :
    (momentScalarAmp2622P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P062Expected]

def momentScalarGrow2622P062Input : RatPair2542 := (momentPanelGrowth2622P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P062Expected : RatState2542 :=
  ((((2666908587557545627255474422703870014088397273477259322070634820030310480697912751605737614153167 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1690353778025421904394537709354087210667306450791 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P062_replay :
    compactExp2620 momentScalarGrow2622P062Input 20 = momentScalarGrow2622P062Expected := by
  decide +kernel

theorem momentScalarGrow2622P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P062_replay] at h
  simpa only [momentPanelGrowth_owner2622P062] using h

theorem momentScalarGrow2622P062_radius_le :
    (momentScalarGrow2622P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P062Expected]

end ConnesWeilRH.Dev
