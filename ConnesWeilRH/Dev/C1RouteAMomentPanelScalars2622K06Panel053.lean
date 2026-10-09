import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P053 : ℚ := ((-20843661 : ℚ) / 577850)

def momentPanelGrowth2622K06P053 : ℚ := ((209831387 : ℚ) / 620784675)

theorem momentPanelPhase_owner2622K06P053 :
    (momentPanelPhase2622K06P053 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P053 :
    (momentPanelGrowth2622K06P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P053Input : RatPair2542 := (momentPanelPhase2622K06P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P053Expected : RatState2542 :=
  ((((461463191581196617681658419713113287354386494156289335037820235149727171442266039 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((292497108844161654893099622979135 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P053_replay :
    compactExp2620 momentScalarAmp2622K06P053Input 20 = momentScalarAmp2622K06P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K06P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P053_replay] at h
  simpa only [momentPanelPhase_owner2622K06P053] using h

theorem momentScalarAmp2622K06P053_radius_le :
    (momentScalarAmp2622K06P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P053Expected]

def momentScalarGrow2622K06P053Input : RatPair2542 := (momentPanelGrowth2622K06P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P053Expected : RatState2542 :=
  ((((748745922428288197151135916740241270031204735515187941514567678118863855128302911144592640044329 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3796591648101832805958472093128716375380098478613 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P053_replay :
    compactExp2620 momentScalarGrow2622K06P053Input 20 = momentScalarGrow2622K06P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P053] using h

theorem momentScalarGrow2622K06P053_radius_le :
    (momentScalarGrow2622K06P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P053Expected]

end ConnesWeilRH.Dev
