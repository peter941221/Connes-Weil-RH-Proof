import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K24
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K24P070 : ℚ := ((-2457459895695138240631761187277752316289 : ℚ) / 78044683913891262624306628223460966400)

def momentPanelGrowth2622K24P070 : ℚ := ((443260906562525261061717142776107 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K24P070 :
    (momentPanelPhase2622K24P070 : ℝ) = momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K24P070 :
    (momentPanelGrowth2622K24P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K24P070Input : RatPair2542 := (momentPanelPhase2622K24P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K24P070Expected : RatState2542 :=
  ((((45143559310803154826624582486057475106148722968466818324309993365754031334991967083 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57227978541580612795234391572774787 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K24P070_replay :
    compactExp2620 momentScalarAmp2622K24P070Input 20 = momentScalarAmp2622K24P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K24P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K24P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K24P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K24P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelPhase2622K24P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K24P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K24P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K24P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K24P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K24P070_replay] at h
  simpa only [momentPanelPhase_owner2622K24P070] using h

theorem momentScalarAmp2622K24P070_radius_le :
    (momentScalarAmp2622K24P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarAmp2622K24P070Expected]

def momentScalarGrow2622K24P070Input : RatPair2542 := (momentPanelGrowth2622K24P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K24P070Expected : RatState2542 :=
  ((((2471005579724385657932593219856803294297847555016199979731030899119436335657137719833409485228171 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3132371271071766685488347639442801183545476999163 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K24P070_replay :
    compactExp2620 momentScalarGrow2622K24P070Input 20 = momentScalarGrow2622K24P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K24P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 24).re * (storedWidth 24 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K24P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K24P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K24P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentPanelGrowth2622K24P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K24P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K24P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K24P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K24P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K24P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K24P070] using h

theorem momentScalarGrow2622K24P070_radius_le :
    (momentScalarGrow2622K24P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, momentScalarGrow2622K24P070Expected]

end ConnesWeilRH.Dev
