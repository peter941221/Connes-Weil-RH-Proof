import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P009 : ℚ := ((-1868618497139978898476331003242599507040272577112582883 : ℚ) / 21433834949981023109780915374804738160141535700582400)

def momentPanelGrowth2622K00P009 : ℚ := ((111636144970413008704601362130813247032767557772846501591 : ℚ) / 27007456415243396080751252638229924110169109657183846400)

theorem momentPanelPhase_owner2622K00P009 :
    (momentPanelPhase2622K00P009 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-161 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P009 :
    (momentPanelGrowth2622K00P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P009Input : RatPair2542 := (momentPanelPhase2622K00P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P009Expected : RatState2542 :=
  ((((29340395366525570997214292819720253010137530856208764485349 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229295546441365 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P009_replay :
    compactExp2620 momentScalarAmp2622K00P009Input 20 = momentScalarAmp2622K00P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K00P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P009_replay] at h
  simpa only [momentPanelPhase_owner2622K00P009] using h

theorem momentScalarAmp2622K00P009_radius_le :
    (momentScalarAmp2622K00P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P009Expected]

def momentScalarGrow2622K00P009Input : RatPair2542 := (momentPanelGrowth2622K00P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P009Expected : RatState2542 :=
  ((((133280956808721489616461612332715178362458099689047779951183059083436708945268178358741094583811453 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((84476509438189870295833123474781305676297002265541 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P009_replay :
    compactExp2620 momentScalarGrow2622K00P009Input 20 = momentScalarGrow2622K00P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P009] using h

theorem momentScalarGrow2622K00P009_radius_le :
    (momentScalarGrow2622K00P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622K00P009Expected]

end ConnesWeilRH.Dev
