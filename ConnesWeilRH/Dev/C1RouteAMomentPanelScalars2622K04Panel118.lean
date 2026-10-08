import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P118 : ℚ := ((-314226103668522953775630454061193621004923682380390711 : ℚ) / 10490555990927346317754613532647679151440464235724800)

def momentPanelGrowth2622K04P118 : ℚ := ((1205742906313042493611314868667642560210600211368205029 : ℚ) / 3990930941820883563902100416585573793795759653309644800)

theorem momentPanelPhase_owner2622K04P118 :
    (momentPanelPhase2622K04P118 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (57 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P118 :
    (momentPanelGrowth2622K04P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P118Input : RatPair2542 := (momentPanelPhase2622K04P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P118Expected : RatState2542 :=
  ((((209446604691800352949070211461717375439223473417261553314343867368461806640286159169 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((265512698585523141764771728439914967 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P118_replay :
    compactExp2620 momentScalarAmp2622K04P118Input 20 = momentScalarAmp2622K04P118Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622K04P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P118]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P118 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P118_replay] at h
  simpa only [momentPanelPhase_owner2622K04P118] using h

theorem momentScalarAmp2622K04P118_radius_le :
    (momentScalarAmp2622K04P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P118Expected]

def momentScalarGrow2622K04P118Input : RatPair2542 := (momentPanelGrowth2622K04P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P118Expected : RatState2542 :=
  ((((1444701008115901249929553621002150828636749495155257427454056884675200826877495121811961591060077 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1831375572423716913878611414969561424079203933057 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P118_replay :
    compactExp2620 momentScalarGrow2622K04P118Input 20 = momentScalarGrow2622K04P118Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P118_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P118] using h

theorem momentScalarGrow2622K04P118_radius_le :
    (momentScalarGrow2622K04P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P118Expected]

end ConnesWeilRH.Dev
