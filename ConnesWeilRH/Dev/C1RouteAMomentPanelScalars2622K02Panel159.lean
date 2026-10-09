import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P159 : ℚ := ((-108588925942715128880516027460274093946667437748552767 : ℚ) / 1967603669164436292026953037483073995017254495846400)

def momentPanelGrowth2622K02P159 : ℚ := ((204873819632941156887362374278214102016669501807693 : ℚ) / 123742374957606721687753393551271228324384132300800)

theorem momentPanelPhase_owner2622K02P159 :
    (momentPanelPhase2622K02P159 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (139 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P159 :
    (momentPanelGrowth2622K02P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P159Input : RatPair2542 := (momentPanelPhase2622K02P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P159Expected : RatState2542 :=
  ((((2299190380839226065342783028403195137045508763461460199062327990694995595 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5332575108571187093123691 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P159_replay :
    compactExp2620 momentScalarAmp2622K02P159Input 20 = momentScalarAmp2622K02P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K02P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P159_replay] at h
  simpa only [momentPanelPhase_owner2622K02P159] using h

theorem momentScalarAmp2622K02P159_radius_le :
    (momentScalarAmp2622K02P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P159Expected]

def momentScalarGrow2622K02P159Input : RatPair2542 := (momentPanelGrowth2622K02P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P159Expected : RatState2542 :=
  ((((11185036790789692088729401551031621095347415623294079555545770919587643548475801593717186911434525 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14178696213963420324244647738160340663106766987999 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P159_replay :
    compactExp2620 momentScalarGrow2622K02P159Input 20 = momentScalarGrow2622K02P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P159] using h

theorem momentScalarGrow2622K02P159_radius_le :
    (momentScalarGrow2622K02P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P159Expected]

end ConnesWeilRH.Dev
