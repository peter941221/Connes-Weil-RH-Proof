import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P074 : ℚ := ((-73184164874853822528340272785351713533464824180110275 : ℚ) / 2377315100823379959323068841017123866847831272718336)

def momentPanelGrowth2622K03P074 : ℚ := ((1175227764425913122588627875526329736400632874517475 : ℚ) / 11292566432394220941797934050888495054437748280655872)

theorem momentPanelPhase_owner2622K03P074 :
    (momentPanelPhase2622K03P074 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P074 :
    (momentPanelGrowth2622K03P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P074Input : RatPair2542 := (momentPanelPhase2622K03P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P074Expected : RatState2542 :=
  ((((91224911273556498320285416933621194757936259597741134920099645927436020949726299847 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((115644708612841567153385976575826219 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P074_replay :
    compactExp2620 momentScalarAmp2622K03P074Input 20 = momentScalarAmp2622K03P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K03P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P074_replay] at h
  simpa only [momentPanelPhase_owner2622K03P074] using h

theorem momentScalarAmp2622K03P074_radius_le :
    (momentScalarAmp2622K03P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P074Expected]

def momentScalarGrow2622K03P074Input : RatPair2542 := (momentPanelGrowth2622K03P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P074Expected : RatState2542 :=
  ((((296282534605871455328929887600645772095242347544651278137864525099671600854310051792990208539417 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3004661564430231808051912625893687117068560372055 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P074_replay :
    compactExp2620 momentScalarGrow2622K03P074Input 20 = momentScalarGrow2622K03P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P074] using h

theorem momentScalarGrow2622K03P074_radius_le :
    (momentScalarGrow2622K03P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P074Expected]

end ConnesWeilRH.Dev
