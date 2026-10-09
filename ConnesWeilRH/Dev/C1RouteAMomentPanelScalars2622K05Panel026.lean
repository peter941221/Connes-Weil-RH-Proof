import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P026 : ℚ := ((-825758478818135409985474507705880936971 : ℚ) / 16138713321625634156334827848282931200)

def momentPanelGrowth2622K05P026 : ℚ := ((51355569539664046294211360605388606443 : ℚ) / 46027886234046918276584694705920409600)

theorem momentPanelPhase_owner2622K05P026 :
    (momentPanelPhase2622K05P026 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-127 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P026, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P026 :
    (momentPanelGrowth2622K05P026 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-127 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P026, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P026Input : RatPair2542 := (momentPanelPhase2622K05P026 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P026Expected : RatState2542 :=
  ((((16042078949649720452202091127429670907427231029825356969644651321059941775 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((165111798334833987169368403 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P026_replay :
    compactExp2620 momentScalarAmp2622K05P026Input 20 = momentScalarAmp2622K05P026Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P026_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-127 / 200) 0) -
      (momentScalarAmp2622K05P026Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P026]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P026 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P026 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P026Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P026_replay] at h
  simpa only [momentPanelPhase_owner2622K05P026] using h

theorem momentScalarAmp2622K05P026_radius_le :
    (momentScalarAmp2622K05P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P026Expected]

def momentScalarGrow2622K05P026Input : RatPair2542 := (momentPanelGrowth2622K05P026 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P026Expected : RatState2542 :=
  ((((101854984389454001730112702583726050400575861327221241866167238073956714109556475831522667518351 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((4131724630710714695348116003247646283612477121835 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P026_replay :
    compactExp2620 momentScalarGrow2622K05P026Input 20 = momentScalarGrow2622K05P026Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P026_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-127 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P026Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P026Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P026 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P026]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P026 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P026 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P026Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P026Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P026_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P026] using h

theorem momentScalarGrow2622K05P026_radius_le :
    (momentScalarGrow2622K05P026Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P026Expected]

end ConnesWeilRH.Dev
