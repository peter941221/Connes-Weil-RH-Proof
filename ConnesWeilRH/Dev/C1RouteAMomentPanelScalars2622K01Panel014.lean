import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P014 : ℚ := ((-28602470901403506481732550459406516759340541744159459 : ℚ) / 409120551114163399905357673142697780844114319769600)

def momentPanelGrowth2622K01P014 : ℚ := ((33126786822225371462239295691287231311764386807099 : ℚ) / 12952272811306585920603945172754168362673425612800)

theorem momentPanelPhase_owner2622K01P014 :
    (momentPanelPhase2622K01P014 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P014 :
    (momentPanelGrowth2622K01P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P014Input : RatPair2542 := (momentPanelPhase2622K01P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P014Expected : RatState2542 :=
  ((((927183538271243244069840144752435591855951621623606980718847658233 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417852814652397144301039 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P014_replay :
    compactExp2620 momentScalarAmp2622K01P014Input 20 = momentScalarAmp2622K01P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K01P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P014_replay] at h
  simpa only [momentPanelPhase_owner2622K01P014] using h

theorem momentScalarAmp2622K01P014_radius_le :
    (momentScalarAmp2622K01P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P014Expected]

def momentScalarGrow2622K01P014Input : RatPair2542 := (momentPanelGrowth2622K01P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P014Expected : RatState2542 :=
  ((((13782309246038394285568820996125836450633509703139190027839501850145617710450005958669909834254555 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((17471109974061477178953565875597855491023414128675 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P014_replay :
    compactExp2620 momentScalarGrow2622K01P014Input 20 = momentScalarGrow2622K01P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P014] using h

theorem momentScalarGrow2622K01P014_radius_le :
    (momentScalarGrow2622K01P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P014Expected]

end ConnesWeilRH.Dev
