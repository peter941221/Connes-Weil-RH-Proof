import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P011 : ℚ := ((-125038124423407267245932498857145873826418871143057463 : ℚ) / 1460645288715279342275049861134613322574102895001600)

def momentPanelGrowth2622K04P011 : ℚ := ((2318711924645519930308733363340660810102421804186990229 : ℚ) / 672237516833277410070131548982829722873141893319884800)

theorem momentPanelPhase_owner2622K04P011 :
    (momentPanelPhase2622K04P011 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P011 :
    (momentPanelGrowth2622K04P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P011Input : RatPair2542 := (momentPanelPhase2622K04P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P011Expected : RatState2542 :=
  ((((141887140093945117366783286944716797530462084990043689925173 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231454903679778582681 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P011_replay :
    compactExp2620 momentScalarAmp2622K04P011Input 20 = momentScalarAmp2622K04P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K04P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P011_replay] at h
  simpa only [momentPanelPhase_owner2622K04P011] using h

theorem momentScalarAmp2622K04P011_radius_le :
    (momentScalarAmp2622K04P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P011Expected]

def momentScalarGrow2622K04P011Input : RatPair2542 := (momentPanelGrowth2622K04P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P011Expected : RatState2542 :=
  ((((8404206514460909068820641653225331323495418099194717736033499424403777410558607356296929149812729 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((42614249552046511909100780400449147917048215650777 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P011_replay :
    compactExp2620 momentScalarGrow2622K04P011Input 20 = momentScalarGrow2622K04P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P011] using h

theorem momentScalarGrow2622K04P011_radius_le :
    (momentScalarGrow2622K04P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P011Expected]

end ConnesWeilRH.Dev
