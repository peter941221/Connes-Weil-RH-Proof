import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P013 : ℚ := ((-105669006116029924538324193169252219725 : ℚ) / 1346021830936739456014835384345165824)

def momentPanelGrowth2622K07P013 : ℚ := ((642790680060992082413880950502853708025 : ℚ) / 224094137293408589103043451600297263104)

theorem momentPanelPhase_owner2622K07P013 :
    (momentPanelPhase2622K07P013 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P013 :
    (momentPanelGrowth2622K07P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P013Input : RatPair2542 := (momentPanelPhase2622K07P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P013Expected : RatState2542 :=
  ((((5374048275391289337231381380975277389527069432404293300201735 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((302231454930909001389203 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P013_replay :
    compactExp2620 momentScalarAmp2622K07P013Input 20 = momentScalarAmp2622K07P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K07P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P013_replay] at h
  simpa only [momentPanelPhase_owner2622K07P013] using h

theorem momentScalarAmp2622K07P013_radius_le :
    (momentScalarAmp2622K07P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P013Expected]

def momentScalarGrow2622K07P013Input : RatPair2542 := (momentPanelGrowth2622K07P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P013Expected : RatState2542 :=
  ((((37612056181768176704703088401265593556873301342558861559336299660411998627174847559956148108906029 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((23839407584162518401851367217798070231086641365555 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P013_replay :
    compactExp2620 momentScalarGrow2622K07P013Input 20 = momentScalarGrow2622K07P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P013] using h

theorem momentScalarGrow2622K07P013_radius_le :
    (momentScalarGrow2622K07P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P013Expected]

end ConnesWeilRH.Dev
