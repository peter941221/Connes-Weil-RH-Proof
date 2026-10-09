import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P049 : ℚ := ((-2472652066766972953728286480141432880751 : ℚ) / 67822349473650820730637213575308902400)

def momentPanelGrowth2622K05P049 : ℚ := ((8645928673426081045291641678157228871243 : ℚ) / 23394326525573703843507702485116098969600)

theorem momentPanelPhase_owner2622K05P049 :
    (momentPanelPhase2622K05P049 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P049 :
    (momentPanelGrowth2622K05P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P049Input : RatPair2542 := (momentPanelPhase2622K05P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P049Expected : RatState2542 :=
  ((((313463807990903990203910108846156230036411720339423650608724200124223986847643761 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((49672050355713943442275164873589 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P049_replay :
    compactExp2620 momentScalarAmp2622K05P049Input 20 = momentScalarAmp2622K05P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K05P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P049_replay] at h
  simpa only [momentPanelPhase_owner2622K05P049] using h

theorem momentScalarAmp2622K05P049_radius_le :
    (momentScalarAmp2622K05P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P049Expected]

def momentScalarGrow2622K05P049Input : RatPair2542 := (momentPanelGrowth2622K05P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P049Expected : RatState2542 :=
  ((((3091024497448643821314128058857906178451967358660146916593777895272780318209993265517039124371563 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3918337678480896688481179547652768544059672028165 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P049_replay :
    compactExp2620 momentScalarGrow2622K05P049Input 20 = momentScalarGrow2622K05P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P049] using h

theorem momentScalarGrow2622K05P049_radius_le :
    (momentScalarGrow2622K05P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P049Expected]

end ConnesWeilRH.Dev
