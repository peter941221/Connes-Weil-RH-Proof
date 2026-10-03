import ConnesWeilRH.Dev.C1RouteACompactExpBatch2542

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem compactNodeError2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 -
      nodeValue2541 i‖ ≤ nodeError2541 i := by
  rw [nodeUnit_eq2541]
  fin_cases i
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0002542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0012542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0022542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0032542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0042542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0052542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0062542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0072542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0082542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0092542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0102542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0112542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0122542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0132542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0142542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0152542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0162542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0172542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0182542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0192542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0202542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0212542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0222542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0232542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0242542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0252542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0262542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0272542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0282542
  · simpa only [nodeZ2541, nodeValue2541, nodeError2541] using
      compactErrorP0292542

theorem signedJet_compact_le2542 :
    signedJetUpper2539 0 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 nodePosition2541 ≤ nodeUpper2541 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * nodeError2541 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (compactNodeError2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeUnit_norm2541 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 nodeUpper2541
  linarith [nodeSum_norm2541, nodeEvaluation_charge2541]

theorem weightedPhysical_compact_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 nodePosition2541‖ ≤
      nodeUpper2541 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i)) nodePosition2541
  simpa only [iteratedDeriv_zero] using h.trans signedJet_compact_le2542

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.compactNodeError2542
#print axioms ConnesWeilRH.Dev.signedJet_compact_le2542
#print axioms ConnesWeilRH.Dev.weightedPhysical_compact_le2542
